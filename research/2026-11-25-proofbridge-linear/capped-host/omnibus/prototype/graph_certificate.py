"""Independent bounded exact verifier for observation consistency and identifiability."""
from hashlib import sha256
from itertools import combinations
import json

SCHEMA = "proofbridge.simple-graph-observation.v1"
MAX_EDGES = 15


def _fail(msg):
    raise ValueError(msg)


def _nat(x, cap):
    if type(x) is not int or not 0 <= x <= cap:
        _fail("invalid bounded integer")
    return x


def _obj(x, fields):
    if type(x) is not dict or set(x) != set(fields):
        _fail("unexpected object shape")


def _feature(f, n):
    if type(f) is not dict:
        _fail("invalid feature")
    kind = f.get("kind")
    if kind == "edge":
        _obj(f, ["kind", "uv"])
        e = f["uv"]
        if type(e) is not list or len(e) != 2:
            _fail("invalid edge")
        u, v = (_nat(x, n-1) for x in e)
        if not u < v:
            _fail("edge endpoints must be increasing")
        return kind, (u,v), 1
    if kind == "degree":
        _obj(f, ["kind", "v"])
        return kind, _nat(f["v"], n-1), n-1
    if kind == "edge_count":
        _obj(f, ["kind"])
        return kind, None, n*(n-1)//2
    _fail("unsupported feature")


def validate_request(req):
    _obj(req, ["schema", "domain", "observations", "query"])
    if req["schema"] != SCHEMA:
        _fail("unsupported schema")
    _obj(req["domain"], ["kind", "n"])
    if req["domain"]["kind"] != "all_labeled_simple_undirected":
        _fail("unsupported domain")
    n = _nat(req["domain"]["n"], 6)
    if type(req["observations"]) is not list or len(req["observations"]) > 64:
        _fail("invalid observation list")
    obs = []
    for item in req["observations"]:
        _obj(item, ["feature", "eq"])
        kind, args, cap = _feature(item["feature"], n)
        obs.append(((kind, args), _nat(item["eq"], cap)))
    q = req["query"]
    if type(q) is not dict:
        _fail("invalid query")
    mode = q.get("kind")
    if mode == "feasible":
        _obj(q, ["kind"])
        target = None
    elif mode == "identify":
        _obj(q, ["kind","target"])
        target = _feature(q["target"], n)[:2]
    else:
        _fail("unsupported query")
    return n, obs, mode, target


def request_hash(req):
    validate_request(req)
    return sha256(json.dumps(req, sort_keys=True, separators=(",", ":"), ensure_ascii=True).encode()).hexdigest()


def verify(req, cert):
    """Return machine status; malformed certificates raise ValueError, never NO."""
    n, obs, mode, target = validate_request(req)
    if type(cert) is not dict or cert.get("request_sha256") != request_hash(req):
        _fail("wrong request hash")
    edges = tuple(combinations(range(n), 2))
    if len(edges) > MAX_EDGES:
        _fail("enumeration budget exceeded")
    universe = 1 << len(edges)
    positions = {e: i for i,e in enumerate(edges)}
    inc = tuple(sum(1 << i for i,e in enumerate(edges) if v in e) for v in range(n))

    def calc(mask, f):
        kind, a = f
        if kind == "edge":
            return (mask >> positions[a]) & 1
        if kind == "degree":
            return (mask & inc[a]).bit_count()
        return mask.bit_count()

    def valid(m):
        return all(calc(m,f) == v for f,v in obs)

    def witness(k):
        m = _nat(cert[k], universe-1)
        if not valid(m):
            _fail("witness violates observations")
        return m

    kind = cert.get("kind")
    top = ["request_sha256", "kind"]
    result = {"request_sha256": cert["request_sha256"], "domain": req["domain"].copy()}
    if kind == "unknown":
        _obj(cert, top)
        return {**result, "status": "unknown", "verified": False}
    if kind == "feasible_witness" and mode == "feasible":
        _obj(cert, top+["witness"])
        witness("witness")
        return {**result, "status": "feasible", "verified": True}
    if kind == "empty_replay":
        _obj(cert, top)
        if any(valid(m) for m in range(universe)):
            _fail("claimed empty but checker found a model")
        return {**result, "status": "empty", "verified": True, "states_replayed": universe}
    if kind == "identified_replay" and mode == "identify":
        _obj(cert, top+["witness"])
        v = calc(witness("witness"), target)
        if any(valid(m) and calc(m,target) != v for m in range(universe)):
            _fail("claimed identified but checker found a second target value")
        return {**result, "status": "identified", "value": v,
                "verified": True, "states_replayed": universe}
    if kind == "ambiguity_pair" and mode == "identify":
        _obj(cert, top+["left", "right"])
        a,b = (calc(witness(k), target) for k in ("left","right"))
        if a == b:
            _fail("witnesses agree on target")
        return {**result, "status": "ambiguous", "values": [a,b], "verified": True}
    _fail("unsupported certificate or mismatched query")


def read_strict(text):
    def pairs(pairs_):
        result = dict(pairs_)
        if len(result) != len(pairs_):
            _fail("duplicate JSON key")
        return result
    def const(_):
        _fail("non-JSON constant")
    return json.loads(text, object_pairs_hook=pairs, parse_constant=const)


if __name__ == "__main__":
    import sys
    try:
        if len(sys.argv) != 3: _fail("usage: graph_certificate.py REQUEST CERT")
        def read_file(path):
            with open(path, encoding="utf-8") as stream:
                record = stream.read(65537)
            if len(record) > 65536: _fail("input too large")
            return read_strict(record)
        result = verify(read_file(sys.argv[1]),read_file(sys.argv[2]))
    except (OSError, ValueError, RecursionError) as e:
        print(json.dumps({"status":"rejected","reason":str(e),"verified":False},sort_keys=True))
        raise SystemExit(2)
    print(json.dumps(result,sort_keys=True))
