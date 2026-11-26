"""Replay a downloaded module set after checking exact Git blob IDs."""
import hashlib, json, os, re, subprocess, sys, time
from pathlib import Path

d = Path(__file__).resolve().parent
source = Path(sys.argv[1]).resolve()
lean = Path(sys.argv[2]).resolve()
lock = json.loads((d / "source-pull.lock.json").read_text())
assert lock["schema"] == "commons.proofbridge.pull.v1"
if list(source.glob("*.olean")):
    sys.exit("refusing to count a stale-olean rebuild as clean")
version = subprocess.check_output([lean, "--version"], text=True)
assert lock["lean_commit"] in version
sources = []
for row in lock["sources"]:
    assert re.fullmatch(r"[A-Za-z][A-Za-z0-9_]*\.lean", row["stage"])
    payload = (source / row["stage"]).read_bytes()
    assert hashlib.sha1(b"blob "+str(len(payload)).encode()+b"\0"+payload).hexdigest() == row["blob"], row
    sources.append({**row, "sha256": hashlib.sha256(payload).hexdigest()})
env = dict(os.environ, LEAN_PATH=str(source))
log = [version.rstrip()]
start = time.monotonic()
for name in ["TwoLiftTriangle","TriangleRun","NanuqOmnibusFixture","ObservationCertificate"]:
    log.append(subprocess.check_output([lean,"-DwarningAsError=true","-o",name+".olean",name+".lean"],cwd=source,env=env,text=True))
consumer = subprocess.check_output([lean,"-DwarningAsError=true","CheckBank.lean"],cwd=source,env=env,text=True)
log.append(consumer)
assert not any("sorryAx" in s for s in log)
checked = {}
for rendered in re.split(r"(?m)^'[^\n]+' (?:depends on axioms:|does not depend on any axioms)", consumer)[:-1]:
    rendered = re.sub(r"^\s*\[[^\]]*\]\s*", "", rendered).strip()
    if rendered:
        declaration = rendered.split()[0].lstrip("@")
        digest = hashlib.sha256(rendered.encode()).hexdigest()
        checked[declaration] = {"printed_type_sha256":digest,"printed_type":rendered}
expected = {"ResearchCommons.TriangleRun.exact_component","ResearchCommons.ObservationCertificate.checked_caterpillar_ambiguity"}
assert set(checked) == expected, consumer
(d/"PULL-REPLAY.log").write_text("\n".join(log))
print(json.dumps({"schema":"commons.proofbridge.source-replay.v1","status":"fresh_kernel_consumer_pass","seconds":round(time.monotonic()-start,3),"sources":sources,"consumer":checked},indent=2,ensure_ascii=False))
