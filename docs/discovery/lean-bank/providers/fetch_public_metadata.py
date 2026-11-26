"""Read public GitHub metadata for exact approved pins; never download source bodies."""
import argparse
from hashlib import sha256
import http.client
import json
from pathlib import Path
import re
from urllib.parse import quote, urlencode
from project_intake import load_json, products, path_parts, REPO, sha

def api_get(path):
    if not path.startswith("/repos/") or "\r" in path or "\n" in path:
        raise ValueError("noncanonical API endpoint")
    connection=http.client.HTTPSConnection("api.github.com",timeout=7)
    try:
        connection.request("GET", path, headers={"Accept":"application/vnd.github+json","User-Agent":"Research-Commons-metadata-index"})
        response=connection.getresponse()
        if response.status != 200:
            raise ValueError(f"GitHub public metadata HTTP {response.status}")
        body=response.read(2_000_001)
        if len(body)>2_000_000: raise ValueError("GitHub metadata response exceeds cap")
        return json.loads(body)
    finally:
        connection.close()

def capture(policy, get=api_get):
    repo,commit=policy["repo"],sha(policy["commit"])
    if not REPO.fullmatch(repo) or any(x in (".","..") for x in repo.split("/")):
        raise ValueError("invalid approved repository")
    root=sha(policy["tree"])
    selected=policy["paths"]
    if not 1<=len(selected)<=min(policy["max_files"],16):
        raise ValueError("online approved path cap exceeded")
    request=f"/repos/{repo}"
    c=get(f"{request}/git/commits/{commit}")
    pin={k:c[k] for k in ("sha","url","tree")}
    if c["sha"]!=commit or c["tree"]["sha"]!=root:
        raise ValueError("resolved commit does not match registered tree")
    trees={}; folders={}; corroboration=[]
    for path in sorted(selected):
        parts=path_parts(path)
        if not path.endswith(".lean"):
            raise ValueError("only registered Lean file metadata is supported")
        cur=root
        for i,n in enumerate(parts):
            if cur not in trees:
                if len(trees)>=24:
                    raise ValueError("online Git subtree cap exceeded")
                t=get(f"{request}/git/trees/{sha(cur)}")
                trees[cur]={"sha":t["sha"],"url":t["url"],"truncated":t["truncated"],
                            "tree":[{k:e[k] for k in ("path","mode","type","sha")} for e in t["tree"]]}
            row=next((e for e in trees[cur]["tree"] if e["path"]==n),None)
            if row is None: raise ValueError("registered path absent from Git tree")
            if i+1<len(parts):
                if row["type"]!="tree": raise ValueError("intermediate path is not directory")
                cur=sha(row["sha"])
        # Contents of the parent directory are a distinct metadata view and
        # contain no source-byte content fields for the child files.
        parent="/".join(parts[:-1])
        if parent not in folders:
            if len(folders)>=16:
                raise ValueError("online Contents directory cap exceeded")
            endpoint=f"{request}/contents"+("/"+quote(parent) if parent else "")
            folders[parent]=get(endpoint+"?"+urlencode({"ref":commit}))
        file=next((e for e in folders[parent] if e["path"]==path and e["type"]=="file"),None)
        if file is None: raise ValueError("GitHub directory metadata lacks admitted file")
        corroboration.append({"path":path,"sha":file["sha"],"url":file["html_url"]})
    return {"schema":"proofbridge.github-metadata.v1","commit":pin,"trees":list(trees.values()),"corroboration":corroboration}

def observe(provider, allowlist, get=api_get):
    policy=allowlist["providers"][provider]
    index,_,receipt=products(provider,allowlist,capture(policy,get))
    return {"status":"passed","receipt":receipt,"rows":[json.loads(line) for line in index.splitlines()]}

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("--allowlist",type=Path,required=True)
    p.add_argument("--out",type=Path,required=True)
    p.add_argument("--prior",type=Path)
    p.add_argument("--refresh",action="store_true")
    a=p.parse_args()
    registry=load_json(a.allowlist)
    pinned=sha256(a.allowlist.read_bytes()).hexdigest()
    result={"schema":"commons.discovery.provider-observation.v1","registry_sha256":pinned,"providers":{}}
    keys=sorted(registry["providers"])
    if not 1<=len(keys)<=2: raise ValueError("workflow provider count outside bounded allowance")
    if a.prior and a.prior.is_file() and not a.refresh:
        old=load_json(a.prior)
        if old.get("schema")==result["schema"] and old.get("registry_sha256")==pinned and sorted(old["providers"])==keys and all(x["status"]=="passed" for x in old["providers"].values()):
            a.out.write_bytes(a.prior.read_bytes());print("Reused existing approved public metadata receipt.");return
    for id in keys:
        try: result["providers"][id]=observe(id,registry)
        except (OSError,ValueError,TypeError,KeyError,http.client.HTTPException) as e:
            result["providers"][id]={"status":"unavailable","reason":str(e)[:240]}
    a.out.write_text(json.dumps(result,sort_keys=True,indent=2)+"\n")
    print(json.dumps({k:v["status"] for k,v in result["providers"].items()}))

if __name__=="__main__": main()
