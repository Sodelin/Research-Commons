"""Produce the curated catalog from the immutable replay outputs for this release."""
import hashlib,json,re,sys
from pathlib import Path
d=Path(__file__).resolve().parent
published=sys.argv[1]
repo="Sodelin/Research-Commons"
comp="Sodelin/Work-on-Samuel-Alexander-Research-"
prefix="research/2026-11-25-proofbridge-linear/capped-host/"
bank="docs/discovery/lean-bank/"
fn=lambda r,c,p:f"https://github.com/{r}/blob/{c}/{p}"
sha=lambda b:hashlib.sha256(b).hexdigest()
digest=lambda p:sha((d/p).read_bytes())
internal=lambda reference:{"kind":"internal","reference":reference}
cat={"schema":"proofbridge.catalog.v1","problems":[],"theorems":[],"artifacts":[]}
def problem(slug,title,statement,closure,ref):
    cat["problems"].append(dict(id="problem."+slug,title=title,statement=statement,closure=closure,provenance=internal(ref)))
def theorem(slug,title,statement,status,links,artifacts,ref,uses=()):
    cat["theorems"].append(dict(id="theorem."+slug,title=title,statement=statement,proof_status=status,
      assumptions=[],problems=[dict(id="problem."+x,relation=y) for x,y in links],
      artifacts=["artifact."+i for i in artifacts],uses=[dict(id="theorem."+x,relation=y) for x,y in uses],
      provenance=internal(ref)))
def artifact(slug,r,c,p,dec,content_sha=None,stmt=None,replay=None):
    kind="kernel_checked" if stmt else ("local_replay" if replay else "source_only")
    cat["artifacts"].append(dict(id="artifact."+slug,repo=r,commit=c,path=p,declaration=dec,sha256=content_sha,
      verification=dict(kind=kind,reference=replay,lean_version="4.33.1" if replay else None,
      statement_sha256=sha(stmt.encode()) if stmt else None),provenance=internal(fn(r,c,p))))

pull=json.loads((d/"source-pull.receipt.json").read_text())
pulllog=fn(repo,published,bank+"PULL-REPLAY.log")
for a in pull["sources"]:
    if a["stage"] in {"TriangleRun.lean","ObservationCertificate.lean"}:
        dec=("ResearchCommons.TriangleRun.exact_component" if a["stage"]=="TriangleRun.lean" else
             "ResearchCommons.ObservationCertificate.checked_caterpillar_ambiguity")
        stmt=pull["consumer"][dec]["printed_type"]
        slug="alexander.zero-run" if a["stage"]=="TriangleRun.lean" else "nanuq.caterpillar"
        title="Alexander isolated zero-run exact component" if slug.startswith("alexander") else "NANUQ caterpillar: same quartet support, different joint split"
        source=fn(repo,a["ref"],a["path"])
        problem(slug,title,stmt,"closed",source)
        artifact(slug,repo,a["ref"],a["path"],dec,a["sha256"],stmt,pulllog)
        dependency="alexander.triangle-source" if slug.startswith("alexander") else "nanuq.caterpillar-source"
        theorem(slug,title,stmt,"kernel_checked",[(slug,"exact")],[slug,dependency],source)
    else:
        slug="alexander.triangle-source" if a["stage"]=="TwoLiftTriangle.lean" else "nanuq.caterpillar-source"
        dec="ResearchCommons.TwoLiftTriangle.triangle_iff" if a["stage"]=="TwoLiftTriangle.lean" else "ResearchCommons.NanuqOmnibusFixture.same_obs_different_joint"
        artifact(slug,repo,a["ref"],a["path"],dec,a["sha256"],None,pulllog)

thuelog=fn(repo,published,bank+"thue/COMBINED-REPLAY.log")
lines=(d/"thue/COMBINED-REPLAY.log").read_text()
for slug,title,dec,module,dep in [
 ("thue.phase-alias","Thue-Morse exact finite phase ambiguity","ResearchCommons.ThueMorsePhaseAliasing.prefix_aliases_with_cofinal_separation","ThueMorsePhaseAliasing.lean","thue.bits"),
 ("thue.first-mismatch","Thue-Morse first mismatch for dyadic triple shift","ResearchCommons.ThueMorsePhaseAliasing.triple_dyadic_first_mismatch","ThueMorsePhaseAliasing.lean","thue.bits"),
 ("thue.zero-height","Thue-Morse exact zero-height prefix count","ThueMorseReuse.zeroCount_exact","PrefixCount.lean","thue.height-provider"),
]:
    match=re.search(r"(?m)^"+re.escape(dec)+r" : (?s:.*?)(?=\n'"+re.escape(dec)+r"' (?:depends|does not depend))",lines)
    if not match: raise ValueError(dec)
    stmt=match[0].strip()
    p=bank+"thue/"+module
    artifact(slug,repo,published,p,dec,digest("thue/"+module),stmt,thuelog)
    problem(slug,title,stmt,"closed",fn(repo,published,p))
    theorem(slug,title,stmt,"kernel_checked",[(slug,"exact")],[slug],fn(repo,published,p),[(dep,"uses")])
manifest=(d/"thue/PROVIDER-MANIFEST.tsv").read_text().splitlines()
provider=manifest[0].split()[2].rstrip(";")
height_art=[]
for row in manifest[1:]:
    p,_,blob_sha=row.split()
    name=Path(p).stem
    slug="thue.provider."+name.lower()
    decls={"ThueMorseBits":"ThueMorseBits.t","FullHeight":"FullHeight.height_from_factorization"}
    artifact(slug,comp,provider,"lean/"+p,decls.get(name),blob_sha,None,thuelog)
    height_art.append(slug)
    if name=="ThueMorseBits":
        theorem("thue.bits","Pinned Thue-Morse digit parity definition","ThueMorseBits.t is the binary digit-parity sequence used by the phase and height results.","checked_component",[],[slug],thuelog)
artifact("thue.reuse",repo,published,bank+"thue/Reuse.lean","ThueMorseReuse.height_zero_iff_descent",digest("thue/Reuse.lean"),None,thuelog)
height_art.append("thue.reuse")
theorem("thue.height-provider","Pinned Thue-Morse genealogical height package","The published FullHeight provider computes phase-zero matching heights from the factorization, with the ladder and the required avoidance proofs pinned in its dependency closure.","checked_component",[],height_art,thuelog)
r3="2b21f9e88ed85df1df1141e71980f9e81a189c09"
prior=fn(repo,r3,prefix+"round3/BALANCED-BINARY-TWO-SHEET.md")
s="For each non-eventually-periodic binary word, there is a continuum antichain of binary edge-labelled avoiders, each with exactly three roots and two children per vertex, precluding every countable portfolio of balanced binary cap-two hosts under weak undirected adjacency embeddings."
problem("alexander.binary-portfolio","Alexander exact binary child-cap-two portfolio (edge-labelled)",s,"closed",prior)
theorem("alexander.binary-portfolio","Binary cap-two portfolio obstruction, complete hand proof",s,"hand_proof",[("alexander.binary-portfolio","exact"),("alexander.formal-assembly","partial")],[],prior,[("alexander.zero-run","uses")])
problem("alexander.formal-assembly","Lean end-to-end assembly of the binary cap-two portfolio result","Construct and verify in one pinned Lean endpoint the full recurrent signature and countable host diagonal in the presented population model.","open",prior)
problem("alexander.fixed-source-portfolio","Fixed-source-color exact cap-two portfolio","Determine the analogous portfolio obstruction for fixed-source-color populations under weak undirected adjacency without assuming the directed line graph preserves triangles.","open",prior)
omni="a38db281d7998a2948cd6496cb3d22ed5cf9c03d"
pair=fn(repo,omni,prefix+"omnibus/fixture/NANUQ-Paired-Fixture.md")
problem("nanuq.network-admission","Lift the paired NANUQ counterexample to one original network class",
        "Determine whether both same-multiplicity plane-tree fixtures arise under one explicit original network admission rule while retaining the same observation and differing joint split occurrence.","open",pair)
theorem("nanuq.paired-observation","Abstract paired plane-tree counterexample","In the specified two plane-tree fixtures, all distinct quartet supports and their raw support-derived distances agree but the joint split pair abc|de and ade|bc occurs in only one.","checked_component",[("nanuq.network-admission","related")],[],pair)
print(json.dumps(cat,indent=2,ensure_ascii=False))
