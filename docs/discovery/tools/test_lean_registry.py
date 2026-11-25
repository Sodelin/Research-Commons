"""Run the documented parent-revision command in a clean two-commit repo."""
import json, subprocess, sys, tempfile
from pathlib import Path

def main():
    tool=Path(__file__).with_name("lean-registry.py").resolve()
    with tempfile.TemporaryDirectory(prefix="lean_registry_regression_") as tmp:
        root=Path(tmp)
        def git(*argv):
            subprocess.run(["git","-C",tmp,"-c","user.name=ProofBridge","-c",
                            "user.email=proofbridge@example.invalid",*argv],
                            check=True,capture_output=True)
        git("init","-q")
        for n,text in [
            ("packages/research/integration/lean-modules.json",'{"modules": []}\n'),
            ("packages/research/vendor/accepted/MANIFEST.json",'{"files": []}\n'),
        ]:
            file=root/n
            file.parent.mkdir(parents=True,exist_ok=True)
            file.write_text(text,encoding="utf-8")
        git("add","."); git("commit","-qm","baseline")
        mod=root/"research/proofbridge-lean/Intake.lean"
        mod.parent.mkdir(parents=True)
        mod.write_text("def entry := 1\n",encoding="utf-8")
        git("add","."); git("commit","-qm","addition")
        argv=[sys.executable,str(tool),"--repo",tmp,"--at","HEAD","--since"]
        p=subprocess.run(argv+["HEAD~1","--delta-only"],check=True,
                         capture_output=True,text=True)
        row=json.loads(p.stdout)
        assert row["id"]=="standalone:Intake" and row["delta"]=="new"
        bad=subprocess.run(argv+["HEAD:README.md","--delta-only"],
                           capture_output=True,text=True)
        assert bad.returncode==2 and "invalid revision" in bad.stderr
    print("documented parent range accepted; path-expression rejected")

if __name__=="__main__":
    main()
