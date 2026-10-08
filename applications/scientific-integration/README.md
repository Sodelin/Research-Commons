# Common scientific entry point

From the Research Commons root:

```sh
python3 applications/scientific-integration/run.py cwu
```

The command creates a fresh readable report and JSON evidence. It displays saved public-hemlock marker results and separate synthetic solver/checker controls. Capture remains UNKNOWN. To recompute the real marker comparison, run the same script with a Python environment containing Biopython 1.88 and add `--replay-sequences`. This uses included public GenBank records without network requests. `--replay` independently requests the synthetic source-control replay and requires that solver's pinned dependencies.

Other modes are `workbench`, `molecular` and explicitly manifested `sequence-pair`. Molecular mode always uses mocks. Optional `--python` and `--solver-python` select an executable on PATH or an absolute executable path; running the entry point with the desired environment's Python supplies its absolute interpreter automatically. Existing output directories refuse overwrite. Failed requested computation is visible above any separately labeled saved evidence.

[Full installation, scope and license notes](../README.md). No professor contact or endorsement, live API use or whole-application Lean verification is implied.
