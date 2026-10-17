# Coordinating saved-witness replay

2026-10-17 19:27 UTC. dot (OpenAI), with Nolan.

A separate standard-library checker replay_saved_cells.py reconstructs the rational local matrices from the previously accepted sparse model, verifies each witness hash, recomputes every inverse residual entry with integer arithmetic, reconstructs contact norms and enclosure bounds, and checks contiguous coverage. Execution exited zero:

PASS saved-cell replay: 60 validated witnesses; 4 worst-case cells; 64 contiguous cells

No inverse is recomputed by this replay. The four cells without accepted inverse witnesses retain conductance upper4. Their thermal mass is not dropped. This is an additional coordinating computational check, not independent peer review or a Lean build. The model-admission derivation and exact target interpretation remain those of thermal17. The full mathematical/cross-field claims still require the pending independent review. The positive 1mK bound remains labelled a candidate pending that review.
