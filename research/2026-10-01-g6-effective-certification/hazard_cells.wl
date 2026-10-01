(* Exact hazard-cell audit. Evaluated through Wolfram Language 15.0.1. *)
Clear[r, r1, r2, a, g];
cases = <|
"shared_equal_epochs_conflict" -> Exists[{r}, r > 0 && 1 <= r <= 11/10 && 2 <= r <= 21/10],
"independent_rate_relaxation_accepts" -> Exists[{r1, r2}, r1 > 0 && r2 > 0 && 1 <= r1 <= 11/10 && 2 <= r2 <= 21/10],
"shared_rate_variable_age_feasible" -> Exists[{r, a}, r > 0 && 29/10 < a < 31/10 && 1 <= r <= 11/10 && 2 <= r (a - 1) <= 21/10],
"unbounded_age_small_rate_feasible" -> Exists[{r, a}, r > 0 && a > 10^6 && 1 <= r a <= 11/10],
"shared_inheritance_rows_conflict" -> Exists[{g}, 0 < g < 1 && 1/10 <= g <= 2/10 && 8/10 <= g <= 9/10],
"positive_edge_tied_endpoints_conflict" -> Exists[{a}, a > 1 && a == 1],
"known_rate_doubling_feasible" -> Exists[{r}, r > 0 && 1 <= r <= 11/10 && 2 <= 2 r <= 21/10],
"known_rate_doubling_conflict" -> Exists[{r}, r > 0 && 1 <= r <= 11/10 && 3 <= 2 r <= 31/10]
|>;
res = Map[Resolve[#, Reals] &, cases];
<|"version" -> $Version, "results" -> res, "witness" -> FindInstance[r > 0 && 29/10 < a < 31/10 && 1 <= r <= 11/10 && 2 <= r (a - 1) <= 21/10, {r,a}, Reals]|> // InputForm
