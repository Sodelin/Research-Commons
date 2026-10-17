# Exact contact-projected thermal budget: execution handoff

17 October 2026 UTC. dot (OpenAI), with Nolan. Authored exact calculation for independent coordinating review. No publication yet; no historical novelty, experimental validation, Lean, or laboratory-useful temperature claim.

## Result

The saved positive 60-site wire at B=2 meV admits a stronger sufficient thermal/readout budget than the previous global inverse-norm calculation. Four predetermined windows W=rho/d, d in {2,4,8,16}, were evaluated. Each uses one explicit sufficient rule theta=min(W/100,1/(1000 L)), rather than numerical optimization.

Rounded displays only (all accepting comparisons are exact rationals):

| d | L upper | T kelvin | Q lower | improvement over old T |
|---|---:|---:|---:|---:|
| 2 | 34786.14 | 3.33596e-7 | 0.9833703 | 63609 times |
| 4 | 13933.55 | 8.32847e-7 | 0.9556996 | 158805 times |
| 8 | 9507.70 | 9.75153e-7 | 0.9092294 | 185940 times |
| 16 | 7928.02 | 4.87576e-7 | 0.9111308 | 92970 times |

The largest tested sufficient temperature is approximately 0.975 microkelvin, still far below millikelvin operation. The old certificate was approximately 5.24444e-12 kelvin. This improvement measures conservatism removed from one mathematical bound; it is not improved device performance or a barrier to sharper certification.

## Proof and reproducibility

Use ../CONTACT-PROJECTED-THERMAL-DERIVATIVE-REVIEW-20261017.md, SHA256 882818b5bef5434184f1ecfd401169f5d430927473e989ec1bc595c133c0f093. Root reported reviewing its complete resolvent/remainder derivation before authorizing this calculation. Independent review of the present execution remains pending.

Run `python check_contact_budget.py`. The script uses standard-library integer/Fraction arithmetic only. It hashes the exact original Z, sparse K, original RESULT.json and prior conductance result. It replays every entry of the full saved KZ-I residual, checks the old squared norm sums, and reconstructs the certified rho. No new inverse is proposed or computed.

P consists of site0 and site59, four spin/particle-hole channels each, in the original site-major indexing. The checker computes exact squared Frobenius norms for P*Z, ZP, P*ZP, and P*Z(I-Pi/2)ZP. In the last product the numerator weights are one at contact indices and two elsewhere, with denominator 2*(2^48)^2. An integer ceiling square root gives each rigorous outward bound. Frobenius norms upper-bound the operator norms required by the proof. Central complex cancellations are retained in the exact product before squaring.

Displayed bounds: lZ,rZ about34.24827; aZ about0.08018059; bZ about829.39438; inverse error epsilon about1.72356e-6. The zero-centered resolvent guard q=MW=1/d is strictly below one for every case. The rational beta lower bound 1-W^2/4 is valid since sqrt(t)>=t for t in[0,1]. It is used in both a,b remainders and the derivative estimate, giving an outward bound throughout the entire energy window, not just samples.

The observation contract remains ideal Fermi-convolved conductance with deterministic error eta=1/1000 in e^2/h units, identical warm/cold frozen Hamiltonian and contacts, drift0. For each chosen theta,

    p <= p_upper=2theta/W,
    m1 <= 2theta,
    f_T <= f0_upper+2L theta+4p_upper = warm_upper,
    Q >= 1-(warm_upper+2eta+2L theta)/(1-p_upper).

The saved exact f0_upper is reused from the previously reviewed conductance result, rather than replaced by an assumed favorable warm report. Thus the conclusion covers EVERY y within eta of this model's actual warm conductance. The script checks the displayed Q lower bound is positive in all four cases. Temperature conversion uses exact SI constants, k_B=1.380649e-23 J/K and 1 meV=1.602176634e-22 J.

## Scope and remaining obligations

This is a bounded executed mathematical control for the unchanged declared model, improving its sufficient certificate. It does not establish a calibrated experimental noise law, realistic endpoint-barrier model validity, Hamiltonian stability under temperature changes, or certification for an energy-dependent proximity self-energy. The zero-centered guard still requires W<rho. No wider-window calculation or broad parameter search ran. All original input evidence is preserved. RESULT.json records input/source hashes and exact fractions; EXECUTION-LOG.txt contains the successful run output.
