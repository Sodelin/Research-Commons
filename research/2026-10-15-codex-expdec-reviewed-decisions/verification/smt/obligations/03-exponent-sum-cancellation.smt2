; This verifies polynomial exponent arithmetic, not exp(Q1)*exp(Q2)=exp(Q1+Q2).
(set-option :timeout 2000)
(set-option :memory_max_size 192)
(set-option :produce-proofs true)
(set-logic QF_NRA)
(declare-const x Real)
(assert (not (= (+ (+ (* x x) (* 2 x)) (* (- 2) x)) (* x x))))
(check-sat)
(get-proof)
