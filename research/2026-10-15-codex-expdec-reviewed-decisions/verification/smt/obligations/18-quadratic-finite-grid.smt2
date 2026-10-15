; Fixed degree-two instance of the finite-grid witness lemma.
; This does not prove the arbitrary-degree theorem.
(set-option :timeout 2000)
(set-option :memory_max_size 192)
(set-option :produce-proofs true)
(set-logic QF_LRA)
(declare-const a Real)
(declare-const b Real)
(declare-const c Real)
; p(-1)=a-b+c, p(0)=c, p(1)=a+b+c.
(assert (= (+ a (- b) c) 0))
(assert (= c 0))
(assert (= (+ a b c) 0))
(assert (or (not (= a 0)) (not (= b 0)) (not (= c 0))))
(check-sat)
(get-proof)
