; Fixed degree-(1,1) instance of the finite-grid witness lemma.
; This does not prove the arbitrary-degree or arbitrary-dimensional theorem.
(set-option :timeout 2000)
(set-option :memory_max_size 192)
(set-option :produce-proofs true)
(set-logic QF_LRA)
(declare-const a Real)
(declare-const b Real)
(declare-const c Real)
(declare-const d Real)
; p(x,y)=a+b*x+c*y+d*x*y at (0,0),(1,0),(0,1),(1,1).
(assert (= a 0))
(assert (= (+ a b) 0))
(assert (= (+ a c) 0))
(assert (= (+ a b c d) 0))
(assert (or (not (= a 0)) (not (= b 0)) (not (= c 0)) (not (= d 0))))
(check-sat)
(get-proof)
