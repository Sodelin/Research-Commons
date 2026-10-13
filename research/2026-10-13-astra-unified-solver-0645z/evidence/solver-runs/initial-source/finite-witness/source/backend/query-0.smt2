; benchmark generated from python API
(set-info :status unknown)
(declare-fun x0 () Real)
(declare-fun x1 () Real)
(declare-fun x2 () Real)
(declare-fun x3 () Real)
(assert
 (and (> x0 0.0) (< x0 1.0)))
(assert
 (and (> x1 0.0) (< x1 1.0)))
(assert
 (and (> x2 0.0) (< x2 1.0)))
(assert
 (and (> x3 0.0) (< x3 1.0)))
(assert
 (let ((?x106 (+ (+ 0.0 (/ 1.0 3.0)) (* (* 1.0 (- (/ 2.0 3.0))) x0))))
 (= ?x106 0.0)))
(assert
 (let ((?x112 (+ (+ 0.0 (- (/ 1.0 6.0))) (* (* 1.0 (/ 1.0 3.0)) x0))))
 (= ?x112 0.0)))
(assert
 (let ((?x112 (+ (+ 0.0 (- (/ 1.0 6.0))) (* (* 1.0 (/ 1.0 3.0)) x0))))
(= ?x112 0.0)))
(check-sat)
