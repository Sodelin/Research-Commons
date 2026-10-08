; benchmark generated from python API
(set-info :status unknown)
(declare-fun x0 () Real)
(declare-fun x1 () Real)
(declare-fun x2 () Real)
(declare-fun x3 () Real)
(declare-fun x4 () Real)
(declare-fun x5 () Real)
(assert
 (and (> x0 0.0) (< x0 1.0)))
(assert
 (and (> x1 0.0) (< x1 1.0)))
(assert
 (and (> x2 0.0) (< x2 1.0)))
(assert
 (and (> x3 0.0) (< x3 1.0)))
(assert
 (and (> x4 0.0) (< x4 1.0)))
(assert
 (and (> x5 0.0) (< x5 1.0)))
(assert
 (let ((?x151 (* (* 1.0 (/ 1.0 3.0)) x0)))
 (let ((?x152 (* ?x151 x1)))
 (let ((?x226 (+ (+ 0.0 (- (/ 4.0 5.0))) ?x152)))
 (= ?x226 0.0)))))
(assert
 (let ((?x143 (* (* 1.0 (- (/ 2.0 3.0))) x0)))
 (let ((?x144 (* ?x143 x1)))
 (let ((?x223 (+ (+ 0.0 (/ 9.0 10.0)) ?x144)))
 (= ?x223 0.0)))))
(assert
 (let ((?x151 (* (* 1.0 (/ 1.0 3.0)) x0)))
(let ((?x152 (* ?x151 x1)))
(let ((?x153 (+ (+ 0.0 (- (/ 1.0 10.0))) ?x152)))
(= ?x153 0.0)))))
(check-sat)
