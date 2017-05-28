;; activate unsate core computation

(set-option :produce-unsat-cores true)

(declare-fun a() Int)
(declare-fun b() Int)
(declare-fun c() Int)

(assert (or ( = a 0) (= b 0)(= c 0)))
(assert (>= (+ a  b  c) 100))
(assert (or (>= a 5) (>= b 5)))
(assert (>= c 10))
(assert (<= (+ a (+ b (+ c))) 180))
(assert (<= (+ (* 3 a) (* 2 b) c) 300))




(check-sat)
(exit)
