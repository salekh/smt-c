;; activate unsat core computation
 
(set-option :produce-unsat-cores true)

(declare-fun a() Int)
(declare-fun b() Int)

(assert (>= (+ a (* 2 b)) 0))
(assert (<= a -2))

(check-sat)
(exit)