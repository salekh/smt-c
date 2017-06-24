;; activate unsat core computation
 
(set-option :produce-unsat-cores true)

(declare-fun a() Real)
(declare-fun b() Real)


(assert (= a 1))
(assert (or (!= a 1) (!= b 1)))
(assert (>= (+ a b) 2))

(check-sat)
(exit)
