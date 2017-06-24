;; activate unsat core computation
 
(set-option :produce-unsat-cores true)

(declare-fun a() Real)
(declare-fun b() Real)


(assert (= b 1))
(assert (!= a 1))
(assert (>= (+ a b) 2))

(check-sat)
(exit)
