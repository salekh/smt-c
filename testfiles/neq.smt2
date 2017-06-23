;; activate unsat core computation
 
(set-option :produce-unsat-cores true)

(declare-fun a() Real)
(declare-fun b() Real)

(assert (!= a 1))

(check-sat)
(exit)
