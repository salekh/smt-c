;; activate unsat core computation
 
(set-option :produce-unsat-cores true)

(declare-fun a() Real)
(declare-fun b() Real)

(assert (> a 0.5))
(assert (< a 0.8))

(assert (> b 1))
(assert (< b 1.2))

(assert (> (+ a b) 1.8))

(check-sat)
(exit)
