;; activate unsat core computation
 
(set-option :produce-unsat-cores true)
 
(declare-fun a() Int)
(declare-fun b() Int)
(declare-fun c() Int)
(declare-fun d() Int)
 
(assert (and (>= b a) (>= a 5)))
(assert (>= c b))
(assert (>= d c))
 
;;(assert (and (> y2 0)(< y2 5)))
 
(check-sat)
(exit)