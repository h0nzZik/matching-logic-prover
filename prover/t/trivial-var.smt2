(declare-const x Int)
(assert (not ( = x x)))
(check-sat)

(set-info :mlprover-strategy smt-cvc4)
