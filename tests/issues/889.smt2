(set-logic ALL)
(declare-const a Int)
(declare-const b Int)
(declare-const c Int)
(assert (not (distinct a b c)))
(assert (distinct a b))
(check-sat)
