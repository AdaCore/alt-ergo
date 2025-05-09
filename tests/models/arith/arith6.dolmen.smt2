(set-option :produce-models true)
(set-logic ALL)
(declare-const x Int)
(declare-const y Int)
(declare-const z Int)
; This linear program is bounded.
(assert (= (+ (* 5 x) (* 2 y) (* (- 0 3) z)) 25))
(assert (= (+ (* (- 0 2) x) (* 4 y)) 8))
(assert (<= x y))
(maximize x)
(check-sat)
(get-model)
(get-objectives)
