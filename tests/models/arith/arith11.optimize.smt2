(set-logic ALL)
(declare-const p1 Bool)
(declare-const p2 Bool)

(declare-const x Real)
(declare-const y Real)
(assert (or p1 p2))
(assert (=> p1 (< x 2.0)))
(assert (=> p2 (<= x 2.0)))
(maximize x)
(check-sat)
