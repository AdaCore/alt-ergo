(set-logic ALL)
(declare-const x (_ BitVec 1024))
(assert (bvult x (_ bv3 1024)))
(assert (= (bvand x (_ bv3 1024)) (_ bv3 1024)))
(check-sat)
