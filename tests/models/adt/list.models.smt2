(set-option :produce-models true)
(set-logic ALL)
(declare-datatype List (
  (empty)
  (cons (head Int) (tail List))
))
(declare-const a List)
(declare-const b List)
(declare-const c List)
(declare-const d List)
(assert (= (tail a) b))
(assert ((_ is cons) c))
(assert (= (tail c) d))
(check-sat)
(get-model)
