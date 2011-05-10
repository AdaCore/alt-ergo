;;; this is a prelude for Z3
(set-logic AUFNIRA)
;;; this is a prelude for Z3 integer arithmetic
(declare-sort uni 0)

(declare-sort deco 0)

(declare-sort ty 0)

(declare-fun sort (ty uni) deco)


(declare-fun int () ty)


(declare-fun int1 () ty)


(declare-fun tb2t (deco) Int)


(declare-fun t2tb (Int) uni)


(declare-fun real () ty)


;; Conv1
  (assert
  (forall ((x Int))
  (! (= (tb2t (sort int1 (t2tb x))) x) :pattern (((sort int1 (t2tb x)))) )))


;; Conv2
  (assert
  (forall ((x uni))
  (! (= (sort int1 (t2tb (tb2t (sort int1 x)))) (sort int1 x)) :pattern ((
  (sort int1 (t2tb (tb2t (sort int1 x)))))) )))


(declare-sort pointer 0)

(declare-fun pointer1 () ty)


(declare-fun pointer2 () ty)


(declare-fun tb2t1 (deco) pointer)


(declare-fun t2tb1 (pointer) uni)


;; Conv1
  (assert
  (forall ((x pointer))
  (! (= (tb2t1 (sort pointer2 (t2tb1 x))) x) :pattern (((sort pointer2
                                                        (t2tb1 x)))) )))


;; Conv2
  (assert
  (forall ((x uni))
  (! (= (sort pointer2 (t2tb1 (tb2t1 (sort pointer2 x)))) (sort pointer2 x)) :pattern ((
  (sort pointer2 (t2tb1 (tb2t1 (sort pointer2 x)))))) )))


(declare-fun t (ty ty) ty)


(declare-fun tb2t2 (deco) (Array pointer pointer))


(declare-fun t2tb2 ((Array pointer pointer)) uni)


(define-sorts ((t_pointer_pointer (Array pointer pointer))))
;; Conv1
  (assert
  (forall ((x t_pointer_pointer))
  (! (= (tb2t2 (sort (t pointer2 pointer2) (t2tb2 x))) x) :pattern ((
  (sort (t pointer2 pointer2) (t2tb2 x)))) )))


;; Conv2
  (assert
  (forall ((x uni))
  (! (= (sort (t pointer2 pointer2)
        (t2tb2 (tb2t2 (sort (t pointer2 pointer2) x)))) (sort
                                                        (t pointer2 pointer2)
                                                        x)) :pattern ((
  (sort (t pointer2 pointer2) (t2tb2 (tb2t2 (sort (t pointer2 pointer2) x)))))) )))








(declare-fun bool () ty)


(declare-fun True () uni)


(declare-fun False () uni)


(declare-fun match_bool (deco deco deco) uni)


;; match_bool_True
  (assert
  (forall ((a ty))
  (forall ((z uni) (z1 uni))
  (= (sort a (match_bool (sort bool True) (sort a z) (sort a z1))) (sort a z)))))


;; match_bool_False
  (assert
  (forall ((a ty))
  (forall ((z uni) (z1 uni))
  (= (sort a (match_bool (sort bool False) (sort a z) (sort a z1))) (sort a
                                                                    z1)))))


(declare-fun index_bool (deco) Int)


;; index_bool_True
  (assert (= (index_bool (sort bool True)) 0))


;; index_bool_False
  (assert (= (index_bool (sort bool False)) 1))


;; bool_inversion
  (assert
  (forall ((u uni))
  (or (= (sort bool u) (sort bool True)) (= (sort bool u) (sort bool False)))))


(declare-fun andb (deco deco) uni)


;; andb_def
  (assert
  (forall ((x uni))
  (and
  (let ((y True))
  (and
  (let ((x1 True))
  (= (sort bool (andb (sort bool x1) (sort bool y))) (sort bool True)))
  (let ((x2 False))
  (= (sort bool (andb (sort bool x2) (sort bool y))) (sort bool False)))))
  (let ((y False))
  (= (sort bool (andb (sort bool x) (sort bool y))) (sort bool False))))))


(declare-fun orb (deco deco) uni)


;; orb_def
  (assert
  (forall ((x uni))
  (and
  (let ((y True))
  (= (sort bool (orb (sort bool x) (sort bool y))) (sort bool True)))
  (let ((y False))
  (and
  (let ((x1 True))
  (= (sort bool (orb (sort bool x1) (sort bool y))) (sort bool True)))
  (let ((x2 False))
  (= (sort bool (orb (sort bool x2) (sort bool y))) (sort bool False))))))))


(declare-fun xorb (deco deco) uni)


;; xorb_def
  (assert
  (and
  (let ((y True))
  (and
  (let ((x True))
  (= (sort bool (xorb (sort bool x) (sort bool y))) (sort bool False)))
  (let ((x False))
  (= (sort bool (xorb (sort bool x) (sort bool y))) (sort bool True)))))
  (let ((y False))
  (and
  (let ((x True))
  (= (sort bool (xorb (sort bool x) (sort bool y))) (sort bool True)))
  (let ((x False))
  (= (sort bool (xorb (sort bool x) (sort bool y))) (sort bool False)))))))


(declare-fun notb (deco) uni)


;; notb_def
  (assert
  (and
  (let ((x True)) (= (sort bool (notb (sort bool x))) (sort bool False)))
  (let ((x False)) (= (sort bool (notb (sort bool x))) (sort bool True)))))


(declare-fun tuple0 () ty)


(declare-fun Tuple0 () uni)


;; tuple0_inversion
  (assert (forall ((u uni)) (= (sort tuple0 u) (sort tuple0 Tuple0))))


(declare-fun ignore (deco) uni)


(declare-fun label_ () ty)


(declare-fun at (deco deco) uni)


(declare-fun old (deco) uni)


;; CompatOrderMult
  (assert
  (forall ((x Int) (y Int) (z Int))
  (implies (<= x y) (implies (<= 0 z) (<= (* x z) (* y z))))))


(declare-fun ref (ty) ty)


(declare-fun get (deco deco) uni)


(declare-fun set (deco deco deco) uni)


;; Select_eq
  (assert
  (forall ((m t_pointer_pointer))
  (forall ((a1 pointer) (a2 pointer))
  (forall ((b pointer))
  (! (implies (= a1 a2) (= (select (store m a1 b) a2) b)) :pattern (((select (store m a1 b) a2))) )))))


;; Select_eq
  (assert
  (forall ((a ty) (b ty))
  (forall ((m uni))
  (forall ((a1 uni) (a2 uni))
  (forall ((b1 uni))
  (! (implies (= (sort a a1) (sort a a2))
     (= (sort b
        (get (sort (t a b) (set (sort (t a b) m) (sort a a1) (sort b b1)))
        (sort a a2))) (sort b b1))) :pattern (((sort b
                                               (get
                                               (sort (t a b)
                                               (set (sort (t a b) m)
                                               (sort a a1) (sort b b1)))
                                               (sort a a2))))) ))))))


;; Select_neq
  (assert
  (forall ((m t_pointer_pointer))
  (forall ((a1 pointer) (a2 pointer))
  (forall ((b pointer))
  (! (implies (not (= a1 a2)) (= (select (store m a1 b) a2) (select m a2))) :pattern (((select (store m a1 b) a2))) )))))


;; Select_neq
  (assert
  (forall ((a ty) (b ty))
  (forall ((m uni))
  (forall ((a1 uni) (a2 uni))
  (forall ((b1 uni))
  (! (implies (not (= (sort a a1) (sort a a2)))
     (= (sort b
        (get (sort (t a b) (set (sort (t a b) m) (sort a a1) (sort b b1)))
        (sort a a2))) (sort b (get (sort (t a b) m) (sort a a2))))) :pattern ((
  (sort b
  (get (sort (t a b) (set (sort (t a b) m) (sort a a1) (sort b b1)))
  (sort a a2))))) ))))))


(declare-fun create_const (deco) uni)


;; Const
  (assert
  (forall ((b pointer) (a pointer))
  (= (select (const[t_pointer_pointer] b) a) b)))


;; Const
  (assert
  (forall ((b ty) (a ty))
  (forall ((b1 uni) (a1 uni))
  (= (sort b (get (sort (t a b) (create_const (sort b b1))) (sort a a1))) 
  (sort b b1)))))


(declare-fun null () pointer)


(declare-fun value () uni)


(declare-fun next () t_pointer_pointer)


(declare-fun is_list (t_pointer_pointer pointer) Bool)


;; is_list_null
  (assert
  (forall ((next1 t_pointer_pointer) (p pointer))
  (implies (= p null) (is_list next1 p))))


;; is_list_next
  (assert
  (forall ((next2 t_pointer_pointer) (p pointer))
  (implies (not (= p null))
  (implies (is_list next2 (select next2 p)) (is_list next2 p)))))


;; is_list_inversion
  (assert
  (forall ((z t_pointer_pointer) (z1 pointer))
  (implies (is_list z z1)
  (or (exists ((next3 t_pointer_pointer)) (and (= z next3) (= z1 null)))
  (exists ((next4 t_pointer_pointer) (p pointer))
  (and (not (= p null))
  (and (is_list next4 (select next4 p)) (and (= z next4) (= z1 p)))))))))


(declare-fun ft (ty) ty)


(declare-fun in_ft (pointer deco) Bool)


(declare-fun list_ft (t_pointer_pointer pointer) uni)


;; frame_list
  (assert
  (forall ((next5 t_pointer_pointer) (p pointer) (q pointer) (v pointer))
  (implies (not (in_ft q (sort (ft pointer2) (list_ft next5 p))))
  (implies (is_list next5 p) (is_list (store next5 q v) p)))))


(declare-fun sep_node_list (t_pointer_pointer pointer pointer) Bool)


;; sep_node_list_def
  (assert
  (forall ((next6 t_pointer_pointer) (p1 pointer) (p2 pointer))
  (iff (sep_node_list next6 p1 p2)
  (not (in_ft p1 (sort (ft pointer2) (list_ft next6 p2)))))))


;; list_ft_node_null
  (assert
  (forall ((next7 t_pointer_pointer) (q pointer) (p pointer))
  (implies (= q null) (not (in_ft p (sort (ft pointer2) (list_ft next7 q)))))))


;; list_ft_node_next
  (assert
  (forall ((next8 t_pointer_pointer) (q pointer) (p pointer))
  (implies (not (= q null))
  (implies (is_list next8 (select next8 q))
  (implies (in_ft p (sort (ft pointer2) (list_ft next8 (select next8 q))))
  (in_ft p (sort (ft pointer2) (list_ft next8 q))))))))


;; list_ft_node_next_inv
  (assert
  (forall ((next9 t_pointer_pointer) (q pointer) (p pointer))
  (implies (not (= q null))
  (implies (is_list next9 (select next9 q))
  (implies (not (= q p))
  (implies (in_ft p (sort (ft pointer2) (list_ft next9 q))) (in_ft p
  (sort (ft pointer2) (list_ft next9 (select next9 q))))))))))


;; frame_list_ft
  (assert
  (forall ((next10 t_pointer_pointer) (p pointer) (q pointer) (v pointer))
  (implies (not (in_ft q (sort (ft pointer2) (list_ft next10 p))))
  (= (sort (ft pointer2) (list_ft next10 p)) (sort (ft pointer2)
                                             (list_ft (store next10 q v) p))))))


(declare-fun list_disj (deco t_pointer_pointer pointer) Bool)


;; list_disj_null
  (assert
  (forall ((ft1 uni) (next11 t_pointer_pointer) (p pointer))
  (implies (= p null) (list_disj (sort (ft pointer2) ft1) next11 p))))


;; list_disj_next
  (assert
  (forall ((ft2 uni) (next12 t_pointer_pointer) (p pointer))
  (implies (not (= p null))
  (implies (is_list next12 (select next12 p))
  (implies (not (in_ft p (sort (ft pointer2) ft2)))
  (implies (list_disj (sort (ft pointer2) ft2) next12 (select next12 p))
  (list_disj (sort (ft pointer2) ft2) next12 p)))))))


;; list_disj_inversion
  (assert
  (forall ((z uni) (z1 t_pointer_pointer) (z2 pointer))
  (implies (list_disj (sort (ft pointer2) z) z1 z2)
  (or
  (exists ((ft3 uni) (next13 t_pointer_pointer))
  (and
  (and (= (sort (ft pointer2) z) (sort (ft pointer2) ft3)) (= z1 next13))
  (= z2 null)))
  (exists ((ft4 uni) (next14 t_pointer_pointer) (p pointer))
  (and (not (= p null))
  (and (is_list next14 (select next14 p))
  (and (not (in_ft p (sort (ft pointer2) ft4)))
  (and (list_disj (sort (ft pointer2) ft4) next14 (select next14 p))
  (and
  (and (= (sort (ft pointer2) z) (sort (ft pointer2) ft4)) (= z1 next14))
  (= z2 p)))))))))))


(declare-fun sep_list_list (t_pointer_pointer pointer pointer) Bool)


;; sep_list_list_def
  (assert
  (forall ((next15 t_pointer_pointer) (p1 pointer) (p2 pointer))
  (iff (sep_list_list next15 p1 p2)
  (and (list_disj (sort (ft pointer2) (list_ft next15 p1)) next15 p2)
  (list_disj (sort (ft pointer2) (list_ft next15 p2)) next15 p1)))))


;; list_ft_disj_null
  (assert
  (forall ((next16 t_pointer_pointer) (q pointer) (p pointer))
  (implies (= q null) (list_disj (sort (ft pointer2) (list_ft next16 q))
  next16 p))))


;; list_ft_disj_next
  (assert
  (forall ((next17 t_pointer_pointer) (p pointer) (q pointer))
  (implies (not (= q null))
  (implies (is_list next17 (select next17 q))
  (implies (not (in_ft q (sort (ft pointer2) (list_ft next17 p))))
  (implies (not (= q p))
  (implies (list_disj (sort (ft pointer2) (list_ft next17 (select next17 q)))
  next17 p) (list_disj (sort (ft pointer2) (list_ft next17 q)) next17 p))))))))


;; list_ft_disj_next_inv
  (assert
  (forall ((next18 t_pointer_pointer) (p pointer) (q pointer))
  (implies (not (= q null))
  (implies (is_list next18 (select next18 q))
  (implies (list_disj (sort (ft pointer2) (list_ft next18 q)) next18 p)
  (list_disj (sort (ft pointer2) (list_ft next18 (select next18 q))) next18
  p))))))


;; frame_list_disj
  (assert
  (forall ((next19 t_pointer_pointer) (p1 pointer) (p2 pointer) (q pointer)
  (v pointer))
  (implies (not (in_ft q (sort (ft pointer2) (list_ft next19 p1))))
  (implies (not (in_ft q (sort (ft pointer2) (list_ft next19 p2))))
  (implies (list_disj (sort (ft pointer2) (list_ft next19 p1)) next19 p2)
  (list_disj (sort (ft pointer2) (list_ft (store next19 q v) p1))
  (store next19 q v) p2))))))


;; acyclic_list
  (assert
  (forall ((next20 t_pointer_pointer) (p pointer))
  (implies (not (= p null))
  (implies (is_list next20 p) (sep_node_list next20 p (select next20 p))))))


(assert
;; WP_list_rev
 ;; File "examples/programs/list_rev.mlw", line 108, characters 6-14
  (not
  (forall ((next21 t_pointer_pointer))
  (forall ((p pointer))
  (implies (is_list next21 p)
  (forall ((result pointer))
  (implies (= result null)
  (and
  (and (is_list next21 p)
  (and (is_list next21 result) (sep_list_list next21 p result)))
  (forall ((next22 t_pointer_pointer))
  (forall ((q pointer))
  (forall ((p1 pointer))
  (implies
  (and (is_list next22 p1)
  (and (is_list next22 q) (sep_list_list next22 p1 q)))
  (forall ((result1 pointer))
  (implies (= result1 p1)
  (if_then_else (not (= result1 null))
  (forall ((result2 t_pointer_pointer))
  (implies (= result2 next22)
  (forall ((result3 pointer))
  (implies (= result3 p1)
  (forall ((result4 t_pointer_pointer))
  (implies (= result4 next22)
  (forall ((result5 pointer))
  (implies (= result5 p1)
  (forall ((result6 pointer))
  (implies (= result6 q)
  (forall ((next23 t_pointer_pointer))
  (implies (= next23 (store result4 result5 result6))
  (forall ((result7 pointer))
  (implies (= result7 p1)
  (forall ((q1 pointer))
  (implies (= q1 result7)
  (forall ((p2 pointer))
  (implies (= p2 (select result2 result3))
  (and (is_list next23 p2)
  (and (is_list next23 q1) (sep_list_list next23 p2 q1)))))))))))))))))))))
  (is_list next22 q))))))))))))))))(check-sat)
