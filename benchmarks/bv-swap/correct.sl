(declare-term-types
((E 0) (Start 0) (Start1 0) (V 0))
((($bvxor V V))
(($seq Start1 Start1))
(($bv=x E)
($bv=y E))
(($IBVVary )
($IBVVarx ))))


(define-funs-rec
((E.Sem ((E_term_0 E) (r__0 (_ BitVec 32)) (x (_ BitVec 32)) (y (_ BitVec 32))) Bool)
(Start.Sem ((Start_term_0 Start) (x_r0 (_ BitVec 32)) (y_r0 (_ BitVec 32)) (x (_ BitVec 32)) (y (_ BitVec 32))) Bool)
(Start1.Sem ((Start1_term_0 Start1) (x_r0 (_ BitVec 32)) (y_r0 (_ BitVec 32)) (x (_ BitVec 32)) (y (_ BitVec 32))) Bool)
(V.Sem ((V_term_0 V) (r__0 (_ BitVec 32)) (x (_ BitVec 32)) (y (_ BitVec 32))) Bool))

((match E_term_0
  ((($bvxor V_term_1 V_term_2) (exists ((r__1 (_ BitVec 32)) (r__2 (_ BitVec 32))) (and (= r__0 (bvor (bvand r__1 (bvnot r__2)) (bvand (bvnot r__1) r__2)))
  (V.Sem V_term_1 r__1 x y)
  (V.Sem V_term_2 r__2 x y))))))
(match Start_term_0
  ((($seq Start1_term_1 Start1_term_2) (exists ((x_r1 (_ BitVec 32)) (y_r1 (_ BitVec 32))) (and (Start1.Sem Start1_term_1 x_r1 y_r1 x y)
  (Start1.Sem Start1_term_2 x_r0 y_r0 x_r1 y_r1))))))
(match Start1_term_0
  ((($bv=x E_term_1) (exists ((r__1 (_ BitVec 32))) (and (and (= x_r0 r__1) ;; here: x -> x_r0
  (= y y_r0))
  (E.Sem E_term_1 r__1 x y))))
(($bv=y E_term_1) (exists ((r__1 (_ BitVec 32))) (and (and (= x x_r0)
  (= y_r0 r__1)) ;; here: y -> y_r0
  (E.Sem E_term_1 r__1 x y))))))
(match V_term_0
  (($IBVVary (exists ((r__1 (_ BitVec 32))) (and (= r__0 r__1)
  (= r__1 y))))
($IBVVarx (exists ((r__1 (_ BitVec 32))) (and (= r__0 r__1)
  (= r__1 x))))))))


(synth-fun BVtest_Swap_XOR_01() Start)
(set-info :solution
  ((BVtest_Swap_XOR_01 ($seq                   
    ($seq
      ($bv=y ($bvxor $IBVVarx $IBVVary))
      ($bv=x ($bvxor $IBVVarx $IBVVary))
    )
    ($bv=y ($bvxor $IBVVarx $IBVVary))
  )))
)

(constraint 
  (forall ((x1 (_ BitVec 32)) (x2 (_ BitVec 32)) (y1 (_ BitVec 32)) (y2 (_ BitVec 32)))
          (=> (Start.Sem BVtest_Swap_XOR_01 x1 y1 x2 y2)
              (and (= x2 y1) (= x1 y2))
          ))
)

(check-synth)
