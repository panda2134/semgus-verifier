; modified from BVtest_XOR_02

(declare-term-types
((E 0) (Start 0))
((($IBVVarx )
($bvneg E)
($IBVVary )
($bvand E E)
($bvor E E))
(($bv=x E))))


(define-funs-rec
((E.Sem ((E_term_0 E) (r__0 (_ BitVec 32)) (x (_ BitVec 32)) (y (_ BitVec 32))) Bool)
(Start.Sem ((Start_term_0 Start) (x_r0 (_ BitVec 32)) (y_r0 (_ BitVec 32)) (x (_ BitVec 32)) (y (_ BitVec 32))) Bool))

((match E_term_0
  (($IBVVarx (exists ((r__1 (_ BitVec 32))) (and (= r__0 r__1)
  (= r__1 x))))
(($bvneg E_term_1) (exists ((r__1 (_ BitVec 32))) (and (= r__0 (bvnot r__1))
  (E.Sem E_term_1 r__1 x y))))
($IBVVary (exists ((r__1 (_ BitVec 32))) (and (= r__0 r__1)
  (= r__1 y))))
(($bvand E_term_1 E_term_2) (exists ((r__1 (_ BitVec 32)) (r__2 (_ BitVec 32))) (and (= r__0 (bvand r__1 r__2))
  (E.Sem E_term_1 r__1 x y)
  (E.Sem E_term_2 r__2 x y))))
(($bvor E_term_1 E_term_2) (exists ((r__1 (_ BitVec 32)) (r__2 (_ BitVec 32))) (and (= r__0 (bvor r__1 r__2))
  (E.Sem E_term_1 r__1 x y)
  (E.Sem E_term_2 r__2 x y))))))
(match Start_term_0
  ((($bv=x E_term_1) (exists ((r__1 (_ BitVec 32))) (and (and (= x_r0 r__1)
  (= y y_r0))
  (E.Sem E_term_1 r__1 x y))))))))


(synth-fun BVtest_XOR_02() Start)

(set-info :solution
  ((BVtest_XOR_02 ($bv=x
    ($bvor ($bvand $IBVVarx ($bvneg $IBVVary)) ($bvand $IBVVary ($bvneg $IBVVarx)))
  )))
)

(constraint (forall ((x0 (_ BitVec 32)) (y0 (_ BitVec 32)) (x1 (_ BitVec 32)) (y1 (_ BitVec 32)))
    (=> (Start.Sem BVtest_XOR_02 x1 y1 x0 y0) (= x1 (bvor (bvand x0 (bvneg y0)) (bvand y0 (bvnot x0)))))
))

(check-synth)
