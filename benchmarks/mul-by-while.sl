;;;;
;;;; mul-by-while.sl - Multiply x and y and store result in z
;;;;

;;; Metadata
;; (set-info :format-version "2.1.0")
;; (set-info :author("Wiley Corning"))
;; (set-info :realizable true)

;;;
;;; Term types
;;;
(declare-term-types
 ;; Nonterminals
 ((S 0) (E 0) (B 0))

;; Productions
  (
    (
        ($assign_x E)
        ($assign_y E)
        ($assign_z E)
        ($cons S S)
        ($ite B S S)
        ($while B S)
    )
    (
        ($0)
        ($1)
        ($x); E productions
        ($y)
        ($z)
        ($+ E E)
        ($- E E)
        ($return_z S)
    )
    (
        ($t) ; B productions
        ($f)
        ($not B)
        ($and B B)
        ($or B B)
        ($< E E)
    )
    )
)

;;;
;;; Semantics
;;;
(define-funs-rec
    ;; CHC heads
    (
        (S.Sem ((t0 S) (x0 Int) (y0 Int) (z0 Int) (x2 Int) (y2 Int) (z2 Int)) Bool)
        (E.Sem ((t0 E) (x Int) (y Int) (z Int) (r Int)) Bool)
        (B.Sem ((t0 B) (x Int) (y Int) (z Int) (r Bool)) Bool)
    )

  ;; Bodies
  (
    ; Statements
    (! (match t0 (
            (($assign_x t1) (exists ((r1 Int)) (and
                (E.Sem t1 x0 y0 z0 r1)
                (= x2 r1) (= y2 y0) (= z2 z0)
            )))
            (($assign_y t1) (exists ((r1 Int)) (and
                (E.Sem t1 x0 y0 z0 r1)
                (= x2 x0) (= y2 r1) (= z2 z0)
            )))
            (($assign_z t1) (exists ((r1 Int)) (and
                (E.Sem t1 x0 y0 z0 r1)
                (= x2 x0) (= y2 y0) (= z2 r1)
            )))
            (($cons t1 t2) (exists ((x1 Int) (y1 Int) (z1 Int)) (and
                (S.Sem t1 x0 y0 z0 x1 y1 z1)
                (S.Sem t2 x1 y1 z1 x2 y2 z2)
            )))
            (($ite t1 t2 t3)
                (exists ((b Bool)) (and
                    (B.Sem t1 x0 y0 z0 b)
                    (= b true)
                    (S.Sem t2 x0 y0 z0 x2 y2 z2)
                ))
                (exists ((b Bool)) (and
                    (B.Sem t1 x0 y0 z0 b)
                    (= b false)
                    (S.Sem t3 x0 y0 z0 x2 y2 z2)
                ))
            )
            (($while t1 t2)
                (exists ((b Bool) (x1 Int) (y1 Int) (z1 Int))
                    (and
                        (B.Sem t1 x0 y0 z0 b)
                        (= b true)
                        (S.Sem t2 x0 y0 z0 x1 y1 z1)
                        (S.Sem t0 x1 y1 z1 x2 y2 z2)
                    )
                )
                (exists ((b Bool))
                    (and
                        (B.Sem t1 x0 y0 z0 b)
                        (= b false)
                        (= x2 x0) (= y2 y0) (= z2 z0)
                    )
                )
            )
        ))
        :input (x0 y0 z0) :output (x2 y2 z2)
    )

    ; Int expressions
    (! (match t0 (
        ($0 (= r 0))
        ($1 (= r 1))
        ($x (= r x))
        ($y (= r y))
        ($z (= r z))
        (($+ t1 t2) (exists ((r1 Int) (r2 Int)) (and
            (E.Sem t1 x y z r1)
            (E.Sem t2 x y z r2)
            (= r (+ r1 r2))
        )))
        (($- t1 t2) (exists ((r1 Int) (r2 Int)) (and
            (E.Sem t1 x y z r1)
            (E.Sem t2 x y z r2)
            (= r (- r1 r2))
        )))
        (($return_z t1) (exists ((x2 Int) (y2 Int) (z2 Int)) (and
            (S.Sem t1 x y z x2 y2 z2)
            (= r z2)
        )))
    )) :input (x y z) :output (r))

    ; Bool expressions
    (! (match t0 (
        ($t (= r true))
        ($f (= r false))
        (($< t1 t2) (exists ((r1 Int) (r2 Int)) (and
            (E.Sem t1 x y z r1)
            (E.Sem t2 x y z r2)
            (= r (< r1 r2))
        )))
        (($and t1 t2) (exists ((r1 Bool) (r2 Bool)) (and
            (B.Sem t1 x y z r1)
            (B.Sem t2 x y z r2)
            (= r (and r1 r2))
        )))
        (($or t1 t2) (exists ((r1 Bool) (r2 Bool)) (and
            (B.Sem t1 x y z r1)
            (B.Sem t2 x y z r2)
            (= r (or r1 r2))
        )))
        (($not t1) (exists ((r1 Bool)) (and
            (B.Sem t1 x y z r1)
            (= r (not r1))
        )))
    )) :input (x y z) :output (r))
  )
)


;;;
;;; Function to synthesize - a term rooted at Start
;;;
(synth-fun mul_by_while() S)

;;  (eval (while (> y 0) (cons (assign_z (+ z x)) (assign_y (- y 1)))))
(set-info :solution (
    (
        mul_by_while
        ($while ($< $0 $y)
            ($cons
                ($assign_z ($+ $z $x))
                ($assign_y ($- $y $1))
            )
        )
    )
))

;;;
;;; Constraints - Logical Formula
;;;
(constraint (forall ((x Int) (y Int) (x2 Int) (y2 Int) (z2 Int))
                (=> (S.Sem mul_by_while x y 0 x2 y2 z2)
                    (= z2 (* x y)))))

;;;
;;; Instruct the solver to find swap
;;;
(check-synth)
