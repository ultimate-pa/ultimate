; chc-comp19-benchmarks/./lra-ts/chc-lra-ts-0092_000.smt2
(set-logic HORN)

(declare-fun |starexecinv1| ( Real Real Real Real ) Bool)

(assert
  (forall ( (A Real) (B Real) (C Real) (D Real) ) 
    (=>
      (and
        (let ((a!1 (not (<= D (+ 9.0 (* (- 1.0) A) (* (- 1.0) B) (* (- 1.0) C)))))
      (a!2 (not (<= D (+ 9.0 A (* (- 1.0) B) (* (- 1.0) C)))))
      (a!3 (not (<= D (+ 9.0 A (* (- 1.0) B) C))))
      (a!4 (not (<= D (+ 9.0 (* (- 1.0) A) C))))
      (a!5 (not (<= D (+ 1.0 (* (- 1.0) C))))))
  (and (= C (- 1.0))
       (= B 0.0)
       (not (<= D 9.0))
       (not (<= D (* (- 1.0) C)))
       (not (<= D (* (- 1.0) B)))
       (not (<= D (* (- 1.0) A)))
       a!1
       a!2
       a!3
       a!4
       (not (<= D (+ 9.0 B)))
       a!5
       (not (<= D (+ 1.0 C)))
       (not (<= D (+ 1.0 A)))
       (not (<= D C))
       (not (<= D B))
       (not (<= D A))
       (= 1.0 A)))
      )
      (starexecinv1 A B C D)
    )
  )
)
(assert
  (forall ( (A Real) (B Real) (C Real) (D Real) (E Real) (F Real) (G Bool) (H Real) (I Real) (J Real) ) 
    (=>
      (and
        (starexecinv1 A B C D)
        (and (= 1.0 E)
     (= 1.0 A)
     (not (= C 0.0))
     (= J (+ (- 1.0) D))
     (= I (ite G 1.0 (+ (- 1.0) F)))
     (= H (+ 1.0 B))
     (>= F 1.0)
     (not (>= C 6.0))
     (>= C (- 1.0))
     (>= B 0.0)
     (>= A 1.0)
     (not (<= 7.0 F))
     (<= A 1.0)
     (= G (= B 9.0)))
      )
      (starexecinv1 E H I J)
    )
  )
)
(assert
  (forall ( (A Real) (B Real) (C Real) (D Real) ) 
    (=>
      (and
        (starexecinv1 A B C D)
        (and (not (= C 0.0))
     (not (>= C 6.0))
     (>= C (- 1.0))
     (>= B 0.0)
     (>= A 1.0)
     (not (<= 0.0 D))
     (<= A 1.0)
     (= 1.0 A))
      )
      false
    )
  )
)

(check-sat)
(exit)
