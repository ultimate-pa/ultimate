; chc-comp19-benchmarks/./lra-ts/chc-lra-ts-0091_000.smt2
(set-logic HORN)

(declare-fun |starexecinv1| ( Real Real Real Real ) Bool)

(assert
  (forall ( (A Real) (B Real) (C Real) (D Real) (E Real) ) 
    (=>
      (and
        (let ((a!1 (not (<= D (+ 1.0 (* (- 1.0) B) (* (- 1.0) A)))))
      (a!2 (not (<= D (+ 1.0 (* (- 1.0) B) A))))
      (a!3 (not (<= D (+ 1.0 B (* (- 1.0) A))))))
  (and (not (<= E 1.0))
       (not (<= E (* (- 1.0) B)))
       (not (<= E (* (- 1.0) A)))
       (not (<= E B))
       (not (<= E A))
       (not (<= D 1.0))
       (not (<= D (* (- 1.0) B)))
       (not (<= D (* (- 1.0) A)))
       a!1
       a!2
       a!3
       (not (<= D (+ 1.0 B A)))
       (not (<= D B))
       (not (<= D A))
       (= A (ite (>= B 0.0) C (- 1.0)))))
      )
      (starexecinv1 B A D E)
    )
  )
)
(assert
  (forall ( (A Real) (B Real) (C Real) (D Real) (E Real) (F Real) (G Real) (H Real) ) 
    (=>
      (and
        (starexecinv1 A B C D)
        (let ((a!1 (not (<= F (+ 1.0 E (* (- 1.0) H)))))
      (a!2 (not (<= F (+ 1.0 (* (- 1.0) E) H))))
      (a!3 (not (<= F (+ 1.0 (* (- 1.0) E) (* (- 1.0) H))))))
(let ((a!4 (and (<= D 0.0)
                (not (<= F E))
                (not (<= F H))
                (not (<= F (+ 1.0 E H)))
                a!1
                a!2
                a!3
                (not (<= F (* (- 1.0) E)))
                (not (<= F (* (- 1.0) H)))
                (not (<= F 1.0))
                (= G (+ (- 1.0) C)))))
(let ((a!5 (or (and (not (<= D 0.0)) (= F (+ (- 1.0) D)) (= G C)) a!4)))
  (and (>= B 0.0)
       (or (>= A 0.0) (>= B (- 1.0)))
       (or (<= B (- 1.0)) (>= A 0.0))
       a!5
       (= E A)))))
      )
      (starexecinv1 E H G F)
    )
  )
)
(assert
  (forall ( (A Real) (B Real) (C Real) (D Real) ) 
    (=>
      (and
        (starexecinv1 A B C D)
        (and (not (<= 0.0 C))
     (or (>= A 0.0) (>= B (- 1.0)))
     (or (<= B (- 1.0)) (>= A 0.0))
     (>= B 0.0))
      )
      false
    )
  )
)

(check-sat)
(exit)
