; chc-comp19-benchmarks/./lia-lin-arr/chc-lia-lin-arr-0000_000.smt2
(set-logic HORN)

(declare-fun |inv| ( (Array Int Int) Int Int Int ) Bool)

(assert
  (forall ( (A (Array Int Int)) (B Int) (v_2 Int) (v_3 Int) ) 
    (=>
      (and
        (and true (= 0 v_2) (= 7 v_3))
      )
      (inv A v_2 v_3 B)
    )
  )
)
(assert
  (forall ( (A (Array Int Int)) (B Int) (C Int) (D Int) (E (Array Int Int)) (F Int) ) 
    (=>
      (and
        (inv A B C D)
        (and (= F (+ 1 B)) (<= B D) (= E (ite (= C B) (store A B 0) (store A B B))))
      )
      (inv E F C D)
    )
  )
)
(assert
  (forall ( (A (Array Int Int)) (B Int) (C Int) (D Int) (E Int) ) 
    (=>
      (and
        (inv A B C D)
        (and (<= 0 E) (not (<= B D)) (<= E D) (not (<= (select A E) C)))
      )
      false
    )
  )
)

(check-sat)
(exit)
