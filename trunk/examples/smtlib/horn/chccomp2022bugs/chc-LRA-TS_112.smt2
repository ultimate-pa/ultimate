; sally-chc-benchmarks/./tte_synchro/tte_synchro.sm_clock_distance_strict_000.smt2
(set-logic HORN)

(declare-fun |invariant| ( Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Real Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool ) Bool)

(assert
  (forall ( (A Real) (B Real) (C Real) (D Real) (E Real) (F Real) (G Real) (H Real) (I Real) (J Real) (K Real) (L Real) (M Real) (N Real) (O Real) (P Real) (Q Real) (R Real) (S Real) (T Real) (U Real) (V Real) (W Real) (X Real) (Y Real) (Z Real) (A1 Real) (B1 Real) (C1 Real) (D1 Real) (E1 Real) (F1 Real) (G1 Real) (H1 Real) (I1 Real) (J1 Real) (K1 Real) (L1 Bool) (M1 Bool) (N1 Bool) (O1 Bool) (P1 Bool) (Q1 Bool) (R1 Bool) (S1 Bool) (T1 Bool) (U1 Bool) ) 
    (=>
      (and
        (and (= J1 0.0)
     (= I1 0.0)
     (= H1 0.0)
     (= G1 0.0)
     (= F1 V)
     (= E1 U)
     (= C1 S)
     (= B1 R)
     (= A1 V)
     (= Z U)
     (= X S)
     (= W R)
     (= V 0.0)
     (= U 0.0)
     (= T 0.0)
     (= S 0.0)
     (= R 0.0)
     (= G 0.0)
     (= F 0.0)
     (= E 0.0)
     (= D 0.0)
     (= C 0.0)
     (= B 0.0)
     (not (<= A 0.0))
     (or (= Q 1.0) (= Q 2.0) (= Q 3.0) (= Q 4.0) (= Q 5.0))
     (or (= P 1.0) (= P 2.0) (= P 3.0) (= P 4.0) (= P 5.0))
     (or (= O 1.0) (= O 2.0) (= O 3.0) (= O 4.0) (= O 5.0))
     (or (= N 1.0) (= N 2.0) (= N 3.0) (= N 4.0) (= N 5.0))
     (or (= M 1.0) (= M 2.0) (= M 3.0) (= M 4.0) (= M 5.0))
     (or (= L 1.0) (= L 2.0) (= L 3.0) (= L 4.0) (= L 5.0))
     (or (= K 1.0) (= K 2.0) (= K 3.0) (= K 4.0) (= K 5.0))
     (or (= J 1.0) (= J 2.0) (= J 3.0) (= J 4.0) (= J 5.0))
     (or (= I 1.0) (= I 2.0) (= I 3.0) (= I 4.0) (= I 5.0))
     (or (= H 1.0) (= H 2.0) (= H 3.0) (= H 4.0) (= H 5.0))
     (or (= K1 0.0) (= K1 1.0) (= K1 2.0))
     (or (= J1 0.0) (= J1 1.0) (= J1 2.0))
     (or (= I1 0.0) (= I1 1.0) (= I1 2.0))
     (or (= H1 0.0) (= H1 1.0) (= H1 2.0))
     (or (= G1 0.0) (= G1 1.0) (= G1 2.0))
     (or (= E 0.0) (= E 1.0) (= E 2.0))
     (or (= D 0.0) (= D 1.0) (= D 2.0))
     (= U1 true)
     (= T1 true)
     (= R1 true)
     (= Q1 true)
     (= P1 true)
     (= O1 true)
     (= M1 true)
     (= L1 true)
     (= K1 0.0))
      )
      (invariant A
           B
           C
           D
           E
           F
           G
           H
           I
           J
           K
           L
           M
           N
           O
           P
           Q
           R
           S
           T
           U
           V
           W
           X
           Y
           Z
           A1
           B1
           C1
           D1
           E1
           F1
           G1
           H1
           I1
           J1
           K1
           L1
           M1
           N1
           O1
           P1
           Q1
           R1
           S1
           T1
           U1)
    )
  )
)
(assert
  (forall ( (A Real) (B Real) (C Real) (D Real) (E Real) (F Real) (G Real) (H Real) (I Real) (J Real) (K Real) (L Real) (M Real) (N Real) (O Real) (P Real) (Q Real) (R Real) (S Real) (T Real) (U Real) (V Real) (W Real) (X Real) (Y Real) (Z Real) (A1 Real) (B1 Real) (C1 Real) (D1 Real) (E1 Real) (F1 Real) (G1 Real) (H1 Real) (I1 Real) (J1 Real) (K1 Real) (L1 Real) (M1 Real) (N1 Real) (O1 Real) (P1 Real) (Q1 Real) (R1 Real) (S1 Real) (T1 Real) (U1 Real) (V1 Real) (W1 Real) (X1 Real) (Y1 Real) (Z1 Real) (A2 Real) (B2 Real) (C2 Real) (D2 Real) (E2 Real) (F2 Real) (G2 Real) (H2 Real) (I2 Real) (J2 Real) (K2 Real) (L2 Real) (M2 Real) (N2 Real) (O2 Real) (P2 Real) (Q2 Real) (R2 Real) (S2 Real) (T2 Real) (U2 Real) (V2 Real) (W2 Bool) (X2 Bool) (Y2 Bool) (Z2 Bool) (A3 Bool) (B3 Bool) (C3 Bool) (D3 Bool) (E3 Bool) (F3 Bool) (G3 Bool) (H3 Bool) (I3 Bool) (J3 Bool) (K3 Bool) (L3 Bool) (M3 Bool) (N3 Bool) (O3 Bool) (P3 Bool) ) 
    (=>
      (and
        (invariant A
           C
           E
           G
           I
           K
           M
           O
           Q
           S
           U
           W
           Y
           A1
           C1
           E1
           G1
           I1
           K1
           M1
           O1
           Q1
           S1
           U1
           W1
           Y1
           A2
           C2
           E2
           G2
           I2
           K2
           M2
           O2
           Q2
           S2
           U2
           W2
           Y2
           A3
           C3
           E3
           G3
           I3
           K3
           M3
           O3)
        (let ((a!1 (and (<= F (+ E A))
                (<= (+ E (* (- 1.0) A)) F)
                (= I 2.0)
                (= J 0.0)
                (= N M)))
      (a!2 (ite (= Z 4.0) I2 (ite (= Z 3.0) G2 (ite (= Z 2.0) E2 C2))))
      (a!3 (ite (= B1 4.0) I2 (ite (= B1 3.0) G2 (ite (= B1 2.0) E2 C2))))
      (a!5 (ite (= D1 4.0) I2 (ite (= D1 3.0) G2 (ite (= D1 2.0) E2 C2))))
      (a!7 (ite (= Z 4.0) M3 (ite (= Z 3.0) K3 (ite (= Z 2.0) I3 G3))))
      (a!8 (ite (= B1 4.0) M3 (ite (= B1 3.0) K3 (ite (= B1 2.0) I3 G3))))
      (a!9 (ite (= D1 4.0) M3 (ite (= D1 3.0) K3 (ite (= D1 2.0) I3 G3))))
      (a!10 (ite (= F1 4.0) M3 (ite (= F1 3.0) K3 (ite (= F1 2.0) I3 G3))))
      (a!11 (ite (= H1 4.0) M3 (ite (= H1 3.0) K3 (ite (= H1 2.0) I3 G3))))
      (a!13 (ite (= F1 4.0) I2 (ite (= F1 3.0) G2 (ite (= F1 2.0) E2 C2))))
      (a!17 (ite (= H1 4.0) I2 (ite (= H1 3.0) G2 (ite (= H1 2.0) E2 C2))))
      (a!19 (and (<= D (+ C A))
                 (<= (+ C (* (- 1.0) A)) D)
                 (= G 2.0)
                 (= H 0.0)
                 (= L K)))
      (a!20 (ite (= P 4.0) Y1 (ite (= P 3.0) W1 (ite (= P 2.0) U1 S1))))
      (a!21 (ite (= R 4.0) Y1 (ite (= R 3.0) W1 (ite (= R 2.0) U1 S1))))
      (a!23 (ite (= T 4.0) Y1 (ite (= T 3.0) W1 (ite (= T 2.0) U1 S1))))
      (a!25 (ite (= P 4.0) C3 (ite (= P 3.0) A3 (ite (= P 2.0) Y2 W2))))
      (a!26 (ite (= R 4.0) C3 (ite (= R 3.0) A3 (ite (= R 2.0) Y2 W2))))
      (a!27 (ite (= T 4.0) C3 (ite (= T 3.0) A3 (ite (= T 2.0) Y2 W2))))
      (a!28 (ite (= V 4.0) C3 (ite (= V 3.0) A3 (ite (= V 2.0) Y2 W2))))
      (a!29 (ite (= X 4.0) C3 (ite (= X 3.0) A3 (ite (= X 2.0) Y2 W2))))
      (a!31 (ite (= V 4.0) Y1 (ite (= V 3.0) W1 (ite (= V 2.0) U1 S1))))
      (a!35 (ite (= X 4.0) Y1 (ite (= X 3.0) W1 (ite (= X 2.0) U1 S1))))
      (a!37 (and (= U2 1.0)
                 (= V2 2.0)
                 (= R1 (+ (* (/ 1.0 2.0) K) (* (/ 1.0 2.0) M)))))
      (a!38 (and (<= R1 (+ Q1 A))
                 (<= (+ Q1 (* (- 1.0) A)) R1)
                 (= U2 2.0)
                 (= V2 0.0)))
      (a!39 (and (= S2 1.0)
                 (= T2 2.0)
                 (= P1 (+ (* (/ 1.0 2.0) K) (* (/ 1.0 2.0) M)))))
      (a!40 (and (<= P1 (+ O1 A))
                 (<= (+ O1 (* (- 1.0) A)) P1)
                 (= S2 2.0)
                 (= T2 0.0)))
      (a!41 (and (= Q2 1.0)
                 (= R2 2.0)
                 (= N1 (+ (* (/ 1.0 2.0) K) (* (/ 1.0 2.0) M)))))
      (a!42 (and (<= N1 (+ M1 A))
                 (<= (+ M1 (* (- 1.0) A)) N1)
                 (= Q2 2.0)
                 (= R2 0.0)))
      (a!43 (and (= O2 1.0)
                 (= P2 2.0)
                 (= L1 (+ (* (/ 1.0 2.0) K) (* (/ 1.0 2.0) M)))))
      (a!44 (and (<= L1 (+ K1 A))
                 (<= (+ K1 (* (- 1.0) A)) L1)
                 (= O2 2.0)
                 (= P2 0.0)))
      (a!45 (and (= M2 1.0)
                 (= N2 2.0)
                 (= J1 (+ (* (/ 1.0 2.0) K) (* (/ 1.0 2.0) M)))))
      (a!46 (and (<= J1 (+ I1 A))
                 (<= (+ I1 (* (- 1.0) A)) J1)
                 (= M2 2.0)
                 (= N2 0.0))))
(let ((a!4 (<= (ite (= Z 5.0) K2 a!2) (ite (= B1 5.0) K2 a!3)))
      (a!6 (<= (ite (= B1 5.0) K2 a!3) (ite (= D1 5.0) K2 a!5)))
      (a!14 (<= (ite (= D1 5.0) K2 a!5) (ite (= F1 5.0) K2 a!13)))
      (a!15 (+ (* (/ 1.0 2.0) (ite (= B1 5.0) K2 a!3))
               (* (/ 1.0 2.0) (ite (= D1 5.0) K2 a!5))))
      (a!22 (<= (ite (= P 5.0) A2 a!20) (ite (= R 5.0) A2 a!21)))
      (a!24 (<= (ite (= R 5.0) A2 a!21) (ite (= T 5.0) A2 a!23)))
      (a!32 (<= (ite (= T 5.0) A2 a!23) (ite (= V 5.0) A2 a!31)))
      (a!33 (+ (* (/ 1.0 2.0) (ite (= R 5.0) A2 a!21))
               (* (/ 1.0 2.0) (ite (= T 5.0) A2 a!23)))))
(let ((a!12 (and a!4
                 a!6
                 (= F E)
                 (= I 0.0)
                 (= J 1.0)
                 (= N (ite (= B1 5.0) K2 a!3))
                 (not (= Z B1))
                 (not (= Z D1))
                 (not (= Z F1))
                 (not (= Z H1))
                 (not (= B1 Z))
                 (not (= B1 D1))
                 (not (= B1 F1))
                 (not (= B1 H1))
                 (not (= D1 Z))
                 (not (= D1 B1))
                 (not (= D1 F1))
                 (not (= D1 H1))
                 (not (= F1 Z))
                 (not (= F1 B1))
                 (not (= F1 D1))
                 (not (= F1 H1))
                 (not (= H1 Z))
                 (not (= H1 B1))
                 (not (= H1 D1))
                 (not (= H1 F1))
                 (ite (= Z 5.0) O3 a!7)
                 (ite (= B1 5.0) O3 a!8)
                 (ite (= D1 5.0) O3 a!9)
                 (not (ite (= F1 5.0) O3 a!10))
                 (not (ite (= H1 5.0) O3 a!11))))
      (a!16 (and a!4
                 a!6
                 a!14
                 (= F E)
                 (= I 0.0)
                 (= J 1.0)
                 (= N a!15)
                 (not (= Z B1))
                 (not (= Z D1))
                 (not (= Z F1))
                 (not (= Z H1))
                 (not (= B1 Z))
                 (not (= B1 D1))
                 (not (= B1 F1))
                 (not (= B1 H1))
                 (not (= D1 Z))
                 (not (= D1 B1))
                 (not (= D1 F1))
                 (not (= D1 H1))
                 (not (= F1 Z))
                 (not (= F1 B1))
                 (not (= F1 D1))
                 (not (= F1 H1))
                 (not (= H1 Z))
                 (not (= H1 B1))
                 (not (= H1 D1))
                 (not (= H1 F1))
                 (ite (= Z 5.0) O3 a!7)
                 (ite (= B1 5.0) O3 a!8)
                 (ite (= D1 5.0) O3 a!9)
                 (ite (= F1 5.0) O3 a!10)
                 (not (ite (= H1 5.0) O3 a!11))))
      (a!18 (and a!4
                 a!6
                 a!14
                 (<= (ite (= F1 5.0) K2 a!13) (ite (= H1 5.0) K2 a!17))
                 (= F E)
                 (= I 0.0)
                 (= J 1.0)
                 (= N (ite (= D1 5.0) K2 a!5))
                 (not (= Z B1))
                 (not (= Z D1))
                 (not (= Z F1))
                 (not (= Z H1))
                 (not (= B1 Z))
                 (not (= B1 D1))
                 (not (= B1 F1))
                 (not (= B1 H1))
                 (not (= D1 Z))
                 (not (= D1 B1))
                 (not (= D1 F1))
                 (not (= D1 H1))
                 (not (= F1 Z))
                 (not (= F1 B1))
                 (not (= F1 D1))
                 (not (= F1 H1))
                 (not (= H1 Z))
                 (not (= H1 B1))
                 (not (= H1 D1))
                 (not (= H1 F1))
                 (ite (= Z 5.0) O3 a!7)
                 (ite (= B1 5.0) O3 a!8)
                 (ite (= D1 5.0) O3 a!9)
                 (ite (= F1 5.0) O3 a!10)
                 (ite (= H1 5.0) O3 a!11)))
      (a!30 (and a!22
                 a!24
                 (= D C)
                 (= G 0.0)
                 (= H 1.0)
                 (= L (ite (= R 5.0) A2 a!21))
                 (not (= P R))
                 (not (= P T))
                 (not (= P V))
                 (not (= P X))
                 (not (= R P))
                 (not (= R T))
                 (not (= R V))
                 (not (= R X))
                 (not (= T P))
                 (not (= T R))
                 (not (= T V))
                 (not (= T X))
                 (not (= V P))
                 (not (= V R))
                 (not (= V T))
                 (not (= V X))
                 (not (= X P))
                 (not (= X R))
                 (not (= X T))
                 (not (= X V))
                 (ite (= P 5.0) E3 a!25)
                 (ite (= R 5.0) E3 a!26)
                 (ite (= T 5.0) E3 a!27)
                 (not (ite (= V 5.0) E3 a!28))
                 (not (ite (= X 5.0) E3 a!29))))
      (a!34 (and a!22
                 a!24
                 a!32
                 (= D C)
                 (= G 0.0)
                 (= H 1.0)
                 (= L a!33)
                 (not (= P R))
                 (not (= P T))
                 (not (= P V))
                 (not (= P X))
                 (not (= R P))
                 (not (= R T))
                 (not (= R V))
                 (not (= R X))
                 (not (= T P))
                 (not (= T R))
                 (not (= T V))
                 (not (= T X))
                 (not (= V P))
                 (not (= V R))
                 (not (= V T))
                 (not (= V X))
                 (not (= X P))
                 (not (= X R))
                 (not (= X T))
                 (not (= X V))
                 (ite (= P 5.0) E3 a!25)
                 (ite (= R 5.0) E3 a!26)
                 (ite (= T 5.0) E3 a!27)
                 (ite (= V 5.0) E3 a!28)
                 (not (ite (= X 5.0) E3 a!29))))
      (a!36 (and a!22
                 a!24
                 a!32
                 (<= (ite (= V 5.0) A2 a!31) (ite (= X 5.0) A2 a!35))
                 (= D C)
                 (= G 0.0)
                 (= H 1.0)
                 (= L (ite (= T 5.0) A2 a!23))
                 (not (= P R))
                 (not (= P T))
                 (not (= P V))
                 (not (= P X))
                 (not (= R P))
                 (not (= R T))
                 (not (= R V))
                 (not (= R X))
                 (not (= T P))
                 (not (= T R))
                 (not (= T V))
                 (not (= T X))
                 (not (= V P))
                 (not (= V R))
                 (not (= V T))
                 (not (= V X))
                 (not (= X P))
                 (not (= X R))
                 (not (= X T))
                 (not (= X V))
                 (ite (= P 5.0) E3 a!25)
                 (ite (= R 5.0) E3 a!26)
                 (ite (= T 5.0) E3 a!27)
                 (ite (= V 5.0) E3 a!28)
                 (ite (= X 5.0) E3 a!29))))
  (and (= T1 J1)
       (= S1 I1)
       (= B A)
       (= L2 R1)
       (= K2 Q1)
       (= J2 P1)
       (= I2 O1)
       (= F2 L1)
       (= E2 K1)
       (= D2 J1)
       (= C2 I1)
       (= B2 R1)
       (= A2 Q1)
       (= Z1 P1)
       (= Y1 O1)
       (= V1 L1)
       (not (<= B 0.0))
       (not (<= A 0.0))
       (or (= H1 1.0) (= H1 2.0) (= H1 3.0) (= H1 4.0) (= H1 5.0))
       (or (= G1 1.0) (= G1 2.0) (= G1 3.0) (= G1 4.0) (= G1 5.0))
       (or (= F1 1.0) (= F1 2.0) (= F1 3.0) (= F1 4.0) (= F1 5.0))
       (or (= E1 1.0) (= E1 2.0) (= E1 3.0) (= E1 4.0) (= E1 5.0))
       (or (= D1 1.0) (= D1 2.0) (= D1 3.0) (= D1 4.0) (= D1 5.0))
       (or (= C1 1.0) (= C1 2.0) (= C1 3.0) (= C1 4.0) (= C1 5.0))
       (or (= B1 1.0) (= B1 2.0) (= B1 3.0) (= B1 4.0) (= B1 5.0))
       (or (= A1 1.0) (= A1 2.0) (= A1 3.0) (= A1 4.0) (= A1 5.0))
       (or (= Z 1.0) (= Z 2.0) (= Z 3.0) (= Z 4.0) (= Z 5.0))
       (or (= Y 1.0) (= Y 2.0) (= Y 3.0) (= Y 4.0) (= Y 5.0))
       (or (= X 1.0) (= X 2.0) (= X 3.0) (= X 4.0) (= X 5.0))
       (or (= W 1.0) (= W 2.0) (= W 3.0) (= W 4.0) (= W 5.0))
       (or (= V 1.0) (= V 2.0) (= V 3.0) (= V 4.0) (= V 5.0))
       (or (= U 1.0) (= U 2.0) (= U 3.0) (= U 4.0) (= U 5.0))
       (or (= T 1.0) (= T 2.0) (= T 3.0) (= T 4.0) (= T 5.0))
       (or (= S 1.0) (= S 2.0) (= S 3.0) (= S 4.0) (= S 5.0))
       (or (= R 1.0) (= R 2.0) (= R 3.0) (= R 4.0) (= R 5.0))
       (or (= Q 1.0) (= Q 2.0) (= Q 3.0) (= Q 4.0) (= Q 5.0))
       (or (= P 1.0) (= P 2.0) (= P 3.0) (= P 4.0) (= P 5.0))
       (or (= O 1.0) (= O 2.0) (= O 3.0) (= O 4.0) (= O 5.0))
       (or (and (= F M) (= I 1.0) (= J 2.0) (= N M)) a!1 a!12 a!16 a!18)
       (or (and (= D K) (= G 1.0) (= H 2.0) (= L K)) a!19 a!30 a!34 a!36)
       (or (= J 0.0) (= J 1.0) (= J 2.0))
       (or (= I 0.0) (= I 1.0) (= I 2.0))
       (or (= H 0.0) (= H 1.0) (= H 2.0))
       (or (= G 0.0) (= G 1.0) (= G 2.0))
       (or (= V2 0.0) (= V2 1.0) (= V2 2.0))
       (or (= U2 0.0) (= U2 1.0) (= U2 2.0))
       (or (= T2 0.0) (= T2 1.0) (= T2 2.0))
       (or (= S2 0.0) (= S2 1.0) (= S2 2.0))
       (or (= R2 0.0) (= R2 1.0) (= R2 2.0))
       (or (= Q2 0.0) (= Q2 1.0) (= Q2 2.0))
       (or (= P2 0.0) (= P2 1.0) (= P2 2.0))
       (or (= O2 0.0) (= O2 1.0) (= O2 2.0))
       (or (= N2 0.0) (= N2 1.0) (= N2 2.0))
       (or (= M2 0.0) (= M2 1.0) (= M2 2.0))
       (or (and (= U2 0.0) (= V2 1.0) (= R1 Q1)) a!37 a!38)
       (or (and (= S2 0.0) (= T2 1.0) (= P1 O1)) a!39 a!40)
       (or (and (= Q2 0.0) (= R2 1.0) (= N1 M1)) a!41 a!42)
       (or (and (= O2 0.0) (= P2 1.0) (= L1 K1)) a!43 a!44)
       (or (and (= M2 0.0) (= N2 1.0) (= J1 I1)) a!45 a!46)
       (= F3 true)
       (= E3 true)
       (= D3 true)
       (= C3 true)
       (= Z2 true)
       (= Y2 true)
       (= X2 true)
       (= W2 true)
       (= P3 true)
       (= O3 true)
       (= N3 true)
       (= M3 true)
       (= J3 true)
       (= I3 true)
       (= H3 true)
       (= G3 true)
       (= U1 K1)))))
      )
      (invariant B
           D
           F
           H
           J
           L
           N
           P
           R
           T
           V
           X
           Z
           B1
           D1
           F1
           H1
           J1
           L1
           N1
           P1
           R1
           T1
           V1
           X1
           Z1
           B2
           D2
           F2
           H2
           J2
           L2
           N2
           P2
           R2
           T2
           V2
           X2
           Z2
           B3
           D3
           F3
           H3
           J3
           L3
           N3
           P3)
    )
  )
)
(assert
  (forall ( (A Real) (B Real) (C Real) (D Real) (E Real) (F Real) (G Real) (H Real) (I Real) (J Real) (K Real) (L Real) (M Real) (N Real) (O Real) (P Real) (Q Real) (R Real) (S Real) (T Real) (U Real) (V Real) (W Real) (X Real) (Y Real) (Z Real) (A1 Real) (B1 Real) (C1 Real) (D1 Real) (E1 Real) (F1 Real) (G1 Real) (H1 Real) (I1 Real) (J1 Real) (K1 Real) (L1 Bool) (M1 Bool) (N1 Bool) (O1 Bool) (P1 Bool) (Q1 Bool) (R1 Bool) (S1 Bool) (T1 Bool) (U1 Bool) ) 
    (=>
      (and
        (invariant A
           B
           C
           D
           E
           F
           G
           H
           I
           J
           K
           L
           M
           N
           O
           P
           Q
           R
           S
           T
           U
           V
           W
           X
           Y
           Z
           A1
           B1
           C1
           D1
           E1
           F1
           G1
           H1
           I1
           J1
           K1
           L1
           M1
           N1
           O1
           P1
           Q1
           R1
           S1
           T1
           U1)
        (or (<= A 0.0)
    (<= (* 2.0 A) (+ R (* (- 1.0) S)))
    (<= (* 2.0 A) (+ R (* (- 1.0) T)))
    (<= (* 2.0 A) (+ R (* (- 1.0) U)))
    (<= (* 2.0 A) (+ R (* (- 1.0) V)))
    (<= (* 2.0 A) (+ S (* (- 1.0) R)))
    (<= (* 2.0 A) (+ S (* (- 1.0) T)))
    (<= (* 2.0 A) (+ S (* (- 1.0) U)))
    (<= (* 2.0 A) (+ S (* (- 1.0) V)))
    (<= (* 2.0 A) (+ T (* (- 1.0) R)))
    (<= (* 2.0 A) (+ T (* (- 1.0) S)))
    (<= (* 2.0 A) (+ T (* (- 1.0) U)))
    (<= (* 2.0 A) (+ T (* (- 1.0) V)))
    (<= (* 2.0 A) (+ U (* (- 1.0) R)))
    (<= (* 2.0 A) (+ U (* (- 1.0) S)))
    (<= (* 2.0 A) (+ U (* (- 1.0) T)))
    (<= (* 2.0 A) (+ U (* (- 1.0) V)))
    (<= (* 2.0 A) (+ V (* (- 1.0) R)))
    (<= (* 2.0 A) (+ V (* (- 1.0) S)))
    (<= (* 2.0 A) (+ V (* (- 1.0) T)))
    (<= (* 2.0 A) (+ V (* (- 1.0) U))))
      )
      false
    )
  )
)

(check-sat)
(exit)
