(set-option :print-success false)
(set-logic QF_UFLIRA)
(declare-sort U 0)

; VARIABLES
(declare-fun c () Bool)
(declare-fun t () Bool)
(declare-fun e () Bool)
(declare-fun p () Bool)
(declare-fun q () Bool)
(declare-fun r () Bool)
(declare-fun s () Bool)
(declare-fun u () Real)
(declare-fun v () Real)
(declare-fun w () Real)
(declare-fun x () Int)
(declare-fun y () Int)
(declare-fun z () Int)
(declare-fun xU () U)
(declare-fun yU () U)
(declare-fun aAmMzZ0123456789._-+*~!$%&/=?<>^ () Bool)

; FUNCTIONS
(declare-fun fII (Int) Int)
(declare-fun fBB (Bool) Bool)
(declare-fun fBI (Bool) Int)
(declare-fun fUUU (U U) U)

; EXAMPLES

;--- string and function compatibility ---;

; string compatibility
; (assert (and aAmMzZ0123456789._-+*~!$%&/=?<>^ (not aAmMzZ0123456789._-+*~!$%&/=?<>^)))

; function compatibility
; Replace the line '(set-logic QF_UFLIRA)' by '(set-logic QF_UF)' and remove the
; VARIABLES and FUNCTIONS for the conversion for SMT-LIB non-theory functions.
; (declare-sort Int 0) (declare-sort Real 0)
; (declare-fun <= (Int Int) Bool)
; (declare-fun < (Int Int) Bool)
; (declare-fun >= (Int Int) Bool)
; (declare-fun > (Int Int) Bool)
; (declare-fun + (Int Int) Int)
; (declare-fun - (Int) Int)
; (declare-fun * (Int Int) Int)
; (declare-fun / (Real Real) Real)
; (declare-fun mod (Int Int) Int)
; (declare-fun div (Int Int) Int)
; (declare-fun abs (Int) Int)
; (declare-fun divisible (Int Int) Bool)
; (declare-fun to_int (Real) Int)
; (declare-fun to_real (Int) Real)
; (declare-fun is_int (Real) Bool)
; (declare-fun x () Int)
; (declare-fun u () Real)
; (assert (and (distinct x x) (< (+ x x) (* (- (abs x)) (to_int (/ u u))))
;  (<= x (to_int (to_real x))) (> (div x x) (mod x x)) (>= x x) (is_int u)
; (divisible x x)))

;--- RESOLUTION ---;

; res_false, res_l and duplicate
; (assert (and (or (not p) r) p (or q (not r)) (not q)))

; all cases together, including duplicates
; (assert (or
;  (and (= (fBI p) 0) (= (fBI false) 1) (= (fBI true) 2))
;  (and (not p) (not t) (or (ite (not p) t e) t))
; ))

;--- LEMMA ---;

;-- CC --;

; case with Diseq
; (assert (and (= xU yU) (= (fUUU xU xU) xU) (not (= (fUUU (fUUU xU xU) yU) (fUUU yU xU)))))

; case without Diseq
; (assert (and (= (fII 1) 1) (= (fII 1) 2)))

;-- LA --;

; integer case
; (assert (not (or (<= y 0) (not (<= (+ (* (- 3) x) (* 2 y) 3) 0)) (not (= (+ x (- 1)) 0)))))

; real case including fractions
; (assert (not (or (<= v 0) (not (<= (+ (* (- 3) u) (* 2 v) 3) 0)) (not (= (+ (* (/ 3 2) u) (- (/ 1 2))) 0)))))

; mixed case including fractions
; (assert (not (or (<= y 0) (not (<= (+ (* (- 3) u) (* 2 y) 3) 0)) (not (= (+ (* (/ 3 2) u) (- (/ 1 2))) 0)))))

;-- Trichotomy --;
; order LEG
; (assert (not (or (= x y) (< x y) (> x y))))

; order GEL
; (assert (not (or (< x y) (= x y) (> x y))))

; order LGE
; (assert (not (or (= x 0) (< x 0) (> x 0))))


;--- TAUTOLOGY ---;

; :trueNotFalse
; (assert (and (= (fBB p) p) (not (= (fBB (fBB p)) p))))

; :or+
; (assert (and (or (not (or p q)) (not (or q p))) (or (or p q) (or q p))))

; :or-
; (assert (or
;  (and (not p) (not q) (or (and p q) q))
;  (and (not p) (not (or p (or q p)))
;   (or (and p (or p (or q p))) (or p q)))
; ))

; :ite+1
; (assert (and (not c) (not t) (or (ite (not c) t e) t)))

; :ite+2
; (assert (and (not c) (not e) (or (ite c t e) e)))

; :ite+red
; (assert (and (not c) (not e) (or (ite c c e) e)))

; :ite-1
; (assert (and c t (not e) (or (not (ite c t e)) (not c) (not t))))

; :ite-2
; (assert (and (not c) (not t) e (or (not (ite c t e)) c t)))

; :ite-red
; (assert (and c t e (or (not (ite c t e)) (not c) (not t))))

; :=+1
; (assert (and (not p) q (or (= p q) p (not q))))

; :=+2
; (assert (and p (not q) (or (= p q) (not p) q)))

; :=-1
; (assert (and (not p) (not q) (or (not (= p q)) p q)))

; :=-2
; (assert (and p q (or (not (= p q)) (not p) (not q))))

; :excludedMiddle1, :excludedMiddle2 (by Jürgen Christ)
; (assert (and (= (fBI p) 0) (= (fBI false) 1) (= (fBI true) 2)))

; :termITE (each disjunct for one of the four cases)
; (assert (or 
;  (not (or (not p) (= (ite p x y) x)))
;  (not (or (not (not p)) (= (ite p x y) y)))
;  (not (or (not p) (not q) (= (ite p (ite q x y) z) x)))
;  (not (or (not (not p)) (not (not q)) (= (ite p x (ite q y z)) z)))
; ))

; :divLow (each disjunct for one of the four cases)
; (assert (or
;  (not (<= (- (* 2 (div x 2)) x) 0))
;  (not (<= (- (* 2 (div (- x) 2)) (- x)) 0))
;  (not (<= (- (* 2 (div (* 2 (- x)) 2)) (* 2 (- x))) 0))
;  (not (<= (- (* 2 (div (* (- 2) (- x)) 2)) (* (- 2) (- x))) 0))
; ))

; :divHigh (each disjunct for one of the four cases)
; (assert (or
;  (<= (+ (- 2 x) (* 2 (div x 2))) 0)
;  (<= (+ (- 2 (- x)) (* 2 (div (- x) 2))) 0)
;  (<= (+ (- 2 (* 2 (- x))) (* 2 (div (* 2 (- x)) 2))) 0)
;  (<= (+ (- 2 (* (- 2) (- x))) (* 2 (div (* (- 2) (- x)) 2))) 0)
; ))

; :toIntLow (each disjunct for one of the four cases)
; (assert (or
;  (not (<= (- (to_real (to_int u)) u) 0))
;  (not (<= (- (to_real (to_int (- u))) (- u)) 0))
;  (not (<= (- (to_real (to_int (* 2 (- u)))) (* 2 (- u))) 0))
;  (not (<= (- (to_real (to_int (* (- 2) (- u)))) (* (- 2) (- u))) 0))
; ))

; :toIntHigh (each disjunct for one of the four cases)
; (assert (or
;  (<= (+ (- 1 u) (to_real (to_int u))) 0)
;  (<= (+ (- 1 (- u)) (to_real (to_int (- u)))) 0)
;  (<= (+ (- 1 (* 2 (- u))) (to_real (to_int (* 2 (- u))))) 0)
;  (<= (+ (- 1 (* (- 2) (- u))) (to_real (to_int (* (- 2) (- u))))) 0)
; ))

; :eq
; (assert (and (< x y) (= y x)))

;--- SUBSTITUTION & REWRITE ---;

; general substitution
; (assert (not (or (or (not (not p)) p) (not (not (not p))))))

; :expand (the first disjunct for showing the not required case,
;          the second disjunct for showing the required case)
; (assert (or (<= 0 1 0) (<= 0 1 0 1 0)))

; :expandDef (the first disjunct for the define-fun case,
;             the second disjunct for the :named case)
; (define-fun plus ((x1 Int)) Int (+ 5 x1))
; (assert (or
;  (= (plus 4) 8)
;  (not (= (! p :named foo) (! foo :named bar) bar))
; ))

; :trueNotFalse (each disjunct for one of the sixteen cases)
; (assert (or
;  (= true false) (= false true) (= p true false) (= p false true)
;  (= true false p) (= false true p) (= p true false q) (= p false true q)
;  (= true p false) (= false p true) (= p true q false) (= p false q true)
;  (= true p false q) (= false p true q)
;  (= p true q false r) (= p false q true r)
; ))

; :constDiff (each disjunct for one of the eight cases)
; (assert (or
;  (= 0 1) (= x 0 1) (= 0 x 1) (= 0 1 x)
;  (= x 0 y 1) (= x 0 1 y) (= 0 x 1 y) (= x 0 y 1 z)
; ))

; :eqTrue (each disjunct for one of the four cases)
; (assert (or 
;  (not (= (= true p) p))
;  (not (= (= p true) p))
;  (not (= (= p true p) p))
;  (not (= (= p true p q p q r true q r r true true true q p r) (and p q r)))
; ))

; :eqFalse (each disjunct for one of the four cases)
; (assert (or 
;  (not (= (= false p) (not p)))
;  (not (= (= p false) (not p)))
;  (not (= (= p false p) (not p)))
;  (not (= (= p false p q p q r false q r r false false false q p r) (not (or p q r))))
; ))

; :eqSame (each disjunct for one of the three cases)
; (assert (or (not (= x x)) (not (= x x x)) (not (= x x x x))))

; :eqSimp
; (assert (not (= (= x y x) (= x y))))

; :eqBinary
; (assert (and (= x y z) (distinct x y)))

; :distinctBool (each disjunct for one of the two cases)
; (assert (or (distinct p q r) (distinct p q r s)))

; :distinctSame (each disjunct for one of the possible cases,
;                but currently the translation is the same)
; (assert (or (distinct 0 0) (distinct 0 0 1)))

; :distinctNeg (each 'distinct' term for one of the four cases)
; (assert (not (=
;  (distinct true false) (distinct false true)
;  (distinct p (not p)) (distinct (not p) p)
; )))

; :distinctTrue (each 'distinct' term for one of the two cases)
; (assert (not (= (distinct true p) (distinct p true))))

; :distinctFalse (each 'distinct' term for one of the two cases)
; (assert (not (= (distinct false p) (distinct p false))))

; :distinctBinary (each disjunct for one of the four cases)
; (assert (or
;  (not (= (distinct p q) (= p (not q))))
;  (not (= (distinct (not p) q) (= (not (not p)) q)))
;  (and (distinct x y) (= x y))
;  (not (= (distinct x y z) (not (or (= x y) (= y z) (= x z)))))
; ))

; :notSimp (each disjunct for one of the three cases)
; (assert (or (not true) (not (not false)) (= (not p) (not (not p)))))

; :orSimp (each disjunct for one of the two cases)
; (assert (or
;  (not (= (or false false) false))
;  (not (= (or false p q r false r q (or p q) q r p) (or p q r)))
; ))

; :orTaut (each disjunct for one of the nine cases (two not really considered))
; (assert (or
;  (not (= (or true p) true)) (not (= (or p true) true))
;  (not (= (or p true p) true))
;  (not (= (or (not p) p) true)) (not (= (or (not p) q p) true))
;  (not (= (or (not p) p q) true))
;  (not (= (or p (not p)) true)) (not (= (or p q (not p)) true))
;  (not (= (or p (not p) q) true))
; ))

; :iteTrue
; (assert (not (= (ite true t e) t)))

; :iteFalse
; (assert (not (= (ite false t e) e)))

; :iteSame
; (assert (not (= (ite c p p) p)))

; :iteBool1 & :iteBool2
; (assert (= (ite c true false) (ite c false true)))

; :iteBool3 & :iteBool5
; (assert (= (ite c true c) (ite c (not c) true)))

; :iteBool4 & :iteBool6
; (assert (not (= (ite c false c) (ite c (not c) false))))

; :andToOr
; (assert (and true false))

; :xorToDistinct
; (assert (not (= (xor p q) (distinct p q))))

; :impToOr (each disjunct for one of the two cases)
; (assert (or
;  (not (= (=> p q) (or q (not p))))
;  (not (= (=> p q r) (or r (not p) (not q))))
; ))

; :strip
; (assert (! (or (! false :named foo) false) :named bar))

; :canonicalSum
; (assert (= (+ 0 1) 0))

; :leqToLeq0 & :ltToLeq0
; (assert (= (<= x y) (< y x)))

; :geqToLeq0 & :gtToLeq0
; (assert (= (>= x y) (> y x)))

; :leqTrue
; (assert (not (<= (- 1) 0)))

; :leqFalse
; (assert (<= 1 0))

; :desugar (The first conjunct shows the conversion of constants, the second
;           conjunct shows the conversion of variables.
;           The first case also shows the hard part in Isabelle.)
; (assert (and (not (< 0 1 2 3.0 4.00)) (= x z y)))

; :divisible (each disjunct for one of the four cases)
; (assert (or
;  (not ((_ divisible 1) 2))
;  (not ((_ divisible 2) 4))
;  ((_ divisible 2) 3)
;  (not (= ((_ divisible 2) x) (= x (* 2 (div x 2)))))
; ))

; :modulo
; (assert (not (= (mod x 2) (- x (* 2 (div x 2))))))

; :modulo1
; (assert (= (mod 2 1) 1))

; :modulo-1
; (assert (= (mod 2 (- 1)) 1))

; :moduloConst
; (assert (= (mod 3 2) 0))

; :div1
; (assert (= (div 2 1) 0))

; :div-1 (each disjunct for one of the four cases)
; (assert (or
;  (not (= (div x (- 1)) (- x)))
;  (not (= (div (- x) (- 1)) x))
;  (not (= (div (* 2 x) (- 1)) (* (- 2) x)))
;  (not (= (div (* (- 2) x) (- 1)) (* 2 x)))
; ))

; :divConst
; (assert (= (div 3 2) 0))

; :toInt
; (assert (not (= (to_int 1.5) 1)))

; toReal
; (assert (distinct 1 (to_real 1)))

; :flatten
; (assert (not (= (or (or (or p q) r) s) (or p q r s))))

;--- SPLIT ---;

; :notOr
; (assert (and (not p) (not q) (or (and p q) q)))

; :=+1, :notOr
; (assert (and (= p q) (not (or p (not q)))))

; :=+2, :notOr
; (assert (and (= p q) (not (or (not p) q))))

; :=-1, :notOr
; (assert (and (not (= p q)) (not (or p q))))

; :=-2, :notOr
; (assert (and (not (= p q)) (not (or (not p) (not q)))))

; :ite+1, :notOr
; (assert (and (ite c t e) (not (or (not c) t))))

; :ite+2, :notOr
; (assert (and (ite c t e) (not (or c e))))

; :ite-1, :notOr
; (assert (and (not (ite c t e)) (not (or (not c) (not t)))))

; :ite-2, :notOr
; (assert (and (not (ite c t e)) (not (or c (not e)))))

(check-sat)
(exit)