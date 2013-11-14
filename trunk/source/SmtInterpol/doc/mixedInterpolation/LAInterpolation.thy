theory LAInterpolation imports SMTInterpolation
begin
text {* With "int/real var LinTerm" we denote the linear terms with 
        variables var over int/real *}

datatype ('a, 'b) LinTerm =
   Zero
 | Var 'a
 | Add "('a, 'b) LinTerm" "('a, 'b) LinTerm" 
 | Mul 'b "('a, 'b) LinTerm" 
 | Div "('a, 'b) LinTerm" "'b" 

datatype ('a, 'b) LinAtom =
   Leq "('a, 'b) LinTerm" 'b

class linringdiv = linordered_ring + ring_div

primrec evalt :: "('a \<Rightarrow> 'b::linringdiv) \<Rightarrow> ('a, 'b) LinTerm \<Rightarrow> 'b"
where
   "evalt \<sigma> (Zero) = 0"
 | "evalt \<sigma> (Var x) = \<sigma> x"
 | "evalt \<sigma> (Add s t) = (evalt \<sigma> s) + (evalt \<sigma> t)"
 | "evalt \<sigma> (Mul c t) = c * (evalt \<sigma> t)"
 | "evalt \<sigma> (Div t c) = (evalt \<sigma> t) div c"

primrec evala :: "('a \<Rightarrow> 'b::linringdiv) \<Rightarrow> ('a, 'b) LinAtom \<Rightarrow> bool"
where
   "evala \<sigma> (Leq t c)  = (evalt \<sigma> t \<le> c)"

primrec symbt :: "('a, 'b) LinTerm \<Rightarrow> 'a set"
where
  "symbt Zero = {}"
 |"symbt (Var v) = {v}"
 |"symbt (Add s t) = symbt s \<union> symbt t"
 |"symbt (Mul c t) = symbt t"
 |"symbt (Div t c) = symbt t"

primrec symba :: "('a, 'b) LinAtom \<Rightarrow> 'a set"
where
  "symba (Leq t c) = symbt t"

lemma coinc_term [simp]:
  "coinc (symbt t) \<sigma> \<sigma>' \<Longrightarrow> evalt \<sigma> t = evalt \<sigma>' t"
  by (induct t, auto simp add:coinc_def)

lemma coinc_atom [simp]:
  "coinc (symba a) \<sigma> \<sigma>' \<Longrightarrow> evala \<sigma> a = evala \<sigma>' a"
  by (induct a, auto)

definition type
  where "type x = UNIV"

interpretation LA : atom "evala" "symba" "type"
proof 
  fix f \<sigma> \<sigma>'
  assume "(\<forall> x \<in> symba (f::('a, 'b::linringdiv) LinAtom). 
                       (\<sigma>::('a \<Rightarrow> 'b::linringdiv)) x = \<sigma>' x)"
  hence "coinc (symba f) \<sigma> \<sigma>'" by auto
  thus "evala \<sigma> f = evala \<sigma>' f" by simp
qed

datatype 'b Vars = 
  Flat nat
  | AuxPos "(nat,'b) LinAtom"
  | AuxNeg "(nat,'b) LinAtom"

locale LAinterpolation =
  fixes A :: "(('b::linringdiv) Vars,'b) LinAtom Formula"
  fixes B :: "(('b::linringdiv) Vars,'b) LinAtom Formula"
  assumes flatA: "LA.symbf A \<subseteq> range Flat"
  assumes flatB: "LA.symbf B \<subseteq> range Flat"

primrec filtert :: "('a, 'b::linringdiv) LinTerm \<Rightarrow> 'a set  \<Rightarrow> ('a,'b::linringdiv) LinTerm"
  where "filtert Zero X = Zero"
  |     "filtert (Var x) X = (if x \<in> X then Var x else Zero)"
  |     "filtert (Add s t) X = Add (filtert s X) (filtert t X)"
  |     "filtert (Mul c t) X = Mul c (filtert t X)"
  |     "filtert (Div t c) X = Div (filtert t X) c"

lemma filtertsymb: "symbt (filtert t X) = (symbt t \<inter> X)"
  by (induct t, auto)

fun flatten :: "('b::linringdiv Vars, 'b) LinTerm \<Rightarrow> (nat, 'b) LinTerm"
  where "flatten Zero = Zero"
  |     "flatten (Var (Flat x)) = Var x"
  |     "flatten (Var (AuxPos l)) = Zero"
  |     "flatten (Var (AuxNeg l)) = Zero"
  |     "flatten (Add s t) = Add (flatten s) (flatten t)"
  |     "flatten (Mul c t) = Mul c (flatten t)"
  |     "flatten (Div t c) = Div (flatten t) c"

fun unflatten :: "(nat, 'b) LinTerm \<Rightarrow> ('b::linringdiv Vars, 'b) LinTerm"
  where "unflatten Zero = Zero"
  |     "unflatten (Var x) = Var (Flat x)"
  |     "unflatten (Add s t) = Add (unflatten s) (unflatten t)"
  |     "unflatten (Mul c t) = Mul c (unflatten t)"
  |     "unflatten (Div t c) = Div (unflatten t) c"

lemma flattenunflatten[simp]: "flatten (unflatten t) = t"
  by (induct t, auto)

lemma unflattenflatten[simp]: 
  "symbt t \<subseteq> range Flat \<Longrightarrow> unflatten (flatten t) = t"
  by (induct t rule:flatten.induct, auto)

context LAinterpolation
begin

  definition ABLinVars
  where "ABLinVars \<equiv> LA.symbf A \<union> LA.symbf B"

  definition cleanlit :: "(('b::linringdiv) Vars,'b) LinAtom Literal \<Rightarrow> bool"
    where
    "cleanlit l \<equiv> LA.symbl l \<subseteq> ABLinVars"

  definition ismixed :: "('b::linringdiv) Vars set \<Rightarrow> bool"
    where
    "ismixed vars \<equiv> (vars \<subseteq> ABLinVars) & 
                    \<not>(vars \<subseteq> LA.symbf A) & \<not>(vars \<subseteq> LA.symbf B)"

  fun auxvars :: "('b::linringdiv Vars, 'b) LinAtom Literal \<Rightarrow> 'b Vars list"
    where "auxvars (Neg (Leq t c)) =
         (if ismixed (symbt t) then [ AuxNeg (Leq (flatten t) c) ] else [])"
    |     "auxvars (Pos (Leq t c)) =
         (if ismixed (symbt t) then [ AuxPos (Leq (flatten t) c) ] else [])"
    |     "auxvars Bot = []"
    |     "auxvars Top = []"

  fun  
    projA  :: "('b::linringdiv Vars, 'b) LinAtom Literal \<Rightarrow>
               ('b Vars, 'b) LinAtom Formula"
    where "projA (Pos (Leq t c)) = Literal
             (if symbt t \<subseteq> LA.symbf A then Neg (Leq t c)
              else if ismixed (symbt t) then 
                Pos (Leq (Add (Mul -1 (filtert t (LA.symbf A))) 
                              (Var (AuxPos (Leq (flatten t) c)))) 0)
              else Top)"
    |     "projA (Neg (Leq t c)) = Literal
             (if symbt t \<subseteq> LA.symbf A then Pos (Leq t c)
              else if ismixed (symbt t) then 
                Pos (Leq (Add (filtert t (LA.symbf A)) 
                              (Mul -1 (Var (AuxNeg (Leq (flatten t) c))))) 0)
              else Top)"
    |     "projA Bot = Literal Bot"
    |     "projA Top = Literal Top"


  fun  
    projB  :: "('b::linringdiv Vars, 'b) LinAtom Literal \<Rightarrow>
               ('b Vars, 'b) LinAtom Formula"
    where "projB (Pos (Leq t c)) = Literal
             (if symbt t \<subseteq> LA.symbf B then Neg (Leq t c)
              else if ismixed (symbt t) then 
                Pos (Leq (Add (Mul -1 (filtert t (LA.symbf B - LA.symbf A))) 
                              (Mul -1 (Var (AuxPos (Leq (flatten t) c))))) (- c))
              else Top)"
    |     "projB (Neg (Leq t c)) = Literal
             (if symbt t \<subseteq> LA.symbf B then Pos (Leq t c)
              else if ismixed (symbt t) then 
                Pos (Leq (Add (filtert t (LA.symbf B - LA.symbf A)) 
                              (Var (AuxNeg (Leq (flatten t) c)))) c)
              else Top)"
    |     "projB Bot = Literal Bot"
    |     "projB Top = Literal Top"

  lemma filterABadd: "symbt t \<subseteq> LA.symbf A \<union> LA.symbf B \<Longrightarrow> 
    evalt \<sigma> t = evalt \<sigma> (filtert t (LA.symbf A)) + 
    evalt \<sigma> (filtert t (LA.symbf B - LA.symbf A))"
  proof (induct t, auto simp add: ismixed_def)

  fun auxlit :: "'b Vars \<Rightarrow> ('b::linringdiv Vars, 'b) LinAtom Literal"
    where "auxlit (AuxNeg (Leq t c)) = Neg (Leq (unflatten t) c)"
    |     "auxlit (AuxPos (Leq t c)) = Pos (Leq (unflatten t) c)"
  
  lemma auxlitinv: "\<lbrakk> cleanlit ell; aux \<in> set (auxvars ell) \<rbrakk> \<Longrightarrow> ell = auxlit aux"
  proof -
    from flatA flatB have rng: "ABLinVars \<subseteq> range Flat"
      by (auto simp add: ABLinVars_def)
    assume "cleanlit ell"
    with rng have rngell: "LA.symbl ell \<subseteq> range Flat" 
      by (auto simp add: cleanlit_def)
    assume "aux \<in> set (auxvars ell)"
    with rngell show "ell = auxlit aux"
      by (induct ell rule: auxvars.induct, auto)
  qed

end


sublocale LAinterpolation < mixedinterpolation "evala" "symba" "type" "A" "B"
                                   "cleanlit" "auxvars" "projA" "projB"
proof
  show "\<forall> l \<in> (LA.lits A \<union> LA.lits B). cleanlit l"
  proof (auto)
    fix l
    assume "l \<in> LA.lits A"
    hence "LA.symbl l \<subseteq> LA.symbf A" by (induct A, auto)
    thus "cleanlit l" 
      by (induct, induct, auto simp add:cleanlit_def ABLinVars_def)
  next
    fix l
    assume "l \<in> LA.lits B"
    hence "LA.symbl l \<subseteq> LA.symbf B" by (induct B, auto)
    thus "cleanlit l" 
      by (induct, induct, auto simp add:cleanlit_def ABLinVars_def)
  qed
next
  fix ell
  show "LA.symbf (projA ell) \<subseteq> LA.symbf A \<union> set (auxvars ell)"
    by (induct ell rule: projA.induct, auto simp add:filtertsymb)
  show "LA.symbf (projB ell) \<subseteq> LA.symbf B \<union> set (auxvars ell)"
    by (induct ell rule: projB.induct, auto simp add:filtertsymb)
next
  fix ell
  assume "cleanlit ell"
  with flatA flatB
  show "set (auxvars ell) \<inter> (LA.symbf A \<union> LA.symbf B) = {}"
    by (induct ell rule: auxvars.induct, auto)
next
  fix ell ell'
  assume clean: "cleanlit ell" "cleanlit ell'"
  assume neq: "ell \<noteq> ell'"
  show "set (auxvars ell) \<inter> set (auxvars ell') = {}"
  proof auto
    fix x
    assume "x \<in> set (auxvars ell)" "x \<in> set (auxvars ell')"
    with clean have "ell = auxlit x" "ell' = auxlit x" 
      by (auto simp only:auxlitinv)
    hence "ell = ell'" by simp
    with neq show "False"..
  qed
next
  fix ell
  assume "cleanlit ell"
  show "LA.consequence {And (projA ell) (projB ell)}
    (Literal (Not ell))"
  proof (induct ell rule: projA.induct, auto)
    fix \<sigma>
    assume "\<sigma> (filtertLA.evalf \<sigma> (projA ell)"
    assume "LA.evalf \<sigma> (projB ell)"
    assume "LA.evalf \<sigma> ell"
  
qed
  


end