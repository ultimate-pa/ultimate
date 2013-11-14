theory UFInterpolation imports SMTInterpolation
begin

text {* Equality reasoning *}

datatype 'b UValues = 
   Bool "bool" 
 | USort 'b
datatype 'd Vars =
   Prop 'd
 | UVar 'd

primrec type
where
   "type (Prop n) = range Bool"
 | "type (UVar n) = range USort"

datatype 'd EqAtom =
   PropAtom 'd
 | Eq 'd 'd

lemma uflit_induct:
 "\<lbrakk> \<And> p q. P (Pos (Eq p q));
    \<And> p q. P (Neg (Eq p q));
    \<And> p. P (Pos (PropAtom p));
    \<And> p. P (Neg (PropAtom p)); P Bot; P Top\<rbrakk> \<Longrightarrow> P ell"
proof (induct ell, auto)
  fix atom
  assume "\<And> p q. P (Pos (Eq p q))" "\<And> p. P (Pos (PropAtom p))"
  thus "P (Pos atom)" by (induct atom, auto)
next
  fix atom
  assume "\<And> p q. P (Neg (Eq p q))" "\<And> p. P (Neg (PropAtom p))"
  thus "P (Neg atom)" by (induct atom, auto)
qed

primrec evala
where
   "evala \<sigma> (PropAtom n) = (\<sigma> (Prop n) = Bool True)"
 | "evala \<sigma> (Eq n1 n2) = (\<sigma> (UVar n1) = \<sigma> (UVar n2))"

primrec symba
where
   "symba (PropAtom n) = { Prop n }"
 | "symba (Eq n1 n2) = { UVar n1, UVar n2 }"

interpretation UF : atom "evala" "symba" "type"
proof
  fix f \<sigma> \<sigma>'
  show "\<forall> x \<in> symba f. \<sigma> x = \<sigma>' x
     \<Longrightarrow> evala \<sigma> f = evala \<sigma>' f" by (induct f, auto)
qed

datatype AllVars =
   Flat nat
 | Aux  nat nat
 | Aux2 nat nat

locale UFinterpolation =
  fixes A :: "AllVars EqAtom Formula"
  fixes B :: "AllVars EqAtom Formula"
  assumes flatA: "(UF.symbf A) \<subseteq> (Prop`(range Flat) \<union> UVar`(range Flat))"
  assumes flatB: "(UF.symbf B) \<subseteq> (Prop`(range Flat) \<union> UVar`(range Flat))"

context UFinterpolation
begin

lemma flatA_elim [elim]:
  "\<lbrakk> x \<in> UF.symbf A; x \<in> Prop`(range Flat) \<Longrightarrow> P; x \<in> UVar`(range Flat) \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
proof -
  assume "x \<in> UF.symbf A" also note flatA finally
  show "\<lbrakk> x \<in> Prop`(range Flat) \<Longrightarrow> P; x \<in> UVar`(range Flat) \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
    by blast
qed
  
lemma flatB_elim [elim]:
  "\<lbrakk> x \<in> UF.symbf B; x \<in> Prop`(range Flat) \<Longrightarrow> P; x \<in> UVar`(range Flat) \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
proof -
  assume "x \<in> UF.symbf B" also note flatB finally
  show "\<lbrakk> x \<in> Prop`(range Flat) \<Longrightarrow> P; x \<in> UVar`(range Flat) \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
    by blast
qed

lemma flat_simp [simp]: 
  "\<not> UVar (Aux p q) \<in> UF.symbf A"
  "\<not> Prop (Aux p q) \<in> UF.symbf A"
  "\<not> UVar (Aux p q) \<in> UF.symbf B"
  "\<not> Prop (Aux p q) \<in> UF.symbf B"
  by auto

definition AVars :: "nat set"
where
  "AVars \<equiv> {v. UVar (Flat v) \<in> UF.symbf A }"

definition BVars :: "nat set"
where
  "BVars \<equiv> {v. UVar (Flat v) \<in> UF.symbf B }"

definition ABVars :: "nat set"
where
  "ABVars \<equiv> (AVars \<union> BVars)"

lemma avars_simp [simp]: "(UVar x \<in> UF.symbf A) = (x \<in> Flat`AVars)"
  by (induct x, auto simp add:AVars_def)
lemma bvars_simp [simp]: "(UVar x \<in> UF.symbf B) = (x \<in> Flat`BVars)"
  by (induct x, auto simp add:BVars_def)
lemma abvars_simp [simp]: 
  "UVar x \<in> UF.symbf A \<Longrightarrow> x \<in> Flat`ABVars"
  "UVar x \<in> UF.symbf B \<Longrightarrow> x \<in> Flat`ABVars"
  by (induct x, auto simp add:ABVars_def)

definition ABPropvars :: "nat set"
where
  "ABPropvars \<equiv> {v. Prop (Flat v) \<in> UF.symbf A | Prop (Flat v) \<in> UF.symbf B }"

lemma abpropvars_simp [simp]: 
  "Prop x \<in> UF.symbf A \<Longrightarrow> x \<in> Flat`ABPropvars"
  "Prop x \<in> UF.symbf B \<Longrightarrow> x \<in> Flat`ABPropvars"
  by (induct x, auto simp add:ABPropvars_def)

lemma aballvars: 
  "x \<in> UF.symbf A \<Longrightarrow> x \<in> UVar`Flat`ABVars \<or> x \<in> Prop`Flat`ABPropvars"
  "x \<in> UF.symbf B \<Longrightarrow> x \<in> UVar`Flat`ABVars \<or> x \<in> Prop`Flat`ABPropvars"
  by (induct x, auto)

definition cleanlit :: "AllVars EqAtom Literal \<Rightarrow> bool"
where
  "cleanlit l \<equiv> UF.symbl l \<subseteq> (Prop`(Flat`ABPropvars) \<union> UVar`(Flat`ABVars))"

lemma cleanlit_induct:
  "\<lbrakk> cleanlit ell;
     \<And> p q. \<lbrakk> p \<in> ABVars; q \<in> ABVars \<rbrakk> \<Longrightarrow> P (Pos (Eq (Flat p) (Flat q)));
     \<And> p q. \<lbrakk> p \<in> ABVars; q \<in> ABVars \<rbrakk> \<Longrightarrow> P (Neg (Eq (Flat p) (Flat q)));
     \<And> p. \<lbrakk> p \<in> ABPropvars \<rbrakk> \<Longrightarrow> P (Pos (PropAtom (Flat p)));
     \<And> p. \<lbrakk> p \<in> ABPropvars \<rbrakk> \<Longrightarrow> P (Neg (PropAtom (Flat p)));
     P Bot; P Top \<rbrakk> \<Longrightarrow> P ell"
  by (induct ell rule: uflit_induct, unfold cleanlit_def, auto)

definition ismixed :: "nat \<Rightarrow> nat \<Rightarrow> bool"
where
   "ismixed p q \<equiv> ({p,q} \<subseteq> ABVars) & 
           \<not>({p,q} \<subseteq> AVars) & \<not>({p,q} \<subseteq> BVars)"

fun auxvars :: "AllVars EqAtom Literal \<Rightarrow> AllVars Vars list"
where
   "auxvars (Neg (Eq (Flat p) (Flat q))) = 
        (if ismixed p q then [UVar (Aux2 p q)] else [])"
 | "auxvars (Pos (Eq (Flat p) (Flat q))) = 
        (if ismixed p q then [Prop (Aux p q), UVar (Aux p q)] else [])"
 | "auxvars _ = []"

definition select
where
   "select X p q \<equiv> (if p \<in> X then p else q)"

lemma select_simpA [simp]: 
  "ismixed p q \<Longrightarrow> select AVars p q \<in> AVars"
  by (auto simp add: select_def ismixed_def ABVars_def) 
lemma select_simpB [simp]: 
  "ismixed p q \<Longrightarrow> select BVars p q \<in> BVars"
  by (auto simp add: select_def ismixed_def ABVars_def) 

lemma select_simpAB1: 
  "\<lbrakk> ismixed p q; P (select AVars p q); P (select BVars p q) \<rbrakk> \<Longrightarrow> P p"
  by (auto simp add: select_def ismixed_def ABVars_def)
lemma select_simpAB2: 
  "\<lbrakk> ismixed p q; P (select AVars p q); P (select BVars p q) \<rbrakk> \<Longrightarrow> P q"
  by (auto simp add: select_def ismixed_def ABVars_def)

fun projEQ
where
   "projEQ X p q = 
    Literal (if ismixed p q then Pos (Eq (Flat (select X p q)) (Aux2 p q))
             else if {p,q} \<subseteq> X then Pos (Eq (Flat p) (Flat q))
             else Top)"

fun projNEQ
where
   "projNEQ X posneg negpos p q = 
    (if ismixed p q then
         Or (And (Literal (posneg (PropAtom (Aux p q))))
                 (Literal (Pos (Eq (Flat (select X p q)) (Aux p q)))))
            (And (Literal (negpos (PropAtom (Aux p q))))
                 (Literal (Neg (Eq (Flat (select X p q)) (Aux p q)))))
     else if {p,q} \<subseteq> X then Literal (Neg (Eq (Flat p) (Flat q)))
     else Literal Top)"
  
fun  
   projA  :: "AllVars EqAtom Literal \<Rightarrow> AllVars EqAtom Formula"
where
   "projA (Neg (Eq (Flat p) (Flat q))) = projEQ AVars p q"
 | "projA (Pos (Eq (Flat p) (Flat q))) = projNEQ AVars Pos Neg p q"
 | "projA l = (if UF.symbl l \<subseteq> UF.symbf A then (Literal (Not l)) else (Literal Top))"

fun
   projB  :: "AllVars EqAtom Literal \<Rightarrow> AllVars EqAtom Formula"
where
   "projB (Neg (Eq (Flat p) (Flat q))) = projEQ BVars p q"
 | "projB (Pos (Eq (Flat p) (Flat q))) = projNEQ BVars Neg Pos p q"
 | "projB l = (if UF.symbl l \<subseteq> UF.symbf B then (Literal (Not l)) else (Literal Top))"

end

context atom
begin
lemma lits_symb:
  "l : lits F \<Longrightarrow> symbl l \<subseteq> symbf F"
  by (induct F, auto)

lemma symblf [simp]: "\<lbrakk> l \<in> lits F; x \<in> symbl l \<rbrakk> \<Longrightarrow> x \<in> symbf F"
  by (induct F, auto)
end

sublocale UFinterpolation < mixedinterpolation "evala" "symba" "type" "A" "B"
                                   "cleanlit" "auxvars" "projA" "projB"
proof
  show "\<forall> l \<in> (UF.lits A \<union> UF.lits B). cleanlit l"
  proof (auto, unfold cleanlit_def)
    fix l assume l: "l \<in> UF.lits A"
    hence "UF.symbl l \<subseteq> UF.symbf A" by auto
    also from aballvars
    have "UF.symbf A \<subseteq> Prop`Flat`ABPropvars \<union> UVar`Flat`ABVars" by auto
    finally show "UF.symbl l \<subseteq> Prop`Flat`ABPropvars \<union> UVar`Flat`ABVars" .
  next
    fix l assume "l \<in> UF.lits B"
    hence "UF.symbl l \<subseteq> UF.symbf B" by auto
    also from aballvars
    have "UF.symbf B \<subseteq> Prop`Flat`ABPropvars \<union> UVar`Flat`ABVars" by auto
    finally show "UF.symbl l \<subseteq> Prop`Flat`ABPropvars \<union> UVar`Flat`ABVars" .
  qed
next
  fix ell show "UF.symbf (projA ell) \<subseteq> UF.symbf A \<union> set (auxvars ell)"
    (is "?symbcond ell")
    by (induct ell rule: projA.induct, auto)
next
  fix ell show "UF.symbf (projB ell) \<subseteq> UF.symbf B \<union> set (auxvars ell)"
    (is "?symbcond ell")
    by (induct ell rule: projB.induct, auto)
next
  fix ell
  show "cleanlit ell \<Longrightarrow> set (auxvars ell) \<inter> (UF.symbf A \<union> UF.symbf B) = {}"
    by (induct ell rule: auxvars.induct, unfold cleanlit_def, auto)
next
  fix ell assume "cleanlit ell" thus "cleanlit ell".
next
  fix ell ell'
  assume "cleanlit ell" "cleanlit ell'" "ell \<noteq> ell'"
  thus "set (auxvars ell) \<inter> set (auxvars ell') = {}"
  proof (induct ell rule: cleanlit_induct, auto)
    fix p q 
    assume "cleanlit ell'" "Neg (Eq (Flat p) (Flat q)) \<noteq> ell'"
      "UVar (Aux2 p q) \<in> set (auxvars ell')"
    thus "False"
      by (induct ell' rule: cleanlit_induct, auto)
  next
    fix p q 
    assume "cleanlit ell'" "Pos (Eq (Flat p) (Flat q)) \<noteq> ell'"
      "UVar (Aux p q) \<in> set (auxvars ell')"
    thus "False"
      by (induct ell' rule: cleanlit_induct, auto)
  next
    fix p q 
    assume "cleanlit ell'" "Pos (Eq (Flat p) (Flat q)) \<noteq> ell'"
      "Prop (Aux p q) \<in> set (auxvars ell')"
    thus "False"
      by (induct ell' rule: cleanlit_induct, auto)
  qed
next
  fix ell
  assume clean:"cleanlit ell"
  {
    fix \<sigma>
    assume wt: "UF.welltyped (\<sigma> :: AllVars Vars \<Rightarrow> 'd UValues)"
    have "\<lbrakk> UF.evalf \<sigma> (projA ell); UF.evalf \<sigma> (projB ell) \<rbrakk> \<Longrightarrow> UF.evall \<sigma> (Not ell)"
    proof (induct ell rule: cleanlit_induct)
      from clean show "cleanlit ell" .
    next
      fix p q
      assume abvars: "p \<in> ABVars" "q \<in> ABVars"
      assume evalA: "UF.evalf \<sigma> (projA (Pos (Eq (Flat p) (Flat q))))"
      assume evalB: "UF.evalf \<sigma> (projB (Pos (Eq (Flat p) (Flat q))))"
      from abvars evalA evalB show "UF.evall \<sigma> (Not (Pos (Eq (Flat p) (Flat q))))"
        by (cases "ismixed p q", auto simp add: ismixed_def ABVars_def select_def)
    next
      fix p q
      assume abvars: "p \<in> ABVars" "q \<in> ABVars"
      assume evalA: "UF.evalf \<sigma> (projA (Neg (Eq (Flat p) (Flat q))))"
      assume evalB: "UF.evalf \<sigma> (projB (Neg (Eq (Flat p) (Flat q))))"
      from abvars evalA evalB show "UF.evall \<sigma> (Not (Neg (Eq (Flat p) (Flat q))))"
        by (cases "ismixed p q", auto simp add: ismixed_def ABVars_def select_def)
    next
      fix p
      assume abvars: "p \<in> ABPropvars" 
      assume evalA: "UF.evalf \<sigma> (projA (Pos (PropAtom (Flat p))))"
      assume evalB: "UF.evalf \<sigma> (projB (Pos (PropAtom (Flat p))))"
      from abvars evalA evalB show "UF.evall \<sigma> (Not (Pos (PropAtom (Flat p))))"
        by (cases "Prop (Flat p) \<in> symbf A",
          auto simp add: ismixed_def ABPropvars_def)
    next
      fix p
      assume abvars: "p \<in> ABPropvars" 
      assume evalA: "UF.evalf \<sigma> (projA (Neg (PropAtom (Flat p))))"
      assume evalB: "UF.evalf \<sigma> (projB (Neg (PropAtom (Flat p))))"
      from abvars evalA evalB show "UF.evall \<sigma> (Not (Neg (PropAtom (Flat p))))"
        by (cases "Prop (Flat p) \<in> symbf A",
          auto simp add: ismixed_def ABPropvars_def)
    next
    qed auto
  }
  thus "UF.consequence _ {And (projA ell) (projB ell)} (Literal (Not ell))"
    by auto
next
  fix ell \<sigma>
  assume clean: "cleanlit ell"
  assume wt: "UF.welltyped (\<sigma> :: AllVars Vars \<Rightarrow> 'd UValues)"
  assume "UF.evalf \<sigma> (Literal (Not ell))" (is "?whole ell")
  thus "\<exists> \<sigma>'. UF.variant (auxvars ell) \<sigma> \<sigma>' \<and>
              UF.evalf \<sigma>' (And (projA ell) (projB ell))"
    (is "\<exists> \<sigma>'. ?variant ell \<sigma>' \<and> ?parts \<sigma>' ell")
  proof (induct ell rule: cleanlit_induct) 
    from clean show "cleanlit ell".
  next
    fix p
    assume "?whole (Pos (PropAtom p))"
    hence "?parts \<sigma> (Pos (PropAtom p))"
      by auto
    thus "\<exists> \<sigma>'. ?variant (Pos (PropAtom p)) \<sigma>' \<and> ?parts \<sigma>' (Pos (PropAtom p))"
      by auto
  next
    fix p
    assume "?whole (Neg (PropAtom p))"
    hence "?parts \<sigma> (Neg (PropAtom p))"
      by auto
    thus "\<exists> \<sigma>'. ?variant (Neg (PropAtom p)) \<sigma>' \<and> ?parts \<sigma>' (Neg (PropAtom p))"
      by auto
  next
    fix p q
    let "?ell" = "Neg (Eq (Flat p) (Flat q))"
    assume whole: "?whole ?ell"
    show "\<exists> \<sigma>'. ?variant ?ell \<sigma>' \<and> ?parts \<sigma>' ?ell"
    proof (cases "ismixed p q")
      case True
      hence aux: "auxvars ?ell = [ UVar (Aux2 p q)]" by simp
      let "?d" = "\<sigma> (UVar (Flat p))"
      let "?s'" = "\<sigma>(UVar (Aux2 p q) := \<sigma> (UVar (Flat p)))"
      from wt have "?d \<in> type (UVar (Flat p))" 
        by (unfold UF.welltyped_def, blast)
      hence "UF.variant [UVar (Aux2 p q)] \<sigma> ?s'" 
        by auto
      hence var: "?variant ?ell ?s'" by (simp only: aux)
      from whole True have parts: "?parts ?s' ?ell" 
        by (auto simp add:select_def)
      from var parts 
      show "\<exists> \<sigma>'. ?variant ?ell \<sigma>' \<and> ?parts \<sigma>' ?ell" by blast
    next
      case False
      with whole have "?parts \<sigma> ?ell" by auto
      with False show "\<exists> \<sigma>'. ?variant ?ell \<sigma>' \<and> ?parts \<sigma>' ?ell" by auto
    qed
  next
    fix p q
    let "?ell" = "Pos (Eq (Flat p) (Flat q))"
    assume whole: "?whole ?ell"
    show "\<exists> \<sigma>'. ?variant ?ell \<sigma>' \<and> ?parts \<sigma>' ?ell"
    proof (cases "ismixed p q")
      case True
      hence aux: "auxvars ?ell = [ Prop (Aux p q), UVar (Aux p q)]" by simp
      let "?d" = "\<sigma> (UVar (Flat (select AVars p q)))"
      let "?s''" = "\<sigma>(UVar (Aux p q) := \<sigma> (UVar (Flat (select AVars p q))))"
      let "?s'" = "?s''(Prop (Aux p q) := Bool True)"
      from wt have "?d \<in> type (UVar (Flat (select AVars p q)))" 
        by (unfold UF.welltyped_def, blast)
      hence "UF.variant [UVar (Aux p q)] \<sigma> ?s''" 
        by auto
      hence "UF.variant [Prop (Aux p q), UVar (Aux p q)] \<sigma> ?s'" 
        by auto
      hence var: "?variant ?ell ?s'" by (simp only: aux)
      from whole True have parts: "?parts ?s' ?ell" 
        by (auto simp add:ismixed_def ABVars_def select_def)
      from var parts 
      show "\<exists> \<sigma>'. ?variant ?ell \<sigma>' \<and> ?parts \<sigma>' ?ell" by blast
    next
      case False
      with whole have "?parts \<sigma> ?ell" by auto
      with False show "\<exists> \<sigma>'. ?variant ?ell \<sigma>' \<and> ?parts \<sigma>' ?ell" by auto
    qed
  qed auto
qed

lemma [elim]: "\<And> \<sigma>. \<lbrakk> UF.welltyped \<sigma>; \<sigma> (Prop p) \<in> range Bool \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
proof (unfold UF.welltyped_def)
  fix \<sigma> p assume "\<forall>x. \<sigma> x \<in> type x"
  hence "\<sigma> (Prop p) \<in> type (Prop p)" ..
  hence "\<sigma> (Prop p) \<in> range Bool" by simp
  thus "\<lbrakk> \<sigma> (Prop p) \<in> range Bool \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P" by blast
qed
lemma [elim]: "\<And> \<sigma>. \<lbrakk> UF.welltyped \<sigma>; \<sigma> (UVar p) \<in> range USort \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
proof (unfold UF.welltyped_def)
  fix \<sigma> p assume "\<forall>x. \<sigma> x \<in> type x"
  hence "\<sigma> (UVar p) \<in> type (UVar p)" ..
  hence "\<sigma> (UVar p) \<in> range USort" by simp
  thus "\<lbrakk> \<sigma> (UVar p) \<in> range USort \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P" by blast
qed

datatype SWAtom =
   Quote "AllVars EqAtom"
 | EQ nat nat AllVars

lemma swlit_cases:
  "\<lbrakk> P Bot; P Top; 
    \<And> a. P  (Pos (Quote a)); \<And> a. P (Neg (Quote a)); 
    \<And> p q s. P (Pos (EQ p q s)); \<And> p q s. P (Neg (EQ p q s)) \<rbrakk> \<Longrightarrow> P lit"
proof (induct "lit", auto)
  fix atom 
  assume "\<And> a. P ( (Pos (Quote a)))" "\<And> p q s. P ( (Pos (EQ p q s)))" 
  thus "P (Pos atom)" by (induct "atom", auto)
  assume "\<And> a. P ( (Neg (Quote a)))" "\<And> p q s. P ( (Neg (EQ p q s)))"
  thus "P (Neg atom)" by (induct "atom", auto)
qed

lemma swlitfull_cases:
  "\<lbrakk> P Bot; P Top; 
    \<And> d1 d2. P  (Pos (Quote (Eq d1 d2))); \<And> d1 d2. P (Neg (Quote (Eq d1 d2))); 
    \<And> pr. P  (Pos (Quote (PropAtom pr))); \<And> pr. P (Neg (Quote (PropAtom pr))); 
    \<And> p q s. P (Pos (EQ p q s)); \<And> p q s. P (Neg (EQ p q s)) \<rbrakk> \<Longrightarrow> P lit"
proof (induct "lit" rule: swlit_cases, auto)
  fix atom 
  assume "\<And> d1 d2. P  (Pos (Quote (Eq d1 d2)))"
         "\<And> pr. P  (Pos (Quote (PropAtom pr)))"
  thus "P (Pos (Quote atom))" by (cases atom, auto)
  assume "\<And> d1 d2. P (Neg (Quote (Eq d1 d2)))"
         "\<And> pr. P (Neg (Quote (PropAtom pr)))"
  thus "P (Neg (Quote atom))" by (cases atom, auto)
qed

lemma swformula_induct:
  "\<lbrakk> P (Literal Bot); P (Literal Top); 
    \<And> a. P (Literal (Pos (Quote a))); \<And> a. P (Literal (Neg (Quote a))); 
    \<And> p q s. P (Literal (Pos (EQ p q s))); \<And> p q s. P (Literal (Neg (EQ p q s)));
    \<And> F1 F2. \<lbrakk> P F1; P F2 \<rbrakk> \<Longrightarrow> P (And F1 F2);
    \<And> F1 F2. \<lbrakk> P F1; P F2 \<rbrakk> \<Longrightarrow> P (Or F1 F2) \<rbrakk> \<Longrightarrow> P F"
  by (induct "F", auto elim: swlit_cases)
    
fun swsymbl
where
    "swsymbl (Pos (Quote (Eq d1 d2))) = { UVar d1, UVar d2 }"
  | "swsymbl (Neg (Quote (Eq d1 d2))) = { UVar d1, UVar d2 }"
  | "swsymbl (Pos (Quote (PropAtom d))) = { Prop d }"
  | "swsymbl (Neg (Quote (PropAtom d))) = { Prop d }"
  | "swsymbl (Pos (EQ p q s)) = { Prop (Aux p q), UVar (Aux p q), UVar s }"
  | "swsymbl (Neg (EQ p q s)) = {}"
  | "swsymbl Bot = {}"
  | "swsymbl Top = {}"

fun strong :: "SWAtom Literal \<Rightarrow> AllVars EqAtom Formula"
where
   "strong (Pos (Quote a)) = Literal (Pos a)"
 | "strong (Neg (Quote a)) = Literal (Neg a)"
 | "strong (Pos (EQ p q s)) = 
       Or (And (Literal (Pos (PropAtom (Aux p q)))) 
               (Literal (Pos (Eq (Aux p q) s))))
          (And (Literal (Neg (PropAtom (Aux p q))))
               (Literal (Neg (Eq (Aux p q) s))))" 
 | "strong (Neg (EQ p q s)) = Literal Bot"
 | "strong Top = Literal Top"
 | "strong Bot = Literal Bot"

lemma swsymbl_symbstrong:
   "swsymbl lit = UF.symbf (strong lit)"
  by (induct lit rule: swlitfull_cases, auto)


context UFinterpolation
begin

fun flatAux2
where
    "flatAux2 (Flat p) = (UVar (Flat p) \<in> symbf A \<inter> symbf B)"
  | "flatAux2 (Aux2 p q) = True"
  | "flatAux2 _ = False"

fun wfpat :: "SWAtom Literal \<Rightarrow> bool"
where
   "wfpat (Pos (Quote (PropAtom p))) = (Prop p \<in> symbf A \<inter> symbf B)"
 | "wfpat (Neg (Quote (PropAtom p))) = (Prop p \<in> symbf A \<inter> symbf B)"
 | "wfpat (Pos (Quote (Eq d1 d2))) = (flatAux2 d1 \<and> flatAux2 d2)"
 | "wfpat (Neg (Quote (Eq d1 d2))) = (flatAux2 d1 \<and> flatAux2 d2)"
 | "wfpat (Pos (EQ p q s)) = flatAux2 s"
 | "wfpat (Neg (EQ p q s)) = False"
 | "wfpat Top = True"
 | "wfpat Bot = True"

fun wfpatf :: "SWAtom Formula \<Rightarrow> bool"
where
   "wfpatf (Literal l) = wfpat l"
 | "wfpatf (And F G) = (wfpatf F \<and> wfpatf G)"
 | "wfpatf (Or F G) = (wfpatf F \<and> wfpatf G)"

lemma wfpat_subst: 
  "\<lbrakk> wfpatf F; \<And> G. wfpat G \<Longrightarrow> wfpatf (s G) \<rbrakk> \<Longrightarrow> wfpatf (subst s F)"
  by (induct F, auto)
end

fun 
  quote :: "AllVars EqAtom Literal \<Rightarrow> SWAtom Literal"
where
   "quote (Pos a) = Pos (Quote a)"
 | "quote (Neg a) = Neg (Quote a)"
 | "quote Bot = Bot"
 | "quote Top = Top"

lemma allvars_induct:
  "\<lbrakk> \<And> p q. P (UVar (Aux p q)); \<And> p q. P (Prop (Aux p q));
     \<And> p q. P (UVar (Aux2 p q)); \<And> p q. P (Prop (Aux2 p q));
     \<And> p. P (UVar (Flat p)); \<And> p. P (Prop (Flat p))\<rbrakk> \<Longrightarrow> P var"
proof (induct "var")
  fix x assume "\<And> p q. P (UVar (Aux p q))" "\<And> p q. P (UVar (Aux2 p q))"
         "\<And> p. P (UVar (Flat p))"
  thus "P (UVar x)" by (induct x, auto)
next
  fix x assume "\<And> p q. P (Prop (Aux p q))" "\<And> p q. P (Prop (Aux2 p q))"
         "\<And> p. P (Prop (Flat p))"
  thus "P (Prop x)" by (induct x, auto)
qed

sublocale UFinterpolation < strongweak "evala" "symba" "type" "A" "B"
  "cleanlit" "auxvars" "projA" "projB" 
  "wfpat" "strong" "strong" "quote"
proof
  fix c show "strong (quote c) = Literal c"
    by (induct c, auto)
next
  fix ell 
  assume "cleanlit ell" "symbl ell \<subseteq> symbf A \<inter> symbf B"
  thus "wfpat (quote ell)"
    by (induct ell rule: cleanlit_induct, auto)
qed auto

fun substv :: "nat \<Rightarrow> nat \<Rightarrow> AllVars \<Rightarrow> AllVars \<Rightarrow> AllVars"
where
  "substv p q s x = (if x = (Aux2 p q) then s else x)"

fun substd
where
   "substd p q s (Pos (EQ p' q' s')) = Pos (EQ p' q' (substv p q s s'))"
 | "substd p q s (Pos (Quote (Eq d1 d2))) = 
                 Pos (Quote (Eq (substv p q s d1) (substv p q s d2)))"
 | "substd p q s (Neg (Quote (Eq d1 d2))) = 
                 Neg (Quote (Eq (substv p q s d1) (substv p q s d2)))"
 | "substd p q s x = x"

fun substI1
where
   "substI1 p q I2 (Pos (EQ p' q' s)) = 
   (if p = p'\<and> q = q' then (subst (Literal o (substd p q s)) I2) 
                      else Literal (Pos (EQ p' q' s)))" 
 | "substI1 p q I2 lit = Literal lit"

lemma substI1_intro:
  "\<lbrakk> lit \<noteq> Pos(EQ p q s) \<Longrightarrow> F (Literal lit);
      \<And> s. lit = Pos(EQ p q s) \<Longrightarrow> F (subst (Literal o (substd p q s)) I2) 
   \<rbrakk> \<Longrightarrow> F (substI1 p q I2 lit)"
  by (cases "(p, q, I2, lit)" rule: substI1.cases, auto) 

fun ufsubst :: "nat \<Rightarrow> nat \<Rightarrow> SWAtom Formula \<Rightarrow> SWAtom Formula \<Rightarrow> SWAtom Formula"
where 
  "ufsubst p q I1 I2 = subst (substI1 p q I2) I1"

context UFinterpolation
begin

fun auxsymb
where
    "auxsymb (Aux2 p q) = {UVar (Aux2 p q)}"
  | "auxsymb _ = {}"

lemma flataux_elim:
  "\<lbrakk> flatAux2 d; \<lbrakk> d \<in> Flat`AVars ; d \<in> Flat`BVars \<rbrakk> \<Longrightarrow> P;
     \<And> p q. d = (Aux2 p q) \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  by (induct d, auto)

lemma auxsymb_aux [simp]: 
  "UVar (Aux p q) \<notin> auxsymb s"
  "Prop (Aux p q) \<notin> auxsymb s"
  by (induct s,auto)

fun auxsymbl
where
    "auxsymbl (Pos (Quote (Eq d1 d2))) = auxsymb d1 \<union> auxsymb d2"
  | "auxsymbl (Neg (Quote (Eq d1 d2))) = auxsymb d1 \<union> auxsymb d2"
  | "auxsymbl (Pos (EQ p q s)) = { Prop (Aux p q), UVar (Aux p q) } \<union> auxsymb s"
  | "auxsymbl _ = {}"

lemma wfpat_symb: 
  "wf C l = (wfpat l \<and> (\<forall> v \<in> auxsymbl l. \<exists> ell \<in> C. v \<in> set (auxvars ell)))"
proof (unfold wf_def)
  fix X
  have "wfpat l \<Longrightarrow> symbf (strong l) - symbf A \<inter> symbf B = auxsymbl l"
    by (induct l rule:swlitfull_cases, auto elim:flataux_elim)
  thus "(wfpat l \<and> (\<forall> a \<in> symbf (strong l) - symbf A \<inter> symbf B. X a))
      = (wfpat l \<and> (\<forall> v \<in> auxsymbl l. X v))"
    by (auto simp only:)
qed

fun auxsymbf
where
   "auxsymbf (Literal l) = auxsymbl l"
 | "auxsymbf (And F G) = auxsymbf F \<union> auxsymbf G"
 | "auxsymbf (Or F G) = auxsymbf F \<union> auxsymbf G"

fun wff
where
    "wff C (Literal l) = wf C l"
  | "wff C (And F G) = (wff C F \<and> wff C G)"
  | "wff C (Or F G) = (wff C F \<and> wff C G)"

lemma wff_allwf: 
  "wff C F = (\<forall> d \<in> lits(F). wf C d)"
  by (induct F, auto)

lemma wfpat_symbf: 
  "wff C F = (wfpatf F \<and> (\<forall> v \<in> auxsymbf F. \<exists> l \<in> C. v \<in> set (auxvars l)))"
  by (induct F, auto simp add: wfpat_symb)

lemma wff_subst:
  "\<lbrakk> wff C1 F;  \<And> d. wf C1 d \<Longrightarrow> wff C (s d) \<rbrakk> \<Longrightarrow> wff C (subst s F)"
  by (induct F, auto)

lemma
  substv_wf [elim]: "\<lbrakk> s \<noteq> Aux2 p q \<rbrakk> \<Longrightarrow> substv p q s v \<noteq> Aux2 p q"
  by (cases v, auto)

lemma wf_subset: "\<lbrakk> wf C2 F \<rbrakk> \<Longrightarrow> wf (C1 \<union> C2) F"
  by (unfold wf_def, auto)

lemma
  wfI1_cases: "\<lbrakk> wf C1 (Pos (EQ p q s));
                 UVar s \<in> symbf A \<inter> symbf B \<Longrightarrow> P;
                 \<And> ps qs. \<lbrakk> s = Aux2 ps qs; ismixed ps qs; 
                             Neg (Eq (Flat ps) (Flat qs)) \<in> C1 \<rbrakk> \<Longrightarrow> P \<rbrakk>
                \<Longrightarrow> P"
proof -
  fix P
  assume imp1: "UVar s \<in> symbf A \<inter> symbf B \<Longrightarrow> P"
  assume imp2: "\<And> ps qs. \<lbrakk> s = Aux2 ps qs; ismixed ps qs; 
                             Neg (Eq (Flat ps) (Flat qs)) \<in> C1 \<rbrakk> \<Longrightarrow> P"
  assume wfc1: "wf C1 (Pos (EQ p q s))"
  have "UVar s \<in> symbf (strong (Pos (EQ p q s)))" by simp
  with wfc1 
  have "UVar s \<in> symbf A \<inter> symbf B \<or> 
        (\<exists> l \<in> C1. UVar s \<in> set (auxvars l))"
    by (unfold wf_def, auto)
  thus "P"
  proof (elim disjE)
    assume "UVar s \<in> symbf A \<inter> symbf B" thus "P" by (rule imp1)
  next
    from wfc1 have aux2: "flatAux2 s" by (unfold wf_def, auto)
    assume "\<exists> l \<in> C1. UVar s \<in> set (auxvars l)"
    then obtain l where l: "l \<in> C1" "UVar s \<in> set (auxvars l)"
      by blast
    with aux2 obtain ps qs where "l = Neg (Eq (Flat ps) (Flat qs))"
      by (induct "l" rule: auxvars.induct, auto)
    with l have
      s: "(s = Aux2 ps qs \<and> ismixed ps qs \<and> Neg (Eq (Flat ps) (Flat qs)) \<in> C1)"
      by simp
    with imp2
    show "P" by auto
  qed
qed


lemma
  wfI2: "\<lbrakk> wf (C2 \<union> { Neg (Eq (Flat p) (Flat q))}) a;
      flatAux2 s;
      (UVar s) \<in> symbf A \<inter> symbf B \<or> (\<exists> ell \<in> C1. UVar s \<in> set (auxvars ell)) \<rbrakk>
      \<Longrightarrow> wf (C1 \<union> C2) (substd p q s a)"
proof -
  assume "wf (C2 \<union> { Neg (Eq (Flat p) (Flat q))}) a"
  hence pat: "wfpat a" and
        c2: "\<forall> x \<in> symbf (strong a) - symbf A \<inter> symbf B. 
           \<exists> ell \<in> C2 \<union> { Neg (Eq (Flat p) (Flat q))}. x\<in> set (auxvars ell)"
    by (unfold wf_def, auto)
  assume "flatAux2 s"
  with pat have pats: "wfpat (substd p q s a)"
    by (induct a rule: wfpat.induct, auto)
  assume c1: "(UVar s) \<in> symbf A \<inter> symbf B 
    \<or> (\<exists> ell \<in> C1. UVar s \<in> set (auxvars ell))"
  have "\<forall> x \<in> symbf (strong (substd p q s a)) - symbf A \<inter> symbf B. 
         \<exists> ell \<in> C1 \<union> C2. x \<in> set (auxvars ell)"
  proof (rule)
    fix x 
    assume asm: "x \<in> symbf (strong (substd p q s a)) - symbf A \<inter> symbf B"
    show "\<exists> ell \<in> C1 \<union> C2. x \<in> set (auxvars ell)"
    proof (cases "x = UVar s")
      case True with asm c1 have "(\<exists> ell \<in> C1. x \<in> set (auxvars ell))"
        by auto
      thus "\<exists> ell \<in> C1 \<union> C2. x \<in> set (auxvars ell)" by blast
    next
      case False with asm
      have "x \<in> symbf (strong a)"
        by (induct a rule: substd.induct, auto)
      with c2 asm
      have "\<exists> ell \<in> C2 \<union> { Neg (Eq (Flat p) (Flat q))}. x \<in> set (auxvars ell)"
        by auto
      then obtain ell where l2: "ell \<in> C2 \<union> { Neg (Eq (Flat p) (Flat q))}" and
        xin: "x \<in> set (auxvars ell)"
        by blast
      moreover
      {
        {
          fix x1 x2 x3
          have "x1 = (if x2 = x1 then x3 else x2) \<Longrightarrow> x1 = x3"
            by (cases "x2 = x1", auto)
        }
        hence ifsimp:
          "\<And> x1 x2 x3. x1 = (if x2 = x1 then x3 else x2) \<Longrightarrow> x1 = x3" .
        assume "ell = Neg (Eq (Flat p) (Flat q))"
        with xin have "x = UVar(Aux2 p q)" by simp
        with asm have "x = UVar s"
          by (induct a rule: substd.induct, auto intro: ifsimp)
        with False have "False" by simp
      }
      ultimately
      show "\<exists> ell \<in> C1 \<union> C2. x \<in> set (auxvars ell)" by blast
    qed
  qed
  with pats show "wf (C1 \<union> C2) (substd p q s a)" 
    by (unfold wf_def, auto)
qed

lemma
  wffI1I2: "\<lbrakk> wff (C1 \<union> { Pos (Eq (Flat p) (Flat q))}) I1;
              wff (C2 \<union> { Neg (Eq (Flat p) (Flat q))}) I2 \<rbrakk>
        \<Longrightarrow> wff (C1 \<union> C2) (ufsubst p q I1 I2)"
proof (simp only: ufsubst.simps, elim wff_subst)
  fix d
  assume I2: "wff (C2 \<union> {Neg (Eq (Flat p) (Flat q))}) I2"
  assume I1: "wf (C1 \<union> {Pos (Eq (Flat p) (Flat q))}) d"
  show  "wff (C1 \<union> C2) (substI1 p q I2 d)"
  proof (cases "\<exists> s. d = Pos (EQ p q s)")
    case True then obtain s where d: "d = Pos (EQ p q s)" by blast
    with I1 have flats: "flatAux2 s" by (unfold wf_def, simp)
    have uvars: "(UVar s) \<in> symbf A \<inter> symbf B
         \<or> (\<exists> ell \<in> C1. UVar s \<in> set (auxvars ell))" (is "?lhs \<or> ?rhs")
    proof (cases s)
      case Flat with flats have "?lhs" by simp
      thus "?lhs \<or> ?rhs" by auto
    next
      case Aux2 with d have "UVar s \<in> auxsymbl d" by (simp)
      with I1 Aux2 have "?rhs" by (auto simp add:wfpat_symb)
      thus "?lhs \<or> ?rhs" by auto
    next
      case Aux with flats have "False" by simp
      thus "?lhs \<or> ?rhs" by auto
    qed
    from I2 have "wff (C1 \<union> C2) (subst (Literal \<circ> substd p q s) I2)"
    proof (elim wff_subst)
      fix d
      assume "wf (C2 \<union> {Neg (Eq (Flat p) (Flat q))}) d"
      with flats uvars
      have "wf (C1 \<union> C2) (substd p q s d)"
        by (elim wfI2, simp)
      thus "wff (C1 \<union> C2) ((Literal \<circ> substd p q s) d)"
        by simp
    qed
    with d show "wff (C1 \<union> C2) (substI1 p q I2 d)"
      by (cases "(p,q,I2,d)" rule: substI1.cases,auto)
  next
    case False
    hence "{ Prop (Aux p q), UVar (Aux p q)} \<inter> auxsymbl d = {}" 
      by (induct d rule: swlitfull_cases, auto)
    with I1 have "wf (C1 \<union> C2) d"
      by (auto simp add:wfpat_symb)
    with False show "wff (C1 \<union> C2) (substI1 p q I2 d)"
      by (cases "(p,q,I2,d)" rule: substI1.cases,auto)
  qed 
qed

definition induction_pre
where
  "induction_pre \<sigma> ell I1 I2 \<equiv>
     (\<forall>\<sigma>'. variant (auxvars ell @ auxvars (Not ell)) \<sigma> \<sigma>' \<longrightarrow>
             (evalf \<sigma>' (projA ell) \<longrightarrow>
              evalf \<sigma>' (subst strong I1)) \<and>
             (evalf \<sigma>' (projA (Not ell)) \<longrightarrow>
              evalf \<sigma>' (subst strong I2)))"

lemma inductionrule1 [simp]:
  "\<lbrakk> induction_pre \<sigma> ell I1 I2;
     variant (auxvars ell @ auxvars (Not ell)) \<sigma> \<sigma>';
     evalf \<sigma>' (projA ell) \<rbrakk> \<Longrightarrow> evalf \<sigma>' (subst strong I1)"
  by (unfold induction_pre_def, auto)

lemma inductionrule2 [simp]:
  "\<lbrakk> induction_pre \<sigma> ell I1 I2;
     variant (auxvars ell @ auxvars (Not ell)) \<sigma> \<sigma>';
     evalf \<sigma>' (projA (Not ell)) \<rbrakk> \<Longrightarrow> evalf \<sigma>' (subst strong I2)"
  by (unfold induction_pre_def, auto)

definition contradiction_post
where
  "contradiction_post \<sigma> ell I1 I2  = 
     (\<exists> \<sigma>'. variant (auxvars ell @ auxvars (Not ell)) \<sigma> \<sigma>' \<and>
             (evalf \<sigma>' (projB ell) \<and>
              evalf \<sigma>' (subst strong I1)) \<or>
             (evalf \<sigma>' (projB (Not ell)) \<and>
              evalf \<sigma>' (subst strong I2)))"

lemma contradiction_intro1 [intro]:
  "\<lbrakk> variant (auxvars ell @ auxvars (Not ell)) \<sigma> \<sigma>';
     evalf \<sigma>' (projB ell); evalf \<sigma>' (subst strong I1) \<rbrakk>
   \<Longrightarrow> contradiction_post \<sigma> ell I1 I2"
  by (unfold contradiction_post_def, auto)
lemma contradiction_intro2 [intro]:
  "\<lbrakk> variant (auxvars ell @ auxvars (Not ell)) \<sigma> \<sigma>';
     evalf \<sigma>' (projB (Not ell)); evalf \<sigma>' (subst strong I2) \<rbrakk>
   \<Longrightarrow> contradiction_post \<sigma> ell I1 I2"
  by (unfold contradiction_post_def, auto)

lemma mixedUFrule_correct:
  assumes ismixed: "ismixed p q"
  assumes clean: "cleanresolution (Pos (Eq (Flat p) (Flat q))) C1 C2" 
  assumes ip1: "ispartinterpolant _ (C1 \<union> { Pos (Eq (Flat p) (Flat q)) }) I1"
  assumes ip2: "ispartinterpolant _ (C2 \<union> { Neg (Eq (Flat p) (Flat q)) }) I2"
  shows "ispartinterpolant _ (C1 \<union> C2) (ufsubst p q I1 I2)"
proof (rule strongweakinterpolation, auto simp only:)
  from ip1
  show "ispartinterpolant _ (C1 \<union> { Pos (Eq (Flat p) (Flat q)) }) I1" 
    sorry
  from ip2 
  show "ispartinterpolant _ (C2 \<union> { Not (Pos (Eq (Flat p) (Flat q))) }) I2"
    sorry
  from clean show "cleanresolution (Pos (Eq (Flat p) (Flat q))) C1 C2" .
next
  from ip1 have wff1: "wff (C1 \<union> { Pos (Eq (Flat p) (Flat q)) }) I1"
    by (unfold ispartinterpolant_def, auto simp only: wff_allwf)
  from ip2 have wff2: "wff (C2 \<union> { Neg (Eq (Flat p) (Flat q)) }) I2"
    by (unfold ispartinterpolant_def, auto simp only: wff_allwf)
  from wff1 wff2 have wff3: "wff (C1 \<union> C2) (ufsubst p q I1 I2)" 
    by (rule wffI1I2)
  fix d assume foo: "d \<in> lits (ufsubst p q I1 I2)"
  with wff3 show "wf (C1 \<union> C2) d" by (auto simp only: wff_allwf)
next
  let "?ell" = "Pos (Eq (Flat p) (Flat q))"
  fix \<sigma> 
  assume allproj: "\<forall>\<sigma>'. variant 
              (auxvars (Pos (Eq (Flat p) (Flat q))) @
               auxvars (Not (Pos (Eq (Flat p) (Flat q)))))
              \<sigma> \<sigma>' \<longrightarrow>
             ((evalf \<sigma>' (projA (Pos (Eq (Flat p) (Flat q)))) \<longrightarrow>
              evalf \<sigma>' (subst strong I1)) \<and>
             (evalf \<sigma>' (projA (Not (Pos (Eq (Flat p) (Flat q))))) \<longrightarrow>
              evalf \<sigma>' (subst strong I2)))"
  hence ind: "induction_pre \<sigma> ?ell I1 I2" by (unfold induction_pre_def, simp)
  assume welltyped: "welltyped \<sigma>"
  let "?a" = "select AVars p q"
  def \<sigma>' \<equiv> "\<sigma> (UVar (Aux2 p q) := \<sigma> (UVar (Flat ?a)),
                  UVar (Aux p q) := \<sigma> (UVar (Flat ?a)),
                  Prop (Aux p q) := Bool True)"
  from welltyped
  have "\<sigma> (UVar (Flat p)) \<in> type (UVar (Aux p q))"
       "\<sigma> (UVar (Flat q)) \<in> type (UVar (Aux p q))" 
   by (unfold welltyped_def, auto)
  then
  have "variant [Prop (Aux p q), UVar (Aux p q), UVar (Aux2 p q)] \<sigma> \<sigma>'"
    by (unfold \<sigma>'_def, intro variant_step_intro, auto simp add:select_def)
  with ismixed 
  have variant: "variant (auxvars ?ell @ auxvars (Not ?ell)) \<sigma> \<sigma>'"
    by auto

  from ismixed have "evalf \<sigma>' (projA ?ell)" by (auto simp add: \<sigma>'_def)
  with ind variant have i1: "evalf \<sigma>' (subst strong I1)" by simp

  from ismixed have "evalf \<sigma>' (projA (Not ?ell))" by (auto simp add: \<sigma>'_def)
  with ind variant have i2: "evalf \<sigma>' (subst strong I2)" by simp

  have aeqsI2:
   "\<And> s. evalf \<sigma> (Literal (Pos (Eq (Flat ?a) s))) \<Longrightarrow>
         evalf \<sigma> (subst strong (subst (Literal o (substd p q s)) I2))"
  proof -
    fix s
    assume "evalf \<sigma> (Literal (Pos (Eq (Flat ?a) s)))"
    hence aeqs: "\<sigma> (UVar (Flat ?a)) = \<sigma> (UVar s)" by simp
    hence aeqs1: "\<And> d. \<lbrakk> flatAux2 d; d \<noteq> Aux2 p q \<rbrakk> \<Longrightarrow> 
             \<sigma>' (UVar d) = \<sigma> (UVar (substv p q s d))"
      by (unfold \<sigma>'_def, elim flataux_elim, auto)
    from aeqs
    have aeqs2: "\<sigma>' (UVar (Aux2 p q)) = \<sigma> (UVar s)" by (simp add: \<sigma>'_def)
    have aeqs3: "\<And> v. v \<noteq> Aux p q \<Longrightarrow> \<sigma>' (Prop v) = \<sigma> (Prop v)" by (simp add: \<sigma>'_def)
    have aeqs4: "\<And> p' q'. p' \<noteq> p \<or> q' \<noteq> q \<Longrightarrow> 
       \<sigma>' (UVar (Aux p' q')) = \<sigma> (UVar (Aux p' q'))" by (auto simp add: \<sigma>'_def)
    have aeqs5: "\<And> p' q'. p' \<noteq> p \<or> q' \<noteq> q \<Longrightarrow> 
      \<sigma>' (UVar (Aux2 p' q')) = \<sigma> (UVar (Aux2 p' q'))" by (auto simp add: \<sigma>'_def)

    from ip2
    have wfd: "\<forall> d \<in> lits I2. wf (C2 \<union> { Neg (Eq (Flat p) (Flat q)) }) d"
      by (unfold ispartinterpolant_def, simp)
    {
      fix l assume "l \<in> C2"
      with clean have "cleanlit ?ell" "cleanlit l" "?ell \<noteq> l"
        by (unfold cleanresolution_def, auto)
      hence "set (auxvars ?ell) \<inter> set (auxvars l) = {}" by (rule auxfresh2)
    }
    with wfd ismixed
    have wff: "\<forall> d \<in> lits I2. wfpat d \<and> 
             UVar (Aux p q) \<notin> auxsymbl d \<and> Prop (Aux p q) \<notin> auxsymbl d"
      by (auto simp add: wfpat_symb)
    from i2 wff
    show "evalf \<sigma> (subst strong (subst (Literal o (substd p q s)) I2))"
    proof (induct I2, auto)
      fix lit 
      assume "wfpat lit"
        "UVar (Aux p q) \<notin> auxsymbl lit" 
        "Prop (Aux p q) \<notin> auxsymbl lit"
        "evalf \<sigma>' (strong lit)"
      thus "evalf \<sigma> (strong (substd p q s lit))"
      by (induct lit rule: swlitfull_cases, 
          auto simp add: aeqs1 aeqs2 aeqs3 aeqs4 aeqs5 del:substv.simps)
    qed
  qed
  from ip1
  have "\<forall> d \<in> lits I1. wf (C1 \<union> { ?ell }) d"
      by (unfold ispartinterpolant_def, simp)
  with i1 show "evalf \<sigma> (subst strong (ufsubst p q I1 I2))"
  proof (induct I1, auto simp del: substI1.simps)
    fix lit 
    assume wf1: "wf (insert ?ell C1) lit"
    hence wfp1: "wfpat lit" by (unfold wf_def, simp)
    {
      fix l assume "l \<in> C1"
      with clean have "cleanlit (Not ?ell)" "cleanlit l" "(Not ?ell) \<noteq> l"
        by (unfold cleanresolution_def, auto)
      hence "set (auxvars (Not ?ell)) \<inter> set (auxvars l) = {}" by (rule auxfresh2)
    }
    with wf1 ismixed have clean: "UVar (Aux2 p q) \<notin> auxsymbl lit"
      by (auto simp add: wfpat_symb)
    assume evallit: "evalf \<sigma>' (strong lit)"
    show "evalf \<sigma> (subst strong (substI1 p q I2 lit))"
    proof (cases "\<exists> s. lit = Pos (EQ p q s)")
      case False
      hence "(substI1 p q I2 lit) = Literal lit"
        by (cases "(p,q,I2,lit)" rule: substI1.cases, auto)
      moreover from clean False wfp1
      have "{Prop (Aux p q), UVar (Aux p q), UVar (Aux2 p q)} 
            \<inter> swsymbl lit = {}"
        by (induct lit rule: swlitfull_cases, auto)
      hence "coinc (swsymbl lit) \<sigma> \<sigma>'" 
        by (unfold coinc_def \<sigma>'_def, auto)
      hence "evalf \<sigma> (strong lit) = evalf \<sigma>' (strong lit)"
        by (auto simp add: swsymbl_symbstrong)
      moreover note evallit
      ultimately show "evalf \<sigma> (subst strong (substI1 p q I2 lit))"
        by simp
    next
      case True then obtain s where lit: "lit = Pos (EQ p q s)" by blast
      hence "substI1 p q I2 lit = subst (Literal \<circ> substd p q s) I2" by simp
      moreover
      from clean lit have notAux2: "s \<noteq> Aux2 p q" by auto
      have "\<And> d. flatAux2 d \<Longrightarrow> d \<noteq> Aux p q" by (auto elim:flataux_elim)
      with lit evallit wfp1 notAux2
      have "evalf \<sigma> (Literal (Pos (Eq (Flat ?a) s)))" 
        by (auto simp add:select_def \<sigma>'_def)
      moreover note aeqsI2
      ultimately show "evalf \<sigma> (subst strong (substI1 p q I2 lit))"
        by simp
    qed
  qed
next
  let "?ell" = "Pos (Eq (Flat p) (Flat q))"
  fix \<sigma> 
  assume evalI3: "evalf \<sigma> (subst strong (ufsubst p q I1 I2))"
  assume welltyped: "welltyped \<sigma>"
  let "?b" = "select BVars p q"
  def \<sigma>' \<equiv> "\<sigma> (UVar (Aux2 p q) := \<sigma> (UVar (Flat ?b)),
               UVar (Aux p q) := \<sigma> (UVar (Flat ?b)),
               Prop (Aux p q) := Bool False)"
  from welltyped
  have "\<sigma> (UVar (Flat p)) \<in> type (UVar (Aux p q))"
       "\<sigma> (UVar (Flat q)) \<in> type (UVar (Aux p q))" 
   by (unfold welltyped_def, auto)
  then
  have "variant [Prop (Aux p q), UVar (Aux p q), UVar (Aux2 p q)] \<sigma> \<sigma>'"
    by (unfold \<sigma>'_def, intro variant_step_intro, auto simp add:select_def)
  with ismixed 
  have variant: "variant (auxvars ?ell @ auxvars (Not ?ell)) \<sigma> \<sigma>'"
    by auto
  moreover
  from ismixed have "evalf \<sigma>' (projB ?ell)"
    by (auto simp add: \<sigma>'_def select_def)
  moreover
  from ismixed have "evalf \<sigma>' (projB (Not ?ell))"
    by (auto simp add: \<sigma>'_def select_def)
  moreover 

  from ip2 have wfd: "\<forall> d \<in> lits I2. wf (C2 \<union> { Not ?ell }) d"
    by (unfold ispartinterpolant_def, simp)
  {
    fix l assume "l \<in> C2"
    with clean have "cleanlit ?ell" "cleanlit l" "?ell \<noteq> l"
      by (unfold cleanresolution_def, auto)
    hence "set (auxvars ?ell) \<inter> set (auxvars l) = {}" by (rule auxfresh2)
  }
  with wfd ismixed
  have wff2: "\<forall> d \<in> lits I2. wfpat d \<and> 
    Prop (Aux p q) \<notin> auxsymbl d \<and> UVar (Aux p q) \<notin> auxsymbl d"
    by (auto simp add: wfpat_symb)

  from wff2
  have i2case:
    "\<And> s. \<lbrakk> evalf \<sigma> (subst strong (subst (Literal \<circ> substd p q s) I2));
                \<sigma>' (UVar (Aux2 p q)) = \<sigma> (UVar s) \<rbrakk>
       \<Longrightarrow> evalf \<sigma>' (subst strong I2)"
  proof (induct I2, auto)
    fix s lit
    assume "wfpat lit" "Prop (Aux p q) \<notin> auxsymbl lit"
           "UVar (Aux p q) \<notin> auxsymbl lit"
    hence sigma1: "\<And> d. \<lbrakk> d \<in> swsymbl lit; d \<noteq> UVar (Aux2 p q) \<rbrakk> \<Longrightarrow> 
           \<sigma>' d = \<sigma> d"
      by (induct lit rule: swlitfull_cases, auto simp add: \<sigma>'_def)
    assume "\<sigma>' (UVar (Aux2 p q)) = \<sigma> (UVar s)"
    with sigma1 
    have substv: "\<And> d. (UVar d) \<in> swsymbl lit \<Longrightarrow> 
      \<sigma>' (UVar d) = \<sigma> (UVar (substv p q s d))"
      by auto
    assume "evalf \<sigma> (strong (substd p q s lit))"
    with sigma1 substv
    show "evalf \<sigma>' (strong lit)"
      by (induct lit rule: swlitfull_cases, auto simp del: substv.simps)
  qed

  from ip1 have wfd: "\<forall> d \<in> lits I1. wf (C1 \<union> { ?ell }) d"
    by (unfold ispartinterpolant_def, simp)
  {
    fix l assume "l \<in> C1"
    with clean have "cleanlit (Not ?ell)" "cleanlit l" "Not ?ell \<noteq> l"
      by (unfold cleanresolution_def, auto)
    hence "set (auxvars (Not ?ell)) \<inter> set (auxvars l) = {}" by (rule auxfresh2)
  }
  with wfd ismixed
  have wff1: "\<forall> d \<in> lits I1. wfpat d \<and> UVar (Aux2 p q) \<notin> auxsymbl d"
    by (auto simp add: wfpat_symb)

  from evalI3 wff1
  have "evalf \<sigma>' (subst strong I1) \<or> evalf \<sigma>' (subst strong I2)"
  proof (induct I1, auto)
    fix lit
    assume notI2: "\<not> evalf \<sigma>' (subst strong I2)"
    assume evallit: "evalf \<sigma> (subst strong (substI1 p q I2 lit))"
    assume clean: "wfpat lit" "UVar (Aux2 p q) \<notin> auxsymbl lit"
    show "evalf \<sigma>' (strong lit)"
    proof (cases "\<exists> s. lit = Pos (EQ p q s)")
      case False
      hence "(substI1 p q I2 lit) = Literal lit"
        by (cases "(p,q,I2,lit)" rule: substI1.cases, auto)
      moreover from clean False
      have "{Prop (Aux p q), UVar (Aux p q), UVar (Aux2 p q)} 
            \<inter> swsymbl lit = {}"
        by (induct lit rule: swlitfull_cases, auto)
      hence "coinc (swsymbl lit) \<sigma> \<sigma>'" 
        by (unfold coinc_def \<sigma>'_def, auto)
      hence "evalf \<sigma> (strong lit) = evalf \<sigma>' (strong lit)"
        by (auto simp add: swsymbl_symbstrong)
      moreover note evallit
      ultimately show "evalf \<sigma>' (strong lit)"
        by simp
    next
      case True then obtain s where lit: "lit = Pos (EQ p q s)" by blast
      with evallit 
      have "evalf \<sigma> (subst strong (subst (Literal \<circ> substd p q s) I2))" by simp
      with notI2 i2case
      have "\<sigma>' (UVar (Aux2 p q)) \<noteq> \<sigma> (UVar s)" by auto
      also from lit clean have "flatAux2 s" "s \<noteq> Aux2 p q" by auto
      hence "\<sigma> (UVar s) = \<sigma>' (UVar s)" by (unfold \<sigma>'_def, auto)
      finally have "\<sigma>' (UVar (Aux2 p q)) \<noteq> \<sigma>' (UVar s)" .
      with lit show "evalf \<sigma>' (strong lit)" 
        by (auto simp add: \<sigma>'_def select_def)
    qed
  qed
  ultimately
  show "\<exists> \<sigma>'. variant (auxvars ?ell @ auxvars (Not ?ell)) \<sigma> \<sigma>' \<and>
            ((evalf \<sigma>' (projB (Pos (Eq (Flat p) (Flat q)))) \<and>
              evalf \<sigma>' (subst strong I1)) \<or>
             (evalf \<sigma>' (projB (Not (Pos (Eq (Flat p) (Flat q))))) \<and>
              evalf \<sigma>' (subst strong I2)))"
    by blast
qed

fun chain1 :: "nat list \<Rightarrow> AllVars EqAtom Literal set"
  where "chain1 [] = {}"
  |     "chain1 [x] = {}"
  |     "chain1 (x # y # tail) = 
         insert (Pos (Eq (Flat x) (Flat y))) (chain1 (y#tail))"
  
fun lemma_transitivity :: "nat list \<Rightarrow> AllVars EqAtom Literal set"
  where "lemma_transitivity l = 
           insert (Neg (Eq (Flat (hd l)) (Flat (last l)))) (chain1 l)"

fun chains :: "nat set \<Rightarrow> nat set \<Rightarrow> nat list \<Rightarrow> AllVars list"
  where "chains As Bs (x # y # zs) = 
          (if y \<in> As then
              chains As Bs (y#zs)
           else if x \<in> Bs then
              (Flat x) # chains Bs As (y#zs)
           else
              (Aux2 x y) # chains Bs As (y#zs))"
      | "chains As Bs _ = []"

fun collect :: "AllVars list \<Rightarrow> SWAtom Literal list"
  where "collect (x # y # zs) = (Pos (Quote (Eq x y)) # collect zs)"
      | "collect _ = []"

fun negcollect :: "AllVars \<Rightarrow> AllVars list \<Rightarrow> SWAtom Literal list"
  where "negcollect h [] = []"
      | "negcollect h [x] = [Neg (Quote (Eq x h))]"
      | "negcollect h [x,y] = negcollect h [x]"
      | "negcollect h (x # y # zs) = (Pos (Quote (Eq x y)) # negcollect h zs)"

fun mixcollect :: "nat \<Rightarrow> nat \<Rightarrow> AllVars list \<Rightarrow> SWAtom Literal list"
  where "mixcollect b a (x # zs) = Pos (EQ b a x) # collect zs"
      | "mixcollect b a _ = []"

fun collect_transitivity :: "nat list \<Rightarrow> SWAtom Literal list"
  where "collect_transitivity l = 
   (if (hd l \<in> BVars \<and> last l \<in> BVars) then
       collect (chains AVars BVars l)
    else if (hd l \<in> AVars \<and> last l \<in> AVars) then 
       negcollect (hd (chains BVars AVars l)) (tl (chains BVars AVars l))
    else if last l \<in> AVars then
       mixcollect (hd l) (last l) (rev (chains BVars AVars l))
    else 
       mixcollect (last l) (hd l) (chains AVars BVars l))"

fun buildand :: "SWAtom Literal list \<Rightarrow> SWAtom Formula"
  where "buildand [] = Literal Top"
     |  "buildand [x] = Literal x"
     |  "buildand (x #xs) = And (Literal x) (buildand xs)"

lemma abelim: "\<lbrakk> {As, Bs} = {AVars, BVars}; x \<notin> ABVars \<Longrightarrow> F; 
                x \<in> As \<Longrightarrow> F; x \<in> Bs \<Longrightarrow> F \<rbrakk> \<Longrightarrow> F"
  by (unfold ABVars_def, auto)

fun ip_transitivity :: "nat list \<Rightarrow> SWAtom Formula"
  where "ip_transitivity xs = buildand (collect_transitivity xs)"

definition AandB :: "nat set \<Rightarrow> nat set \<Rightarrow> bool"
  where "AandB As Bs \<equiv> {As,Bs} = {AVars, BVars}"

lemma AandB_commutes: "AandB As Bs = AandB Bs As"
  by (auto simp add: AandB_def)

lemma AandB_inter1: "\<lbrakk> AandB As Bs; x \<in> As; x \<in> Bs \<rbrakk> \<Longrightarrow> Flat x \<in> Flat`AVars"
  and AandB_inter2: "\<lbrakk> AandB As Bs; x \<in> As; x \<in> Bs \<rbrakk> \<Longrightarrow> Flat x \<in> Flat`BVars"
  by (auto simp add: AandB_def)

lemma chain_flataux2: " \<And> As Bs h. \<lbrakk> 
         x \<in> set (chains As Bs (h#t)); h \<in> As;
         set (h#t) \<subseteq> As \<union> Bs; AandB As Bs \<rbrakk> \<Longrightarrow> flatAux2 x"
proof (induct "t")
  fix h a t As Bs
  assume IH: "(\<And>As Bs h.
           x \<in> set (chains As Bs (h # t)) \<Longrightarrow>
           h \<in> As \<Longrightarrow> set (h # t) \<subseteq> As \<union> Bs \<Longrightarrow> AandB As Bs \<Longrightarrow> flatAux2 x)"
  assume pre:
         "x \<in> set (chains As Bs (h # a # t))"
         "h \<in> As" "set (h # a # t) \<subseteq> As \<union> Bs" "AandB As Bs"
  hence lems: "set (a#t) \<subseteq> Bs \<union> As" "AandB Bs As" 
    by (auto simp add:AandB_commutes)
  have cases: "a \<in> As \<or> (a \<notin> As \<and> h \<in> Bs) \<or> (a \<notin> As \<and> h \<notin> Bs)" by blast
  from cases IH pre lems
  show "flatAux2 x"
    by (elim disjE, auto simp add: AandB_commutes AandB_inter1 AandB_inter2)
qed auto

lemma chain_auxsymbl: " \<And> As Bs h. \<lbrakk> 
         Aux2 p q \<in> set (chains As Bs (h#t)); h \<in> As;
         set (h#t) \<subseteq> As \<union> Bs; AandB As Bs \<rbrakk> \<Longrightarrow> 
         (Pos (Eq (Flat p) (Flat q))) \<in> chain1 (h#t)"
proof (induct "t")
  fix h a t As Bs
  assume IH: "(\<And>As Bs h.
           Aux2 p q \<in> set (chains As Bs (h # t)) \<Longrightarrow>
           h \<in> As \<Longrightarrow> set (h # t) \<subseteq> As \<union> Bs \<Longrightarrow> AandB As Bs \<Longrightarrow> 
           Pos (Eq (Flat p) (Flat q)) \<in> chain1 (h # t))"
  assume pre:
         "Aux2 p q \<in> set (chains As Bs (h # a # t))"
         "h \<in> As" "set (h # a # t) \<subseteq> As \<union> Bs" "AandB As Bs"
  hence lems: "set (a#t) \<subseteq> Bs \<union> As" "AandB Bs As" 
    by (auto simp add:AandB_commutes)
  have cases: "a \<in> As \<or> (a \<notin> As \<and> h \<in> Bs) \<or> (a \<notin> As \<and> h \<notin> Bs)" by blast
  from cases IH pre lems
  show "Pos (Eq (Flat p) (Flat q)) \<in> chain1 (h # a # t)"
    by (elim disjE, auto simp add: AandB_commutes AandB_inter1 AandB_inter2)
qed auto

lemma "\<lbrakk> a \<in> BVars; last l \<in> BVars; 
         lit \<in> set (collect_transitivity (a#l)) \<rbrakk> \<Longrightarrow> 
         consequence _ (projA`(lemma_transitivity (a#l))) (strong lit)"
proof -
  let "?cons a l" = 
      "consequence _ (projA`(chain1 (a#l))) (strong lit)"
  assume last: "last l \<in> BVars"
  have "\<And>a. a \<in> BVars \<and> lit \<in> set (collect (chains AVars BVars (a#l))) \<longrightarrow> 
        ?cons _ a l"
        (is "\<And>a. ?IH1 a l")
    and "\<And>a. a \<in> AVars \<and> lit \<in> set (collect (tl (chains BVars AVars (a#l)))) \<longrightarrow>
        ?cons _ a l"
        (is "\<And>a. ?IH2 a l")
    and "\<And>a. a \<in> AVars \<and> chains BVars AVars (a#l) \<noteq> [] \<and>
         lit = Pos (Quote (Eq (Flat a) (hd (chains BVars AVars (a#l))))) \<longrightarrow>
        ?cons _ a l"
        (is "\<And>a. ?IH3 a l")
  proof (induct l)
    fix a
    show "?IH1 a []" by auto
    show "?IH2 a []" by auto
    show "?IH3 a []" by auto
    fix b t
    assume ih1: "\<And> a'. ?IH1 a' t"
    assume ih2: "\<And> a'. ?IH2 a' t"
    assume ih3: "\<And> a'. ?IH3 a' t"
    have cases: "b \<in> AVars \<or> (b \<notin> AVars \<and> a \<in> BVars) \<or> (b \<notin> AVars \<and> a \<notin> BVars)" by blast
    thus "?IH1 a (b#t)"
    proof (elim disjE, auto simp only: chains.simps if_True if_False)
      assume "a \<in> BVars"
      assume "lit \<in> set (collect (chains AVars BVars (b # t)))"
      with ih1 show "?cons _ a (b#t)" 
      proof (auto simp add: chain1.simps consequence.simps)
      assume "b \<in>
             "
    a \<in> BVars \<Longrightarrow>
     \<Longrightarrow>
    True \<Longrightarrow>
    atom.consequence evala type (projA ` lemma_transitivity (a # b # t))
     (strong lit)

      fix a
      assume "a \<in> BVars" "lit \<in> set (collect (chains AVars BVars (a # b # t)"
      s
  
  assume "a \<in> Bs"
         

lemma "\<lbrakk> l : ABVars; hd l \<in> BVars; last l \<in> BVars;
         collect (chains AVars BVars l)
lemma "\<lbrakk> AVars = { 1, 2, 3, 4}; BVars = { 3,4,5, 6}\<rbrakk> \<Longrightarrow>
       result = ip_transitivity [1, 3, 2,5,6]"
  proof auto

end

end
