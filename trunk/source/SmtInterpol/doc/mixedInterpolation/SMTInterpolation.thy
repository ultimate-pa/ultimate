theory SMTInterpolation imports Main begin

text {* The locale atom abstracts logical atoms, valuations, and types.
        We assume typed variables given by type 'a.
        These are mapped to a value domain given by type 'b.
        Atoms are represented as abstract type 'c.
        Valuations are given as mappings from variables to values.
        The function evala takes a valuation and an atom and returns
        the truth value. The value symba takes an atom and returns the
        variables.  The function type takes a variable and returns its
        type. *}

locale atom =
  fixes evala    :: "('a \<Rightarrow> 'b) \<Rightarrow> 'c \<Rightarrow> bool"
  fixes symba    :: "'c \<Rightarrow> 'a set"
  fixes type     :: "('a \<Rightarrow> 'b set)"
  assumes symba_def: "(\<forall> x \<in> (symba f). \<sigma> x = \<sigma>' x) \<Longrightarrow> evala \<sigma> f = evala \<sigma>' f"

definition
  coinc   :: "'a set \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool"
where
  "coinc X \<sigma> \<sigma>' = (\<forall> x \<in> X. \<sigma> x = \<sigma>' x)"
lemma coinc_intro [intro]: "(\<forall> x \<in> X. \<sigma> x = \<sigma>' x) \<Longrightarrow> coinc X \<sigma> \<sigma>'"
  by (unfold coinc_def)
lemma coinc_union [simp]: "coinc (X \<union> Y) \<sigma>  \<sigma>' = (coinc X \<sigma> \<sigma>' & coinc Y \<sigma> \<sigma>')"
  by (unfold coinc_def, blast)

context atom
begin

lemma coinca_elim [elim]: "\<lbrakk> coinc (symba a) \<sigma> \<sigma>'; \<lbrakk> evala \<sigma> a = evala \<sigma>' a \<rbrakk> \<Longrightarrow> F \<rbrakk> \<Longrightarrow> F"
  by  (unfold coinc_def symba_def, auto)

end


datatype 'c Literal =
  Bot | Top | Pos 'c | Neg 'c

primrec Not :: "'c Literal \<Rightarrow> 'c Literal"
where
   "Not (Pos a) = Neg a"
 | "Not (Neg a) = Pos a"
 | "Not Bot = Top"
 | "Not Top = Bot"

lemma notnot [simp]: "Not (Not a) = a" 
  by (induct a, auto)

context atom
begin
primrec evall :: "('a \<Rightarrow> 'b) \<Rightarrow> 'c Literal \<Rightarrow> bool"
where
   "evall \<sigma> (Pos a) = evala \<sigma> a"
 | "evall \<sigma> (Neg a) = (\<not> evala \<sigma> a)"
 | "evall \<sigma> Bot = False"
 | "evall \<sigma> Top = True"

lemma evall_not [simp]: "evall \<sigma> (Not l) = (\<not> evall \<sigma> l)"
  by (induct l, auto)

primrec symbl :: "'c Literal \<Rightarrow> 'a set"
where
   "symbl (Pos a) = symba a"
 | "symbl (Neg a) = symba a"
 | "symbl Bot = {}"
 | "symbl Top = {}"

lemma symbl_not[simp]: "symbl (Not l) = symbl l"
  by (induct l, auto)

lemma coincl_simp [simp]: "coinc (symbl l) \<sigma> \<sigma>' \<Longrightarrow> evall \<sigma> l = evall \<sigma>' l"
  by (induct l, auto)
lemma coincl_elim [elim]: "\<lbrakk> coinc (symbl l) \<sigma> \<sigma>'; \<lbrakk> evall \<sigma> l = evall \<sigma>' l \<rbrakk> \<Longrightarrow> F \<rbrakk> \<Longrightarrow> F"
  by  auto

end

datatype 'c Formula =
   Literal "'c Literal"
 | Or   "'c Formula" "'c Formula" 
 | And  "'c Formula" "'c Formula"

context atom
begin

primrec
   variant :: "('a list) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool"
where
   "variant Nil \<sigma> \<sigma>' = (\<sigma> = \<sigma>')"
 | "variant (x#xs) \<sigma> \<sigma>' = (\<exists> \<sigma>'' d. variant xs \<sigma> \<sigma>''
                          & d \<in> type x & \<sigma>' = \<sigma>''(x := d))"

lemma variant_id [simp]: "variant [] \<sigma> \<sigma>"
  by (unfold variant_def, auto)

lemma variant_same:
  "variant [] \<sigma> \<sigma>' \<Longrightarrow> \<sigma>' = \<sigma>"
  by (unfold variant_def, auto)
  
lemma variant_same_elim [elim]:
  "\<lbrakk> variant [] \<sigma> \<sigma>'; \<sigma>' = \<sigma> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  by (simp only:variant_same)

lemma variant_step_intro [intro]: 
  "\<lbrakk> d \<in> type x; variant xs \<sigma> \<sigma>' \<rbrakk> \<Longrightarrow> variant (x#xs) \<sigma> (\<sigma>'(x:=d))"
  by auto

lemma variant_coinc [elim]:
  "\<And> \<sigma>'. \<lbrakk> variant X \<sigma> \<sigma>'; set X \<inter> Y = {} \<rbrakk> \<Longrightarrow> coinc Y \<sigma> \<sigma>'"
  by (induct X, unfold coinc_def, auto)
  
primrec evalf :: "('a \<Rightarrow> 'b) \<Rightarrow> 'c Formula \<Rightarrow> bool"
where
   "evalf \<sigma> (Literal l) = evall \<sigma> l"
 | "evalf \<sigma> (And f g) = (evalf \<sigma> f \<and> evalf \<sigma> g)"
 | "evalf \<sigma> (Or f g) = (evalf \<sigma> f \<or> evalf \<sigma> g)"

primrec symbf :: "'c Formula \<Rightarrow> 'a set"
where
   "symbf (Literal l) = symbl l"
 | "symbf (And f g) = (symbf f \<union> symbf g)"
 | "symbf (Or f g) = (symbf f \<union> symbf g)"

primrec lits :: "'x Formula \<Rightarrow> 'x Literal set"
where
   "lits (Literal l) = {l}"
 | "lits (And f g) = (lits f \<union> lits g)"
 | "lits (Or f g) = (lits f \<union> lits g)"
  
primrec atomsl :: "'x Literal \<Rightarrow> 'x set"
where
   "atomsl (Pos a) = {a}"
 | "atomsl (Neg a) = {a}"
 | "atomsl Bot = {}"
 | "atomsl Top = {}"

primrec atoms :: "'x Formula \<Rightarrow> 'x set"
where
   "atoms (Literal l) = atomsl l"
 | "atoms (And f g) = (atoms f \<union> atoms g)"
 | "atoms (Or f g) = (atoms f \<union> atoms g)"

lemma coincf_simp [simp]: "coinc (symbf f) \<sigma> \<sigma>' \<Longrightarrow> evalf \<sigma> f = evalf \<sigma>' f"
  by (induct f, auto)
lemma coincf_elim [elim]: "\<lbrakk> coinc (symbf f) \<sigma> \<sigma>'; \<lbrakk> evalf \<sigma> f = evalf \<sigma>' f \<rbrakk> \<Longrightarrow> F \<rbrakk> \<Longrightarrow> F"
  by  auto

end

definition (in atom)
  welltyped :: "('a \<Rightarrow> 'b) \<Rightarrow> bool"
where
  "welltyped \<sigma> \<equiv> (\<forall> x. \<sigma> x \<in> type x)"

fun (in atom) 
  consequence :: "'c Formula set \<Rightarrow> 'c Formula \<Rightarrow> bool"
      ("_ \<Turnstile> _" [60,61] 60)
where
  "consequence fs g = (\<forall> \<sigma>. welltyped \<sigma> \<longrightarrow> (\<forall> f \<in> fs. evalf \<sigma> f) \<longrightarrow> evalf \<sigma> g)"

lemma (in atom) variant_welltyped [simp]:
  "\<And> \<sigma>'. \<lbrakk> variant X \<sigma> \<sigma>'; welltyped \<sigma> \<rbrakk> \<Longrightarrow> welltyped \<sigma>'"
  by (induct X, unfold welltyped_def, auto)

lemma (in atom) 
  notbot: "{ Literal F, Literal (Not F) } \<Turnstile> Literal Bot"
  by (induct F, auto)

definition (in atom) 
  isinterpolant :: "'c Formula \<Rightarrow> 'c Formula \<Rightarrow> 'c Formula \<Rightarrow> bool"
where
  "isinterpolant A B I \<equiv> 
    {A} \<Turnstile> I \<and> {B, I} \<Turnstile> Literal Bot \<and> symbf(I) \<subseteq> symbf(A) \<inter> symbf(B)"

locale interpolationProblem = atom + 
  fixes A :: "'c Formula"
  fixes B :: "'c Formula"

locale mixedinterpolation = interpolationProblem +
  fixes cleanlit  :: "'c Literal \<Rightarrow> bool"
  fixes auxvars   :: "'c Literal \<Rightarrow> 'a list"
  fixes projA     :: "'c Literal \<Rightarrow> 'c Formula"
  fixes projB     :: "'c Literal \<Rightarrow> 'c Formula"
  assumes cleanAB: "\<forall> ell \<in> lits(A) \<union> lits(B). cleanlit ell"
  assumes projA_symb: "(symbf :: 'c Formula \<Rightarrow> 'a set) (projA ell) \<subseteq> symbf(A) \<union> set (auxvars ell)"
  assumes projB_symb: "symbf (projB ell) \<subseteq> symbf(B) \<union> set (auxvars ell)"
  assumes auxfresh: "cleanlit ell \<Longrightarrow> set (auxvars ell) \<inter> (symbf(A) \<union> symbf(B)) = {}"
  assumes auxfresh2: "\<lbrakk> cleanlit ell; cleanlit ell'; ell \<noteq> ell' \<rbrakk>
    \<Longrightarrow> set (auxvars ell) \<inter> set (auxvars ell') = {}"
  assumes projABstrong: "\<lbrakk> cleanlit ell \<rbrakk> \<Longrightarrow>
     (consequence { And (projA ell) (projB ell) } (Literal (Not ell)))"
  assumes projABweak: "\<lbrakk> cleanlit ell; welltyped \<sigma>; evalf \<sigma> (Literal (Not ell)) \<rbrakk> \<Longrightarrow>
     \<exists> \<sigma>'.  variant (auxvars ell) \<sigma> \<sigma>' \<and> 
            evalf \<sigma>' (And (projA ell) (projB ell))"

fun (in mixedinterpolation)
  projcA :: "'c Literal set \<Rightarrow> 'c Formula set"
where
  "projcA C = projA ` C"

fun (in mixedinterpolation)
  projcB :: "'c Literal set \<Rightarrow> 'c Formula set"
where
  "projcB C = projB ` C"

primrec subst :: "('x Literal \<Rightarrow> 'y Formula) \<Rightarrow> 'x Formula \<Rightarrow> 'y Formula"
where
   "subst \<theta> (Literal l) = \<theta> l"
 | "subst \<theta> (Or f g) = Or (subst \<theta> f) (subst \<theta> g)"
 | "subst \<theta> (And f g) = And (subst \<theta> f) (subst \<theta> g)"

locale strongweak = mixedinterpolation +
  fixes wfpat  :: "'d Literal \<Rightarrow> bool"
  fixes strong :: "'d Literal \<Rightarrow> 'c Formula"
  fixes weak   :: "'d Literal \<Rightarrow> 'c Formula"
  fixes quote  :: "'c Literal \<Rightarrow> 'd Literal"
  assumes sw: "{strong d} \<Turnstile> weak d"
  assumes strongsymb: "symbf (strong d) = symbf (weak d)"
  assumes wfquote:  "\<lbrakk> cleanlit c; symbl c \<subseteq> symbf A \<inter> symbf B \<rbrakk>
                    \<Longrightarrow> wfpat (quote c)"
  assumes strongquote[simp]: "strong (quote c) = (Literal c)"
  assumes weakquote[simp]: "weak (quote c) = (Literal c)"

definition (in strongweak)
  wf :: "'c Literal set \<Rightarrow> 'd Literal \<Rightarrow> bool"
where
  "wf C d \<equiv> wfpat d 
          & (\<forall> a \<in> (symbf (strong d) - (symbf A \<inter> symbf B)). 
             \<exists> ell \<in> C. a \<in> set (auxvars ell))"

lemma (in strongweak) wf_elim [elim]: 
  "\<lbrakk> wf (insert ell C) d; 
     \<forall> a \<in> set (auxvars ell). a \<notin> symbf (strong d) \<rbrakk>
  \<Longrightarrow> wf C d"
proof - 
  assume wfC: "wf (insert ell C) d"
  hence  wfinsert: "\<forall> a\<in> symbf (strong d) - symbf A \<inter> symbf B.
                    \<exists>l \<in> insert ell C. a \<in> set (auxvars l)" 
    by (unfold wf_def, auto)
  assume allaux: 
    "\<forall> a \<in> set (auxvars ell). a \<notin> symbf (strong d)"
  hence "\<And> a. a \<in> symbf (strong d) - symbf A \<inter> symbf B
         \<Longrightarrow> \<exists> l \<in> C. a \<in> set (auxvars l)"
 proof -
    fix a
    assume asymb: "a \<in> symbf (strong d) - symbf A \<inter> symbf B"
    with allaux wfinsert
    show "\<exists> l \<in> C. a \<in> set (auxvars l)"
      by (cases "a \<in> set (auxvars ell)", auto)
  qed
  with wfC show "wf C d"
    by (unfold wf_def, auto)
qed

definition (in strongweak)
  ispartinterpolant :: "'c Literal set \<Rightarrow> 'd Formula \<Rightarrow> bool"
where
  "ispartinterpolant C I \<equiv> 
     (projcA C) \<union> {A} \<Turnstile> subst strong I \<and> 
     (projcB C) \<union> {B, subst weak I} \<Turnstile> Literal Bot \<and>
     (\<forall> d \<in> lits I. wf C d)"

lemma (in atom) substlits:
  "\<forall> a \<in> lits F. \<sigma> a = \<sigma>' a \<Longrightarrow> subst \<sigma> F = subst \<sigma>' F"
  by (induct F, auto)


lemma (in strongweak) finalinterpolant: 
  assumes ispart: "ispartinterpolant {} I"
  shows "isinterpolant A B (subst strong I)"
proof -
  from ispart
  have "{A} \<Turnstile> subst strong I"
    by (auto simp add: ispartinterpolant_def)
  moreover
  from sw have sw2: "{subst strong I} \<Turnstile> subst weak I"
    by (induct I, auto)
  from ispart
  have weak: "{B, subst weak I} \<Turnstile> Literal Bot"
    by (auto simp add: ispartinterpolant_def)
  with sw2
  have "{B, subst strong I} \<Turnstile> Literal Bot"
    by auto
  moreover
  { 
    fix d
    assume "d \<in> lits(I)"
    with ispart
    have "wf {} d"
      by (auto simp only: ispartinterpolant_def)
    hence "symbf(strong d) \<subseteq> symbf(A) \<inter> symbf(B)" 
      by (unfold wf_def, blast)
  }
  hence "symbf(subst strong I) \<subseteq> symbf(A) \<inter> symbf(B)"
    by (induct I, auto)
  ultimately
  show "isinterpolant A B (subst strong I)" 
    by (unfold isinterpolant_def, blast)
qed

theorem (in atom) monotonicity:
  "(\<forall> i. consequence (Ass \<union> {G i}) (G' i)) \<Longrightarrow> 
     consequence (Ass \<union> {subst G F}) (subst G' F)"
  by (induct F, auto) 

theorem (in atom) deepsubst:
  assumes g12g3: "\<forall> i j. consequence (Ass \<union> {G1 i, G2 j}) (G3 i j)"
  shows "consequence (Ass \<union> {subst G1 F1, subst G2 F2})
             (subst (%i. subst (%j. G3 i j) F2)  F1)"
proof -
  {
    fix i
    assume "\<forall> j. consequence (Ass \<union> {(G1 i), (G2 j)}) (G3 i j)"
    hence "\<forall> j. consequence (Ass \<union> {G1 i} \<union> {G2 j}) (G3 i j)" by auto
    hence "consequence (Ass \<union> {G1 i} \<union> {subst G2 F2}) 
      (subst (%j. G3 i j) F2)" by (rule monotonicity)
    hence "consequence (Ass \<union> {subst G2 F2} \<union> {G1 i}) 
      (subst (%j. G3 i j) F2)" by auto
  }
  with g12g3
  have "\<forall> i. consequence 
    (Ass \<union> {subst G2 F2} \<union> {G1 i}) (subst (%j. G3 i j) F2)" by auto
  hence "consequence (Ass \<union> {subst G2 F2} \<union> {subst G1 F1})
         (subst (%i. subst (%j. G3 i j) F2) F1)" by (rule monotonicity)
  thus "?thesis" by auto
qed

definition (in mixedinterpolation)
  cleanresolution
where
  "cleanresolution ell C1 C2 \<equiv>
  (\<forall> l \<in> (C1 \<union> C2 \<union> {ell, Not ell}). cleanlit l)
  & {ell, Not ell} \<inter> (C1 \<union> C2) = {}"

context strongweak
begin

lemma strongweakinterpolation:
  assumes ip1: "ispartinterpolant (C1 \<union> { ell }) I1"
  assumes ip2: "ispartinterpolant (C2 \<union> { Not ell }) I2"
  assumes clean: "cleanresolution ell C1 C2"
  assumes ind: "\<forall> \<sigma>. welltyped \<sigma> \<longrightarrow> (\<forall> \<sigma>'. variant (auxvars ell @ auxvars (Not ell)) \<sigma> \<sigma>' \<longrightarrow>
      (evalf \<sigma>' (projA ell) \<longrightarrow> evalf \<sigma>' (subst strong I1))
      \<and> (evalf \<sigma>' (projA (Not ell)) \<longrightarrow> evalf \<sigma>' (subst strong I2)))
    \<longrightarrow> evalf \<sigma> (subst strong I3)"
  assumes cont: "\<forall> \<sigma>. welltyped \<sigma> \<longrightarrow> evalf \<sigma> (subst weak I3) \<longrightarrow>
      (\<exists> \<sigma>'. variant (auxvars ell @ auxvars (Not ell)) \<sigma> \<sigma>' \<and>
         ((evalf \<sigma>' (projB ell) \<and> evalf \<sigma>' (subst weak I1))
          \<or> (evalf \<sigma>' (projB (Not ell)) \<and> evalf \<sigma>' (subst weak I2))))"
  assumes wf: "\<forall> d \<in> lits(I3). wf (C1 \<union> C2) d"
  shows "ispartinterpolant (C1 \<union> C2) I3"
proof -
  have lfresh: "\<And> l. l \<in> C1 \<union> C2 \<Longrightarrow> 
                set (auxvars ell @ auxvars (Not ell)) \<inter> set (auxvars l) = {}" 
  proof -
    fix l
    assume choose: "l \<in> C1 \<union> C2"
    with clean 
    have "ell \<noteq> l" by (auto simp add:cleanresolution_def)
    with clean choose
    have "set (auxvars ell) \<inter> set (auxvars l) = {}" 
      by (unfold cleanresolution_def, intro auxfresh2, auto)
    moreover
    from choose clean
    have "Not ell \<noteq> l" by (auto simp add:cleanresolution_def)
    from clean choose
    have "set (auxvars (Not ell)) \<inter> set (auxvars l) = {}" 
      by (unfold cleanresolution_def, intro auxfresh2, auto)
    ultimately
    show "set (auxvars ell @ auxvars (Not ell)) \<inter> set (auxvars l) = {}" 
      by auto
  qed
  
  have "projcA (C1 \<union> C2) \<union> {A} \<Turnstile> subst strong I3" 
    (is "?C1C2A \<union> {A} \<Turnstile> ?I1S")
  proof auto
    fix \<sigma>
    assume sigmawt: "welltyped \<sigma>"
    assume evalA: "evalf \<sigma> A"
      "\<forall> l \<in> C1 \<union> C2. evalf \<sigma> (projA l)"
    {
      fix \<sigma>'
      assume var: "variant (auxvars ell @ auxvars (Not ell)) \<sigma> \<sigma>'"
      with sigmawt have sigmapwt: "welltyped \<sigma>'" by auto
      from auxfresh clean 
      have afresh: "set (auxvars ell @ auxvars (Not ell)) \<inter> symbf A = {}" 
        by (unfold cleanresolution_def, auto)
      from this var have "coinc (symbf A) \<sigma> \<sigma>'"
        by (auto simp only:)
      with evalA have sigmap1: "evalf \<sigma>' A" by auto
      
      have sigmap2: "\<And> l. l : C1 \<union> C2 \<Longrightarrow> evalf \<sigma>' (projA l)"
      proof -
        fix l
        assume choosel: "l: C1 \<union> C2"
        with evalA have eval2: "evalf \<sigma> (projA l)" by auto
        from choosel 
        have "set (auxvars ell @ auxvars (Not ell)) \<inter> set (auxvars l) = {}" 
          by (rule lfresh)
        with afresh projA_symb
        have "set (auxvars ell @ auxvars (Not ell)) \<inter> symbf (projA l) = {}" by blast
        from this var have "coinc (symbf (projA l)) \<sigma>  \<sigma>'"
          by (auto simp only:)
        with eval2 show "evalf \<sigma>' (projA l)" by auto
      qed

      from ip1 
      have "projcA C1 \<union> { projA ell} \<union> {A} \<Turnstile> subst strong I1" 
        by (auto simp add: ispartinterpolant_def)
      with sigmap1 sigmap2 sigmapwt
      have "evalf \<sigma>' (projA ell) \<longrightarrow> evalf \<sigma>' (subst strong I1)"
        by auto
      moreover
      from ip2 
      have "projcA C2 \<union> { projA (Not ell)} \<union> {A} \<Turnstile> subst strong I2" 
        by (auto simp add: ispartinterpolant_def)
      with sigmap1 sigmap2 sigmapwt
      have "evalf \<sigma>' (projA (Not ell)) \<longrightarrow> evalf \<sigma>' (subst strong I2)"
        by auto
      ultimately
      have "(evalf \<sigma>' (projA ell) \<longrightarrow> evalf \<sigma>' (subst strong I1))
        \<and> (evalf \<sigma>' (projA (Not ell)) \<longrightarrow> evalf \<sigma>' (subst strong I2))" ..
    }
    with sigmawt ind
    show "evalf \<sigma> (subst strong I3)" by auto
  qed
  moreover
  have "\<And> X. projcB (C1 \<union> C2) \<union> {B, subst weak I3} \<Turnstile> X" 
  proof auto
    fix \<sigma> X
    assume sigmawt: "welltyped \<sigma>"
    assume evalB: "evalf \<sigma> B"
          "\<forall> l \<in> C1 \<union> C2. evalf \<sigma> (projB l)"
    assume evalI3: "evalf \<sigma> (subst weak I3)"
    with sigmawt cont
    have "(\<exists> \<sigma>'. variant (auxvars ell @ auxvars (Not ell)) \<sigma> \<sigma>' \<and>
         ((evalf \<sigma>' (projB ell) \<and> evalf \<sigma>' (subst weak I1))
          \<or> (evalf \<sigma>' (projB (Not ell)) \<and> evalf \<sigma>' (subst weak I2))))" by auto
    then obtain "\<sigma>'" where
      var: "variant (auxvars ell @ auxvars (Not ell)) \<sigma> \<sigma>'" and
      eval: "(evalf \<sigma>' (projB ell) \<and> evalf \<sigma>' (subst weak I1))
          \<or> (evalf \<sigma>' (projB (Not ell)) \<and> evalf \<sigma>' (subst weak I2))" by blast
    moreover
    from sigmawt var have sigmapwt: "welltyped \<sigma>'" by auto
    from auxfresh clean 
    have afresh: "set (auxvars ell @ auxvars (Not ell)) \<inter> symbf B = {}" 
      by (unfold cleanresolution_def, auto)
    from this var have "coinc (symbf B) \<sigma> \<sigma>'"
      by (auto simp only:)
    with evalB have sigmap1: "evalf \<sigma>' B" by auto
    
    have sigmap2: "\<And> l. l : C1 \<union> C2 \<Longrightarrow> evalf \<sigma>' (projB l)"
    proof -
      fix l
      assume choosel: "l: C1 \<union> C2"
      with evalB have eval2: "evalf \<sigma> (projB l)" by auto
      from choosel 
      have "set (auxvars ell @ auxvars (Not ell)) \<inter> set (auxvars l) = {}" 
        by (rule lfresh)
      with afresh projB_symb
      have "set (auxvars ell @ auxvars (Not ell)) \<inter> symbf (projB l) = {}" by blast
      from this var have "coinc (symbf (projB l)) \<sigma> \<sigma>'"
        by (auto simp only:)
      with eval2 choosel show "evalf \<sigma>' (projB l)" by auto
    qed

    from ip1 
    have "projcB C1 \<union> { projB ell} \<union> {B, subst weak I1} \<Turnstile> Literal Bot"       
      by (auto simp add: ispartinterpolant_def)
    with sigmap1 sigmap2 sigmapwt
    have "evalf \<sigma>' (projB ell) \<and> evalf \<sigma>' (subst weak I1) \<longrightarrow> False"
      by auto
    moreover
    from ip2 
    have "projcB C2 \<union> { projB (Not ell)} \<union> {B, subst weak I2} \<Turnstile> Literal Bot"       
      by (auto simp add: ispartinterpolant_def)
    with sigmap1 sigmap2 sigmapwt
    have "evalf \<sigma>' (projB (Not ell)) \<and> evalf \<sigma>' (subst weak I2) \<longrightarrow> False"
      by (auto)
    ultimately
    have "False" by blast
    thus "X" ..
  qed
  moreover
  note wf
  ultimately
  show "ispartinterpolant (C1 \<union> C2) I3" 
    by (auto simp only: ispartinterpolant_def)
qed

lemma notmixedA:
  "\<And> ell. \<lbrakk> cleanlit ell; welltyped \<sigma>; auxvars ell = []; evall \<sigma> (Not ell) \<rbrakk> \<Longrightarrow> evalf \<sigma> (projA ell)"
proof -
  fix ell
  assume clean: "cleanlit ell"
  assume wt: "welltyped \<sigma>"
  assume notmixed: "auxvars ell = []"
  assume "evall \<sigma> (Not ell)"
  with projABweak clean wt
  have "\<exists> \<sigma>'. variant (auxvars ell) \<sigma> \<sigma>' \<and> evalf \<sigma>' (And (projA ell) (projB ell))" 
    by simp
  with notmixed 
  show "evalf \<sigma> (projA ell)"
    by auto
qed

lemma notmixedB:
  "\<And> ell. \<lbrakk> cleanlit ell; welltyped \<sigma>; auxvars ell = []; evall \<sigma> (Not ell) \<rbrakk> \<Longrightarrow> evalf \<sigma> (projB ell)"
proof -
  fix ell
  assume clean: "cleanlit ell"
  assume wt: "welltyped \<sigma>"
  assume notmixed: "auxvars ell = []"
  assume "evall \<sigma> (Not ell)"
  with projABweak wf clean wt
  have "\<exists> \<sigma>'. variant (auxvars ell) \<sigma> \<sigma>' \<and> evalf \<sigma>' (And (projA ell) (projB ell))" 
    by simp
  with notmixed
  show "evalf \<sigma> (projB ell)"
    by auto
qed

lemma pudlak_A_correct:
  assumes Alocal: "projB ell = Literal (Not Bot)"
                  "projB (Not ell) = Literal (Not Bot)"
  assumes notmixed: "auxvars ell = []" "auxvars (Not ell) = []"
  assumes clean: "cleanresolution ell C1 C2"
  assumes ip1: "ispartinterpolant (C1 \<union> { ell }) I1"
  assumes ip2: "ispartinterpolant (C2 \<union> { Not ell }) I2"
  shows "ispartinterpolant (C1 \<union> C2) (Or I1 I2)"
proof (rule strongweakinterpolation, auto simp only:)
  from ip1 show "ispartinterpolant (C1 \<union> { ell }) I1" .
  from ip2 show "ispartinterpolant (C2 \<union> { Not ell }) I2" .
  from clean show "cleanresolution ell C1 C2" .
next
  fix \<sigma>
  assume wt: "welltyped \<sigma>"
  assume I1I2: "(\<forall> \<sigma>'. variant (auxvars ell @ auxvars (Not ell)) \<sigma> \<sigma>' \<longrightarrow>
    (evalf \<sigma>' (projA ell) \<longrightarrow> evalf \<sigma>' (subst strong I1))
    \<and> (evalf \<sigma>' (projA (Not ell)) \<longrightarrow> evalf \<sigma>' (subst strong I2)))"
  show "evalf \<sigma> (subst strong (Or I1 I2))" 
  proof (cases "(evall \<sigma> ell)")
    assume "evall \<sigma> ell"
    with notmixed clean wt
    have "evalf \<sigma> (projA (Not ell))" 
      by (unfold cleanresolution_def, auto intro: notmixedA)
    with I1I2 notmixed have "evalf \<sigma> (subst strong I2)"
      by auto
    thus "evalf \<sigma> (subst strong (Or I1 I2))" 
      by auto
  next
    assume "\<not> evall \<sigma> ell" hence "evall \<sigma> (Not ell)" by simp
    with notmixed notmixedA clean wt
    have "evalf \<sigma> (projA ell)" 
      by (unfold cleanresolution_def, auto intro: notmixedA)
    with I1I2 notmixed
    have "evalf \<sigma> (subst strong I1)"
      by auto
    hence "evalf \<sigma> (subst strong I1)"
      by auto
    thus "evalf \<sigma> (subst strong (Or I1 I2))" 
      by auto
  qed
next
  fix \<sigma>
  assume "evalf \<sigma> (subst weak (Or I1 I2))"
  with Alocal
  have "(evalf \<sigma> (projB ell) \<and> evalf \<sigma> (subst weak I1) \<or>
         evalf \<sigma> (projB (Not ell)) \<and> evalf \<sigma> (subst weak I2))" (is "?goal")
    by (auto)
  with notmixed
  show "\<exists> \<sigma>'. variant (auxvars ell @ auxvars (Not ell)) \<sigma> \<sigma>' \<and>
        (evalf \<sigma>' (projB ell) \<and> evalf \<sigma>' (subst weak I1) \<or>
         evalf \<sigma>' (projB (Not ell)) \<and> evalf \<sigma>' (subst weak I2))" 
    by auto
next
  fix d
  assume dlits: "d \<in> lits (Or I1 I2)"
  show "wf (C1 \<union> C2) d" 
  proof (cases "d \<in> lits(I1)")
    case True with ip1 have "wf (insert ell C1) d"
      by (unfold ispartinterpolant_def, auto)
    with notmixed have "wf C1 d" 
      by (elim wf_elim, auto)
    thus "wf (C1 \<union> C2) d" by (unfold wf_def, blast)
  next
    case False with ip2 dlits have "wf (insert (Not ell) C2) d"
      by (unfold ispartinterpolant_def, auto)
    with notmixed have "wf C2 d" 
      by (elim wf_elim, auto)
    thus "wf (C1 \<union> C2) d" by (unfold wf_def, blast)
  qed
qed
    

lemma pudlak_B_correct:
  assumes Blocal: "projA ell = Literal (Not Bot)"
                  "projA (Not ell) = Literal (Not Bot)"
  assumes notmixed: "auxvars ell = []" "auxvars (Not ell) = []"
  assumes clean: "cleanresolution ell C1 C2"
  assumes ip1: "ispartinterpolant (C1 \<union> { ell }) I1"
  assumes ip2: "ispartinterpolant (C2 \<union> { Not ell }) I2"
  shows "ispartinterpolant (C1 \<union> C2) (And I1 I2)"
proof (rule strongweakinterpolation, auto simp only:)
  from ip1 show "ispartinterpolant (C1 \<union> { ell }) I1" .
  from ip2 show "ispartinterpolant (C2 \<union> { Not ell }) I2" .
  from clean show "cleanresolution ell C1 C2" .
next
  fix \<sigma>
  assume I1I2: "(\<forall> \<sigma>'. variant (auxvars ell @ auxvars (Not ell)) \<sigma> \<sigma>' \<longrightarrow>
    (evalf \<sigma>' (projA ell) \<longrightarrow> evalf \<sigma>' (subst strong I1))
    \<and> (evalf \<sigma>' (projA (Not ell)) \<longrightarrow> evalf \<sigma>' (subst strong I2)))"
  with notmixed
  have "(evalf \<sigma> (projA ell) \<longrightarrow> evalf \<sigma> (subst strong I1))
    \<and> (evalf \<sigma> (projA (Not ell)) \<longrightarrow> evalf \<sigma> (subst strong I2))"
    by (auto)
  with Blocal
  have "evalf \<sigma> (subst strong I1) \<and> evalf \<sigma> (subst strong I2)"
    by (simp)
  thus "evalf \<sigma> (subst strong (And I1 I2))" by simp
next
  fix \<sigma>
  assume wt: "welltyped \<sigma>"
  assume "evalf \<sigma> (subst weak (And I1 I2))"
  hence i3: "evalf \<sigma> (And (subst weak I1) (subst weak I2))" by simp
  hence "(evalf \<sigma> (projB ell) \<and> evalf \<sigma> (subst weak I1) \<or>
         evalf \<sigma> (projB (Not ell)) \<and> evalf \<sigma> (subst weak I2))" (is "?goal")
  proof (cases "evalf \<sigma> (Literal (Not ell))")
    case True 
    with clean wt projABweak
    have "\<exists> \<sigma>'.  variant (auxvars ell) \<sigma> \<sigma>' \<and> 
      evalf \<sigma>' (And (projA ell) (projB ell))" 
      by (unfold cleanresolution_def, auto)
    with notmixed have "\<exists> \<sigma>'. coinc (symbf (projB ell)) \<sigma> \<sigma>' \<and> evalf \<sigma>' (projB ell)"
      by (auto)
    hence "evalf \<sigma> (projB ell)" by auto
    with i3 show "?goal" by simp
  next
    case False
    hence "evalf \<sigma> (Literal (Not (Not ell)))" by simp
    with clean projABweak wt
    have "\<exists> \<sigma>'.  variant (auxvars (Not ell)) \<sigma> \<sigma>' \<and> 
      evalf \<sigma>' (And (projA (Not ell)) (projB (Not ell)))" 
      by (unfold cleanresolution_def, auto)
    with notmixed have "\<exists> \<sigma>'. coinc (symbf (projB (Not ell))) \<sigma> \<sigma>' 
      \<and> evalf \<sigma>' (projB (Not ell))"
      by (auto)
    hence "evalf \<sigma> (projB (Not ell))" by auto
    with i3 show "?goal" by simp
  qed
  with notmixed
  show "\<exists> \<sigma>'. variant (auxvars ell @ auxvars (Not ell)) \<sigma> \<sigma>' \<and>
        (evalf \<sigma>' (projB ell) \<and> evalf \<sigma>' (subst weak I1) \<or>
         evalf \<sigma>' (projB (Not ell)) \<and> evalf \<sigma>' (subst weak I2))" 
    by (auto)
next
  fix d
  assume dlits: "d \<in> lits (And I1 I2)"
  show "wf (C1 \<union> C2) d" 
  proof (cases "d \<in> lits(I1)")
    case True with ip1 have "wf (insert ell C1) d"
      by (unfold ispartinterpolant_def, auto)
    with notmixed have "wf C1 d" 
      by (elim wf_elim, auto)
    thus "wf (C1 \<union> C2) d" by (unfold wf_def, blast)
  next
    case False with ip2 dlits have "wf (insert (Not ell) C2) d"
      by (unfold ispartinterpolant_def, auto)
    with notmixed have "wf C2 d" 
      by (elim wf_elim, auto)
    thus "wf (C1 \<union> C2) d" by (unfold wf_def, blast)
  qed
qed

lemma pudlak_shared_correct:
  assumes shared: "symbl ell \<subseteq> (symbf A \<inter> symbf B)"
  assumes notmixed: "auxvars ell = []" "auxvars (Not ell) = []"
  assumes clean: "cleanresolution ell C1 C2"
  assumes ip1: "ispartinterpolant (C1 \<union> { ell }) I1"
  assumes ip2: "ispartinterpolant (C2 \<union> { Not ell }) I2"
  shows "ispartinterpolant (C1 \<union> C2) (And (Or I1 (Literal (quote ell)))
                                     (Or I2 (Literal (quote (Not ell)))))"
         (is "ispartinterpolant ?C3 ?I3")
proof (rule strongweakinterpolation, auto simp only:)
  from ip1 show "ispartinterpolant (C1 \<union> { ell }) I1" .
  from ip2 show "ispartinterpolant (C2 \<union> { Not ell }) I2" .
  from clean show "cleanresolution ell C1 C2" .
next
  fix \<sigma>
  assume wt: "welltyped \<sigma>"
  assume I1I2: "(\<forall> \<sigma>'. variant (auxvars ell @ auxvars (Not ell)) \<sigma> \<sigma>' \<longrightarrow>
    (evalf \<sigma>' (projA ell) \<longrightarrow> evalf \<sigma>' (subst strong I1))
    \<and> (evalf \<sigma>' (projA (Not ell)) \<longrightarrow> evalf \<sigma>' (subst strong I2)))"
  with notmixed
  have pre: "(evalf \<sigma> (projA ell) \<longrightarrow> evalf \<sigma> (subst strong I1))
    \<and> (evalf \<sigma> (projA (Not ell)) \<longrightarrow> evalf \<sigma> (subst strong I2))"
    by auto
  show "evalf \<sigma> (subst strong (And (Or I1 (Literal (quote ell)))
                              (Or I2 (Literal (quote (Not ell))))))" 
    (is "?goal")
  proof (cases "evall \<sigma> (Not ell)")
    case True 
    with notmixed clean wt 
    have "evalf \<sigma> (projA ell)" 
      by (unfold cleanresolution_def, auto intro: notmixedA)
    with pre have "evalf \<sigma> (subst strong I1)" by auto
    with True show "?goal" by auto
  next
    case False 
    with notmixed clean wt 
    have "evalf \<sigma> (projA (Not ell))" 
      by (unfold cleanresolution_def, auto intro: notmixedA)
    with pre have "evalf \<sigma> (subst strong I2)" by auto
    with False show "?goal" by auto
  qed
next
  fix \<sigma>
  assume wt: "welltyped \<sigma>"
  assume "evalf \<sigma> (subst weak (And (Or I1 (Literal (quote ell)))
                              (Or I2 (Literal (quote (Not ell))))))"
  hence i3: "(evall \<sigma> ell \<or> evalf \<sigma> (subst weak I1)) \<and>
         (evall \<sigma> (Not ell) \<or> evalf \<sigma> (subst weak I2))" 
    by auto
  have "(evalf \<sigma> (projB ell) \<and> evalf \<sigma> (subst weak I1) \<or>
         evalf \<sigma> (projB (Not ell)) \<and> evalf \<sigma> (subst weak I2))" (is "?goal")
  proof (cases "evall \<sigma> (Not ell)")
    case True 
    with notmixed clean wt
    have "evalf \<sigma> (projB ell)" 
      by (unfold cleanresolution_def, auto intro: notmixedB)
    with i3 True show "?goal" by auto
  next
    case False 
    with notmixed clean wt
    have "evalf \<sigma> (projB (Not ell))" 
      by (unfold cleanresolution_def, auto intro: notmixedB)
    with i3 False show "?goal" by auto
  qed
  with notmixed
  show "\<exists>\<sigma>'. variant (auxvars ell @ auxvars (Not ell)) \<sigma> \<sigma>' \<and>
             (evalf \<sigma>' (projB ell) \<and> evalf \<sigma>' (subst weak I1) \<or>
    evalf \<sigma>' (projB (Not ell)) \<and> evalf \<sigma>' (subst weak I2))"
    by auto
next
  fix d
  assume lit: "d \<in> lits (And (Or I1 (Literal (quote ell)))
                         (Or I2 (Literal (quote (Not ell)))))"
  hence "d \<in> lits (I1) \<or> d \<in> lits(I2) \<or> 
         d \<in> {quote ell, quote (Not ell)}" by auto
  thus "wf (C1 \<union> C2) d" 
  proof (elim disjE)
    assume "d \<in> lits I1"
    with ip1 have "wf (insert ell C1) d"
      by (unfold ispartinterpolant_def, auto)
    with notmixed have "wf C1 d" 
      by (elim wf_elim, auto)
    thus "wf (C1 \<union> C2) d" by (unfold wf_def, blast)
  next
    assume "d \<in> lits I2"
    with ip2 have "wf (insert (Not ell) C2) d"
      by (unfold ispartinterpolant_def, auto)
    with notmixed have "wf C2 d" 
      by (elim wf_elim, auto)
    thus "wf (C1 \<union> C2) d" by (unfold wf_def, blast)
  next
    from shared clean have pat: "wfpat (quote ell)" "wfpat (quote (Not ell))"
      by (unfold cleanresolution_def, auto simp add: wfquote)
    assume quote: "d \<in> { quote ell, quote (Not ell) }"
    hence "strong d \<in> {Literal ell, Literal (Not ell)}" by auto
    hence "symbf (strong d) = symbl ell" 
      by auto
    also note shared
    finally have "symbf (strong d) - symbf A \<inter> symbf B = {}" by blast
    with pat quote clean show "wf (C1 \<union> C2) d" 
      by (unfold wf_def cleanresolution_def, auto)
  qed
qed
end

end
