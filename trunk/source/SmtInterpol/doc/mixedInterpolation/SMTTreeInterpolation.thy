theory SMTTreeInterpolation
imports SMTInterpolation
begin

fun
  nary_and :: "'c Formula list \<Rightarrow> 'c Formula"
where
  nary_and_empty:     "nary_and [] = Literal Top" |
  nary_and_singleton: "nary_and (F # []) = F" |
  nary_and_step:      "nary_and (F1 # l) = And F1 (nary_and l)"

lemma (in atom)  "\<lbrakk> x\<in>set Y; evalf \<sigma> (nary_and Y) \<rbrakk> \<Longrightarrow> evalf \<sigma> x"
proof (induct Y, simp)
  fix a Y
  show "(x \<in> set Y \<Longrightarrow> evalf \<sigma> (nary_and Y) \<Longrightarrow> evalf \<sigma> x) \<Longrightarrow>
       x \<in> set (a # Y) \<Longrightarrow> evalf \<sigma> (nary_and (a # Y)) \<Longrightarrow> evalf \<sigma> x"
    by (cases "x=a", cases Y, auto, cases Y, auto)
qed

datatype tree =
  Node nat "tree list"

fun
  node_list :: "tree \<Rightarrow> tree list"
where
  "node_list (Node n l) = ((Node n l) # concat (map node_list l))"

fun nodes :: "tree \<Rightarrow> tree set" where
  "nodes (Node n l) = {(Node n l)} \<union> {n. \<exists>x\<in>set l. n\<in>nodes(x)}"

lemma node_list_is_nodes: "set (node_list t) = nodes t"
  and node_list_is_nodes_list: "{n. \<exists>x\<in>set l. n\<in>nodes(x)} = set (concat (map node_list l))"
  by (induct t and l,auto)

fun children :: "tree \<Rightarrow> tree set" where
  "children (Node n l) = set l"

locale treeInterpolation = atom +
  fixes problem :: tree
  fixes labelling :: "tree \<Rightarrow> 'c Formula"

definition (in treeInterpolation)
  innerSymbols :: "tree \<Rightarrow> 'a set"
where
  "innerSymbols n = (\<Union>m\<in>nodes(n). symbf(labelling(m)))"

definition (in treeInterpolation)
  outerSymbols :: "tree \<Rightarrow> 'a set"
where
  "outerSymbols n = (\<Union>m\<in>(nodes(problem) - nodes(n)). symbf(labelling(m)))"

definition (in treeInterpolation)
  sharedSymbols :: "tree \<Rightarrow> 'a set"
where
  "sharedSymbols n = (innerSymbols n) \<inter> (outerSymbols n)"

definition (in treeInterpolation) 
  istreeinterpolant :: "(tree \<Rightarrow> 'c Formula) \<Rightarrow> bool"
where
  "istreeinterpolant I \<equiv> 
    (I problem) = Literal Bot \<and> (\<forall>n\<in>nodes(problem). 
      ((I ` children(n))\<union>{(labelling n)}\<Turnstile>(I n)) \<and>
      (symbf (I n) \<subseteq> sharedSymbols n))"

locale mixedTreeInterpolation = treeInterpolation +
  fixes cleanlit  :: "'c Literal \<Rightarrow> bool"
  fixes auxvars   :: "'c Literal \<Rightarrow> tree \<Rightarrow> 'a list"
  fixes proj      :: "'c Literal \<Rightarrow> tree \<Rightarrow> 'c Formula"
  fixes quote     :: "'c Literal \<Rightarrow> 'd Literal"
  fixes unfold    :: "'d Literal \<Rightarrow> 'c Formula"
  fixes wfpat     :: "'d Literal \<Rightarrow> tree \<Rightarrow> bool"
  fixes allauxvars:: "'c Literal \<Rightarrow> 'a list"
  assumes allauxvars_def: "allauxvars ell = concat (map (auxvars ell) (node_list problem))"
  assumes cleanAB: "\<forall> ell \<in> {l |l. \<exists>n\<in>nodes(problem). l\<in>lits(labelling(n))}. cleanlit ell"
  assumes proj_symb: "\<forall>n\<in>nodes(problem). (symbf :: 'c Formula \<Rightarrow> 'a set) (proj ell n) \<subseteq> (innerSymbols n) \<union> set (auxvars ell n)"
  assumes auxfresh: "cleanlit ell \<Longrightarrow> (\<forall>n\<in>nodes(problem). set (auxvars ell n) \<inter> (\<Union>n\<in>nodes(problem). symbf(labelling n)) = {})"
  assumes auxfresh2: "\<lbrakk> cleanlit ell; cleanlit ell'; ell \<noteq> ell' \<rbrakk>
    \<Longrightarrow> (\<forall>n\<in>nodes(problem). \<forall>m\<in>nodes(problem). set (auxvars ell n) \<inter> set (auxvars ell' m) = {})"
  assumes wfquote:  "\<lbrakk> cleanlit c; symbl c \<subseteq> sharedSymbol n \<rbrakk>
                    \<Longrightarrow> wfpat (quote c) n"
  assumes unfoldquote[simp]: "unfold (quote c) = (Literal c)"
  assumes projstrong: "\<lbrakk> cleanlit ell \<rbrakk> \<Longrightarrow>
     (consequence ((proj ell) ` nodes(problem)) (Literal (Not ell)))"
  assumes projweak: "\<lbrakk> cleanlit ell; welltyped \<sigma>; evalf \<sigma> (Literal (Not ell)) \<rbrakk> \<Longrightarrow>
     \<exists> \<sigma>'.  variant (allauxvars ell) \<sigma> \<sigma>' \<and> 
            evalf \<sigma>' (nary_and (map (proj ell) (node_list problem)))"

fun (in mixedTreeInterpolation)
  projcn :: "'c Literal set \<Rightarrow> tree \<Rightarrow> 'c Formula set"
where
  "projcn C n = (\<lambda>l. proj l n) ` C"

definition (in mixedTreeInterpolation)
  wf :: "'c Literal set \<Rightarrow> 'd Literal \<Rightarrow> tree \<Rightarrow> bool"
where
  "wf C d n \<equiv> wfpat d n
          & (\<forall> a \<in> (symbf (unfold d) - (sharedSymbols n)). 
             \<exists> ell \<in> C. a \<in> (set (auxvars ell n)\<union>(\<Union>m\<in>children(n). set (auxvars ell m))))"

lemma (in mixedTreeInterpolation) wf_elim [elim]: 
assumes wfinsert: "wf (insert ell C) d n" and
        auxfree: "\<forall> a \<in> set (auxvars ell n)\<union>(\<Union>m\<in>children n. set (auxvars ell m)). a \<notin> symbf (unfold d)"
shows "wf C d n"
proof (unfold wf_def, rule conjI)
  from wfinsert show "wfpat d n" unfolding wf_def ..
  from wfinsert have "(\<forall>a\<in>symbf (unfold d) - sharedSymbols n.
    \<exists>ell\<in>insert ell C. a \<in> set (auxvars ell n) \<union> (\<Union>m\<in>children n. set (auxvars ell m)))" unfolding wf_def ..
  with auxfree show "\<forall>a\<in>symbf (unfold d) - sharedSymbols n.
       \<exists>ell\<in>C. a \<in> set (auxvars ell n) \<union> (\<Union>m\<in>children n. set (auxvars ell m))" by blast
qed


lemma (in atom) symbf_subst:
   "\<lbrakk> !!d. d \<in> lits F \<Longrightarrow> symbf (u d) \<subseteq> symbset \<rbrakk>
       \<Longrightarrow> symbf (subst u F) \<subseteq> symbset"
  by (induct F, auto)

definition (in mixedTreeInterpolation)
  isparttreeinterpolant :: "'c Literal set \<Rightarrow> (tree \<Rightarrow> 'd Formula) \<Rightarrow> bool"
where
  "isparttreeinterpolant C I \<equiv> (subst unfold (I problem) = (Literal Bot)) \<and>
    (\<forall>n\<in>nodes(problem). 
      ((\<lambda>n. subst unfold (I n)) ` children n)\<union>{(labelling n)}\<union>projcn C n\<Turnstile>subst unfold (I n) \<and>
      (\<forall> d \<in> lits (I n). wf C d n))"

lemma (in mixedTreeInterpolation) finalinterpolant: 
  assumes ispart: "isparttreeinterpolant {} I"
  shows "istreeinterpolant (\<lambda>n. (subst unfold (I n)))"
  proof -
  from ispart have "subst unfold (I problem) = Literal Bot"
    unfolding isparttreeinterpolant_def by (elim conjE)
  moreover
  from ispart have "(\<forall>n\<in>nodes problem.
        (\<lambda>n. subst unfold (I n)) ` children n \<union> {labelling n} \<Turnstile> subst unfold (I n)\<and>
        symbf (subst unfold (I n)) \<subseteq> sharedSymbols n)"
    unfolding isparttreeinterpolant_def proof (intro ballI conjI, simp)
      fix n
      assume problemnode: "n \<in> nodes problem"
      assume "subst unfold (I problem) = Literal Bot \<and>
        (\<forall>n\<in>nodes problem.
            (\<lambda>n. subst unfold (I n)) ` children n \<union> {labelling n} \<union>
            projcn {} n \<Turnstile> subst unfold (I n) \<and>
            (\<forall>d\<in>lits (I n). wf {} d n))"
      with problemnode have "(\<forall>d\<in>lits (I n). wf {} d n)" by (simp)
      hence "(\<forall>d\<in>lits (I n). symbf (unfold d) \<subseteq> sharedSymbols n)" unfolding wf_def by (fast)
      hence "\<And>d. d\<in>lits (I n) \<Longrightarrow> symbf (unfold d) \<subseteq> sharedSymbols n" ..
      then show "symbf (subst unfold (I n)) \<subseteq> sharedSymbols n" 
        by (elim symbf_subst)
    qed
  ultimately show "?thesis" unfolding istreeinterpolant_def ..
qed

lemma (in mixedTreeInterpolation) notmixed:
  "\<And> ell n. \<lbrakk> n \<in> nodes problem; cleanlit ell; welltyped \<sigma>; auxvars ell n = []; evall \<sigma> (Not ell) \<rbrakk> \<Longrightarrow> 
    evalf \<sigma> (proj ell n)"
proof -
  fix ell n
  assume "evall \<sigma> (Not ell)" then have notEll: "evalf \<sigma> (Literal (Not ell))" by (simp)
  assume "cleanlit ell" "welltyped \<sigma>"
  from this notEll have 
    "\<exists>\<sigma>'. variant (allauxvars ell) \<sigma> \<sigma>' \<and> evalf \<sigma>' (nary_and (map (proj ell) (node_list problem)))"
  by (rule projweak)
  from this obtain "\<sigma>'" where 
    "variant (allauxvars ell) \<sigma> \<sigma>' \<and> evalf \<sigma>' (nary_and (map (proj ell) (node_list problem)))"
  ..
  hence variant: "variant (allauxvars ell) \<sigma> \<sigma>'" and
        evalf: "evalf \<sigma>' (nary_and (map (proj ell) (node_list problem)))"
        by (auto)
  assume nintree: "n\<in>nodes(problem)"
  hence "n \<in> set (node_list problem)" by (simp add: node_list_is_nodes[symmetric])
  with evalf have "evalf \<sigma>' (proj ell n)" proof 

  with variant and notEll have "evalf \<sigma>' (Literal (Not ell))" proof (auto simp add: allauxvars_def node_list_is_nodes)
  


end
