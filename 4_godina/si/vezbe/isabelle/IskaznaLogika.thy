theory IskaznaLogika
  imports Main

begin

datatype prop_form = 
    TOP
  | BOT
  | VAR nat
  | NOT prop_form
  | AND prop_form prop_form (infixl "AND" 104)
  | OR prop_form prop_form (infixl "OR" 103)
  | IMP prop_form prop_form (infixl "IMP" 102)
  | EQ prop_form prop_form (infixl "EQ" 101)

term "TOP AND BOT EQ TOP"

type_synonym valuation = "nat \<Rightarrow> bool"

primrec Iv :: "valuation \<Rightarrow> prop_form \<Rightarrow> bool"
  where
    "Iv v TOP = True"
  | "Iv v BOT = False"
  | "Iv v (VAR x) = v x"
  | "Iv v (NOT f) = (\<not> (Iv v f))"
  | "Iv v (f1 AND f2) = (Iv v f1 \<and> Iv v f2)"
  | "Iv v (f1 OR f2) = (Iv v f1 \<or> Iv v f2)"
  | "Iv v (f1 IMP f2) = (Iv v f1 \<longrightarrow> Iv v f2)"
  | "Iv v (f1 EQ f2) = (Iv v f1 \<longleftrightarrow> Iv v f2)"

lemma 
  shows "Iv v (f1 AND f2) \<longleftrightarrow> (if Iv v f1 = True \<and> Iv v f2 = True then True else False)"
  by auto
lemma
  shows "Iv v (f1 IMP f2) \<longleftrightarrow> (if Iv v f1 = False \<or> Iv v f2 = True then True else False)"
  by auto

definition satisfies :: "valuation \<Rightarrow> prop_form \<Rightarrow> bool" (infix "|=" 50) where
  "satisfies v f \<longleftrightarrow> Iv v f = True"

lemma satisfies [simp]:
  "v |= TOP"
  "\<not> (v |= BOT)"
  "v |= VAR n \<longleftrightarrow> v n"
  "v |= NOT f \<longleftrightarrow> \<not> v |= f"
  "v |= f1 AND f2 \<longleftrightarrow> v |= f1 \<and> v |= f2"
  "v |= f1 OR f2 \<longleftrightarrow> v |= f1 \<or> v |= f2"
  "v |= f1 IMP f2 \<longleftrightarrow> v |= f1 \<longrightarrow> v |= f2"
  "v |= f1 EQ f2 \<longleftrightarrow> (v |= f1 \<longleftrightarrow> v |= f2)"
  by (auto simp add: satisfies_def)

definition tautology :: "prop_form \<Rightarrow> bool" where
  "tautology f \<longleftrightarrow> (\<forall> v. v |= f)"

definition satisfiable :: "prop_form \<Rightarrow> bool" where
  "satisfiable f \<longleftrightarrow> (\<exists> v. v |= f)"

lemma "tautology f \<longleftrightarrow> \<not> satisfiable (NOT f)"
  unfolding tautology_def satisfiable_def satisfies_def
  by auto

primrec vars :: "prop_form \<Rightarrow> nat set" where
  "vars TOP = {}"
| "vars BOT = {}"
| "vars (VAR x) = {x}"
| "vars (NOT f) = vars f"
| "vars (f1 AND f2) = vars f1 \<union> vars f2"
| "vars (f1 OR f2) = vars f1 \<union> vars f2"
| "vars (f1 IMP f2) = vars f1 \<union> vars f2"
| "vars (f1 EQ f2) = vars f1 \<union> vars f2"

lemma finite_vars:
  shows "finite (vars f)"
  by (induction f) auto

lemma relevant_vars:
  assumes "\<forall> n \<in> vars f. v1 n = v2 n"
  shows "Iv v1 f = Iv v2 f"
  using assms
  by (induction f) auto

value "vars (VAR 1 AND VAR 2 EQ TOP)"

lemma
  assumes "tautology f"
  shows "satisfiable f"
  using assms
  using satisfiable_def tautology_def by auto

lemma
  shows "tautology TOP"
  using satisfies_def tautology_def by auto

lemma 
  shows "\<not> satisfiable BOT"
  by (simp add: satisfiable_def satisfies_def)

definition satisfies_set :: "valuation \<Rightarrow> prop_form set \<Rightarrow> bool" (infix "|=\<^sub>s" 120) where
"v |=\<^sub>s \<Gamma> \<longleftrightarrow> (\<forall> f \<in> \<Gamma>. v |= f)"

definition satisfiable_set :: "prop_form set \<Rightarrow> bool" where
"satisfiable_set \<Gamma> \<longleftrightarrow> (\<exists> v. v |=\<^sub>s \<Gamma>)"

lemma 
  assumes "satisfiable_set \<Gamma>" "tautology f"
  shows "satisfiable_set (\<Gamma> \<union> {f})"
  using assms
  by (simp add: satisfiable_set_def satisfies_set_def tautology_def)

lemma
  assumes "\<not> satisfiable_set \<Gamma>"
  shows "\<not> satisfiable_set (\<Gamma> \<union> {f})"
  using assms
  by (simp add: satisfiable_set_def satisfies_set_def)

lemma
  assumes "\<not> satisfiable_set \<Gamma>" "tautology f"
  shows "\<not> satisfiable_set (\<Gamma> - {f})"
  using assms
  by (metis Diff_empty Diff_insert0 insertE insert_Diff satisfiable_set_def satisfies_set_def tautology_def)

definition equiv :: "prop_form \<Rightarrow> prop_form \<Rightarrow> bool" (infix "\<equiv>\<^sub>e" 120) where
"equiv f1 f2 \<longleftrightarrow> (\<forall> v. Iv v f1 \<longleftrightarrow> Iv v f2)"

lemma
  shows "f1 \<equiv>\<^sub>e f2 \<longleftrightarrow> tautology (f1 EQ f2)"
  by (simp add: equiv_def satisfies_def tautology_def)

lemma
  shows "equiv (NOT (NOT f)) f"
  by (simp add: equiv_def)

definition entails :: "prop_form \<Rightarrow> prop_form \<Rightarrow> bool" (infix "|=\<^sub>e" 120) where
  "f1 |=\<^sub>e f2 \<longleftrightarrow> (\<forall> v. v |= f1 \<longrightarrow> v |= f2)"

lemma
  assumes "f1 |=\<^sub>e f2" "f2 |=\<^sub>e f1"
  shows "f1 \<equiv>\<^sub>e f2"
  using assms
  using entails_def equiv_def
  by (meson satisfies_def)

lemma
  shows "f1 |=\<^sub>e f2 \<longleftrightarrow> tautology (f1 IMP f2)"
  using entails_def tautology_def satisfies_def
  by auto

primrec subst :: "nat \<Rightarrow> prop_form \<Rightarrow> prop_form \<Rightarrow> prop_form" where
    "subst p f BOT = BOT"
  | "subst p f TOP = TOP"
  | "subst p f (VAR q) = (if p = q then f else VAR q)"
  | "subst p f (NOT f') = NOT (subst p f f')"
  | "subst p f (f1 AND f2) = subst p f f1 AND subst p f f2"
  | "subst p f (f1 OR f2) = subst p f f1 OR subst p f f2"
  | "subst p f (f1 IMP f2) = subst p f f1 IMP subst p f f2"
  | "subst p f (f1 EQ f2) = subst p f f1 EQ subst p f f2"

value "let p = VAR 0; 
           q = VAR 1;
           f = (p AND q) IMP (p OR q)
       in subst 0 TOP f"

lemma vars_subst:
  shows "vars (subst p f f') = (if p \<in> vars f' then vars f' - {p} \<union> vars f else vars f')"
  by (induction f') auto

lemma subst_TOP:
  assumes "v p = True"
  shows "v |= f \<longleftrightarrow> v (p := x) |= (subst p TOP f)"
  using assms 
  by (induction f) (auto simp add: satisfies_def)

lemma subst_BOT:
  assumes "v p = False"
  shows "v |= f \<longleftrightarrow> v (p := x) |= (subst p BOT f)"
  using assms
  by (induction f) (auto simp add: satisfies_def)

lemma "satisfiable f \<longleftrightarrow> satisfiable (subst p TOP f) \<or> satisfiable (subst p BOT f)"
  using satisfiable_def satisfies_def
  using subst_TOP subst_BOT
  by (metis fun_upd_idem_iff fun_upd_upd)

lemma "tautology f \<longleftrightarrow> tautology (subst p TOP f) \<and> tautology (subst p BOT f)"
  using tautology_def
  using subst_TOP subst_BOT
  by (metis fun_upd_idem_iff fun_upd_upd)

fun simplify_const_NOT :: "prop_form \<Rightarrow> prop_form"
  where
    "simplify_const_NOT (NOT f) = (if f = TOP then BOT else if f = BOT then TOP else NOT f)"
  | "simplify_const_NOT f = f"

lemma [simp]:
  "simplify_const_NOT (NOT TOP) = BOT"
  "simplify_const_NOT (NOT BOT) = TOP"
  by auto

lemma simplify_const_NOT [simp]:
  shows "v |= (simplify_const_NOT f) \<longleftrightarrow> v |= f"
  by (induction f rule: simplify_const_NOT.induct) auto

lemma simplify_const_NOT_equiv:
  shows "(simplify_const_NOT f) \<equiv>\<^sub>e f"
  using equiv_def satisfies_def simplify_const_NOT 
  by auto

fun simplify_const_AND :: "prop_form \<Rightarrow> prop_form"
  where
    "simplify_const_AND (f1 AND f2) = 
      (if f1 = TOP then f2
       else if f2 = BOT then BOT
       else if f2 = TOP then f1
       else if f1 = BOT then BOT
       else (f1 AND f2))"
  | "simplify_const_AND f = f"

fun simplify_const_OR :: "prop_form \<Rightarrow> prop_form"
  where
    "simplify_const_OR (f1 OR f2) =
      (if f2 = TOP then TOP
       else if f2 = BOT then f1
       else if f1 = TOP then TOP
       else if f1 = BOT then f2
       else (f1 OR f2))"
  | "simplify_const_OR f = f"

fun simplify_const_IMP :: "prop_form \<Rightarrow> prop_form"
  where
    "simplify_const_IMP (f1 IMP f2) =
      (if f1 = BOT then TOP
       else if f1 = TOP then f2
       else if f2 = TOP then TOP
       else if f2 = BOT then simplify_const_NOT (NOT f1)
       else (f1 IMP f2))"
  | "simplify_const_IMP f = f"

fun simplify_const_EQ :: "prop_form \<Rightarrow> prop_form"
  where
    "simplify_const_EQ (f1 EQ f2) =
      (if f1 = TOP then f2
       else if f2 = TOP then f1
       else if f1 = BOT then simplify_const_NOT (NOT f2)
       else if f2 = BOT then simplify_const_NOT (NOT f1)
       else (f1 EQ f2))"
  | "simplify_const_EQ f = f"

primrec simplify_const :: "prop_form \<Rightarrow> prop_form"
  where
    "simplify_const TOP = TOP"
  | "simplify_const BOT = BOT"
  | "simplify_const (VAR n) = VAR n"
  | "simplify_const (NOT f) = simplify_const_NOT (NOT (simplify_const f))"
  | "simplify_const (f1 AND f2) = simplify_const_AND ((simplify_const f1) AND (simplify_const f2))"
  | "simplify_const (f1 OR f2) = simplify_const_OR ((simplify_const f1) OR (simplify_const f2))"
  | "simplify_const (f1 IMP f2) = simplify_const_IMP ((simplify_const f1) IMP (simplify_const f2))"
  | "simplify_const (f1 EQ f2) = simplify_const_EQ ((simplify_const f1) EQ (simplify_const f2))"


lemma simplify_const [simp]:
  shows "v |= simplify_const f \<longleftrightarrow> v |= f"
  sorry

lemma simplify_const_equiv:
  shows "simplify_const f \<equiv>\<^sub>e f"
  sorry

lemma simplify_const_satisfiable [simp]:
  shows "satisfiable (simplify_const f) \<longleftrightarrow> satisfiable f"
  sorry

lemma simplify_const_tautology [simp]:
  shows "tautology (simplify_const f) \<longleftrightarrow> tautology f"
  sorry

lemma vars_simp_const [simp]:
  shows "vars (simplify_const f) \<subseteq> vars f"
  sorry

lemma card_vars_simp_const [simp]:
  shows "card (vars (simplify_const f)) \<le> card (vars f)"
  by (simp add: card_mono finite_vars)

lemma vars_simp_const_nonempty:
  assumes "(simplify_const f) \<noteq> TOP" "(simplify_const f) \<noteq> BOT"
  shows "vars (simplify_const f) \<noteq> {}"
  using assms
  apply (induction f)
         apply auto
     apply presburger+
  done


end