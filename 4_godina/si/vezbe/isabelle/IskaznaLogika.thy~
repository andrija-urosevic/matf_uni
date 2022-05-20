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
  shows "Iv v (f1 AND f2) \<longleftrightarrow> (if Iv v f1 \<and> Iv v f2 then True else False)"
  by auto

definition satisfies :: "valuation \<Rightarrow> prop_form \<Rightarrow> bool" (infix "|=" 50) where
  "satisfies v f \<longleftrightarrow> Iv v f = True"

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

lemma "vars (subst p f f') = (if p \<in> vars f' then vars f' - {p} \<union> vars f else vars f')"
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
  sorry

end