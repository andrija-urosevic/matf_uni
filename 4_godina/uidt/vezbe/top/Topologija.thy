theory Topologija
  imports "Complex_Main" "HOL-Library.Code_Target_Nat" "HOL-Library.Multiset"

begin

locale topological_space =
  fixes X :: "'a set"
  fixes \<tau> :: "'a set set"
  assumes subsets: "\<And> S. S \<in> \<tau> \<Longrightarrow> S \<subseteq> X"
  assumes univ: "X \<in> \<tau>"
  assumes empty: "{} \<in> \<tau>"
  assumes inter: "\<And> S1 S2. \<lbrakk>S1 \<in> \<tau>; S2 \<in> \<tau>\<rbrakk> \<Longrightarrow> S1 \<inter> S2 \<in> \<tau>"
  assumes union: "\<And> \<tau>'. \<lbrakk>\<tau>' \<noteq> {}; \<tau>' \<subseteq> \<tau>\<rbrakk> \<Longrightarrow> \<Union> \<tau>' \<in> \<tau>"
begin

abbreviation open_set :: "'a set \<Rightarrow> bool"
  where
    "open_set S \<equiv> S \<in> \<tau>"

term finite
thm finite.induct

lemma inter_finite:
  assumes "finite \<tau>'" "\<tau>' \<noteq> {}" "\<forall> S \<in> \<tau>'. open_set S"
  shows "open_set (\<Inter> \<tau>')"
  using assms
proof (induction "\<tau>'" rule: finite.induct)
  case emptyI
  then show ?case by simp
next
  case (insertI A a)
  show ?case
  proof (cases "A = {}")
    case True
    then show ?thesis using insertI.prems(2) by simp
  next
    case False
    then show ?thesis using insertI inter by simp
  qed
qed

definition closed_set :: "'a set \<Rightarrow> bool"
  where
    "closed_set S \<longleftrightarrow> open_set (X - S)"

lemma closed_empty:
  shows "closed_set {}"
  unfolding closed_set_def
  using univ by auto

lemma closed_inter:
  assumes "closed_set S1" "closed_set S2"
  shows "closed_set (S1 \<inter> S2)"
  using assms union[of "{X - S1, X - S2}"]
  unfolding closed_set_def
  by (simp add: Diff_Int)

lemma closed_inter_finite:
  assumes "finite \<tau>'" "\<tau>' \<noteq> {}" "\<forall> S \<in> \<tau>'. closed_set S"
  shows "closed_set (\<Inter> \<tau>')"
proof -
  have "X - (\<Inter> \<tau>') = \<Union> {X - S | S . S \<in> \<tau>'}"
    using assms
    by auto
  thus ?thesis
    using assms union[of "{X - S | S . S \<in> \<tau>'}"]
    unfolding closed_set_def
    by auto
qed

end