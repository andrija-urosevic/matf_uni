theory MathLogic
  imports Main

begin

lemma 
  assumes "\<exists> x. P x"
  assumes "\<forall> x. P x \<longrightarrow> Q x"
  shows "\<exists> x. Q x"
proof -
  from \<open>\<exists> x. P x\<close> obtain x where 1:"P x" by (erule exE)
  from \<open>\<forall> x. P x \<longrightarrow> Q x\<close> have 2:"P x \<longrightarrow> Q x" by (erule_tac x="x" in allE)
  from 1 2 have "Q x" by simp
  then show "\<exists> x. Q x" by (rule_tac x="x" in exI)
qed

lemma 
  assumes "\<forall> c. covek c \<longrightarrow> smrtan c"
  assumes "\<forall> g. grk g \<longrightarrow> covek g"
  shows "\<forall> a. grk a \<longrightarrow> smrtan a"
proof
  fix Jorgos
  show "grk Jorgos \<longrightarrow> smrtan Jorgos"
  proof
    assume "grk Jorgos"
    with assms(2) have "covek Jorgos" by simp
    with assms(1) show "smrtan Jorgos" by simp
  qed
qed

lemma 
  assumes "\<exists> x. A x \<or> B x"
  shows "(\<exists> x. A x) \<or> (\<exists> x. B x)"
proof -
  from assms obtain x where "A x \<or> B x" by auto
  then show "(\<exists> x. A x) \<or> (\<exists> x. B x)"
  proof
    assume "A x"
    then have "\<exists> x. A x" by (rule exI)
    then show "(\<exists>x. A x) \<or> (\<exists>x. B x)" by simp
  next
    assume "B x"
    then have "\<exists> x. B x" by (rule exI)
    then show "(\<exists>x. A x) \<or> (\<exists>x. B x)" by simp
  qed
qed

lemma 
  assumes "\<forall> x. A x \<longrightarrow> \<not> B x"
  shows "\<not> (\<exists> x. A x \<and> B x)"
proof
  assume "\<exists>x. A x \<and> B x"
  then obtain x where "A x \<and> B x" by auto
  then have 1:"A x" "B x" by auto
  with assms have 2:"\<not> B x" by auto
  from 1 2 show False by auto
qed

lemma "\<not> (A \<and> B) \<longrightarrow> \<not> A \<or> \<not> B"
proof
  assume 2:"\<not> (A \<and> B)"
  show "\<not> A \<or> \<not> B"
  proof (rule ccontr)
    assume 1:"\<not> (\<not> A \<or> \<not> B)"
    have "A \<and> B"
    proof
      show A
      proof (rule ccontr)
        assume "\<not> A"
        then have "\<not> A \<or> \<not> B" by simp
        with 1 show False by simp
      qed
    next
      show B
      proof (rule ccontr)
        assume "\<not> B"
        then have "\<not> A \<or> \<not> B" by simp
        with 1 show False by simp
      qed
    qed
    with 2 show False by simp
  qed
qed

lemma
  assumes "(P \<longrightarrow> Q) \<longrightarrow> P"
  shows "P"
proof (rule ccontr)
  assume "\<not> P"
  have "P \<longrightarrow> Q"
  proof
    assume P
    with \<open>\<not> P\<close> show Q by simp
  qed 
  with assms have P by simp
  with \<open>\<not> P\<close> show False by simp
qed

lemma "P \<or> \<not> P"
proof (rule classical)
  assume 1:"\<not> (P \<or> \<not> P)"
  show "P \<or> \<not> P"
  proof
    show P
    proof (rule classical)
      assume "\<not> P"
      then have "P \<or> \<not> P" by simp
      with 1 have False by simp
      then show P by simp
    qed
  qed
qed

lemma Drunker's_Principle: "\<exists> x. (Drunk x \<longrightarrow> (\<forall> x. Drunk x))"
proof cases
  assume "\<forall> x. Drunk x"
  fix a
  from \<open>\<forall> x. Drunk x\<close> have "Drunk a" by auto
  then show ?thesis by auto
next
  assume "\<not> (\<forall> x. Drunk x)"
  then have "\<exists> x. \<not> Drunk x" by auto
  then obtain a where "\<not> Drunk a" by auto
  have "Drunk a \<longrightarrow> (\<forall> x. Drunk x)"
  proof
    assume "Drunk a"
    with \<open>\<not> Drunk a\<close> have False by auto
    then show "\<forall> x. Drunk x" by auto
  qed
  show ?thesis by auto
qed

lemma no_one_admits_knave:
  assumes "k \<longleftrightarrow> (k \<longleftrightarrow> yes)"
  shows "yes"
proof (cases "k")
  case True
  with assms have "k \<longleftrightarrow> yes" by simp
  with \<open>k\<close> show yes by simp
next
  case False
  with assms have "\<not> (k \<longleftrightarrow> yes)" by simp
  with \<open>\<not>k\<close> show yes by simp
qed

lemma no_one_admits_kneve':
  assumes "k \<longleftrightarrow> (k \<longleftrightarrow> yes)"
  shows "yes"
  using assms by blast

lemma Smullyan_1_1:
  assumes "kA \<longleftrightarrow> (kA \<longleftrightarrow> yesA)"
  assumes "kB \<longleftrightarrow> \<not> yesA"
  assumes "kC \<longleftrightarrow> \<not> kB"
  shows "kC"
proof -
  from assms(1) have yesA 
    by (auto simp add: no_one_admits_knave)
  with assms(2) have "\<not> kB" by auto
  with assms(3) show "kC" by auto
qed

end