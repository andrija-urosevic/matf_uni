theory Funkcije
  imports Main

begin

term inj
term surj
term bij

thm inj_def
thm surj_def
thm bij_def

lemma "f = g \<longleftrightarrow> (\<forall> x. f x = g x)"
  by auto

lemma "bij f \<longleftrightarrow> inj f \<and> surj f"
  by (auto simp add: bij_def)

thm image_def
thm vimage_def

lemma "f ` (A \<union> B) = f ` A \<union> f ` B"
proof
  show "f ` (A \<union> B) \<subseteq> f ` A \<union> f ` B"
  proof
    fix y
    assume "y \<in> f ` (A \<union> B)"
    then have "\<exists> x. x \<in> A \<union> B \<and> y = f x" by auto
    then obtain x where "x \<in> A \<union> B" "y = f x" by auto
    then have "x \<in> A \<or> x \<in> B" by simp
    then show "y \<in> f ` A \<union> f ` B"
    proof
      assume "x \<in> A"
      then have "f x \<in> f ` A" by simp
      with \<open>y = f x\<close> have "y \<in> f ` A" by simp
      then show "y \<in> f ` A \<union> f ` B" by simp
    next
      assume "x \<in> B"
      then have "f x \<in> f ` B" by simp
      with \<open>y = f x\<close> have "y \<in> f ` B" by simp
      then show "y \<in> f ` A \<union> f ` B" by simp
    qed
  qed
next
  show "f ` A \<union> f ` B \<subseteq> f ` (A \<union> B)"
  proof
    fix y
    assume "y \<in> f ` A \<union> f ` B"
    then have "y \<in> f ` A \<or> y \<in> f ` B" by simp
    then show "y \<in> f ` (A \<union> B)"
    proof
      assume "y \<in> f ` A"
      then have "\<exists> x. x \<in> A \<and> y = f x" by auto
      then obtain x where "x \<in> A" "y = f x" by auto
      then have "x \<in> A \<union> B" by simp
      then have "f x \<in> f ` (A \<union> B)" by simp
      with \<open>y = f x\<close> show "y \<in> f ` (A \<union> B)" by simp
    next
      assume "y \<in> f ` B"
      then have "\<exists> x. x \<in> B \<and> y = f x" by auto
      then obtain x where "x \<in> B" "y = f x" by auto
      then have "x \<in> A \<union> B" by simp
      then have "f x \<in> f ` (A \<union> B)" by simp
      with \<open>y = f x\<close> show "y \<in> f ` (A \<union> B)" by simp
    qed
  qed
qed

lemma
  assumes "inj f"
  shows "f ` (A \<inter> B) = f ` A \<inter> f ` B"
proof
  show "f ` (A \<inter> B) \<subseteq> f ` A \<inter> f ` B"
  proof
    fix y
    assume "y \<in> f ` (A \<inter> B)"
    then have "\<exists> x. x \<in> A \<inter> B \<and> y = f x" by auto
    then obtain x where "x \<in> A \<inter> B" "y = f x" by auto
    then have "x \<in> A \<and> x \<in> B" by simp
    then have "f x \<in> f ` A \<and> f x \<in> f ` B" by simp
    with \<open>y = f x\<close> show "y \<in> f ` A \<inter> f ` B" by simp
  qed
next
  show "f ` A \<inter> f ` B \<subseteq> f ` (A \<inter> B)"
  proof
    fix y
    assume "y \<in> f ` A \<inter> f ` B"
    then have "y \<in> f ` A" "y \<in> f ` B" by auto
    from \<open>y \<in> f ` A\<close> obtain xa where "xa \<in> A" "y = f xa" by auto
    moreover
    from \<open>y \<in> f ` B\<close> obtain xb where "xb \<in> B" "y = f xb" by auto
    ultimately
    have "xa = xb" using \<open>inj f\<close> by (simp add: inj_def)
    with \<open>xb \<in> B\<close> have "xa \<in> B" by simp
    with \<open>xa \<in> A\<close> have "xa \<in> A \<inter> B" by simp
    then have "f xa \<in> f ` (A \<inter> B)" by simp
    with \<open>y = f xa\<close> show "y \<in> f ` (A \<inter> B)" by simp
  qed
qed

end