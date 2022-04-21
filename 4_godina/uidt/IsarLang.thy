theory IsarLang
  imports Main

begin

lemma "\<not> (A \<or> B) \<longleftrightarrow> \<not> A \<and> \<not> B"
proof
  assume "\<not> (A \<or> B)"
  show "\<not> A \<and> \<not> B"
  proof
    show "\<not> A"
    proof
      assume "A"
      hence "A \<or> B" by (rule disjI1)
      show False
        using \<open>A \<or> B\<close> \<open>\<not> (A \<or> B)\<close>
        by - (erule notE, assumption)
    qed
  next
    show "\<not> B"
    proof
      assume "B"
      hence "A \<or> B" by (rule disjI2)
      with \<open>\<not> (A \<or> B)\<close> show False
        by - (erule notE, assumption)
    qed
  qed
next
  assume "\<not> A \<and> \<not> B"
  hence "\<not> A" "\<not> B" by auto
  show "\<not> (A \<or> B)"
  proof
    assume "A \<or> B"
    then show False
    proof
      assume "A"
      from this \<open>\<not> A\<close>
      show False
        by - (erule notE, assumption)
    next
      assume "B"
      from this \<open>\<not> B\<close>
      show False
        by - (erule notE, assumption)
    qed
  qed
qed

lemma "\<not> (A \<and> B) \<longleftrightarrow> \<not>A \<or> \<not>B" (is "?l \<longleftrightarrow> ?d")
proof
  assume "?l"
  show "?d"
  proof (rule ccontr)
    assume "\<not> (\<not> A \<or> \<not> B)"
    have "A \<and> B"
    proof
      show "A"
      proof (rule ccontr)
        assume "\<not> A"
        then have "\<not>A \<or> \<not>B" by (rule disjI1)
        with \<open>\<not> (\<not>A \<or> \<not>B)\<close> 
        show False by auto
      qed
    next
      show "B"
      proof (rule ccontr)
        assume "\<not> B"
        then have "\<not>A \<or> \<not>B" by (rule disjI2)
        with \<open>\<not> (\<not>A \<or> \<not>B)\<close> 
        show False by auto
      qed
    qed
      with \<open>\<not> (A \<and> B)\<close> 
      show False by auto
    qed
  next
    assume "?d"
    show "?l"
      sorry
  qed


lemma 
  assumes sim: "\<forall> x y. R x y \<longrightarrow> R y x"
  assumes tranz: "\<forall> x y z. R x y \<and> R y z \<longrightarrow> R x z"
  assumes post: "\<forall> x. \<exists> y. R x y"
  shows "\<forall> x. R x x"
proof
  fix x
  show "R x x"
  proof-
    from post obtain y where "R x y" by auto
    with sim have "R y x" by auto
    with tranz show "?thesis" by auto
  qed
qed

lemma
  assumes *: "\<forall>x. (\<exists>y. voli x y) \<longrightarrow> (\<forall>z. voli z x)"
  assumes "voli Dzon Meri"
  shows "voli Jago Otelo"
proof-
  have "voli Otelo Dzon" using assms by auto
  with * show ?thesis by auto
qed

end