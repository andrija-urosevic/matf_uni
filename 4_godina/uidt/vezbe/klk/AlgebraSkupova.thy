theory AlgebraSkupova
  imports Main

begin

lemma "-(A \<union> B) = - A \<inter> - B"
proof
  show "- (A \<union> B) \<subseteq> - A \<inter> - B"
  proof
    fix x
    assume "x \<in> - (A \<union> B)"
    then have "x \<notin> A \<union> B" by simp
    then have "x \<notin> A \<and> x \<notin> B" by simp
    then have "x \<in> - A \<and> x \<in> - B" by simp
    then show "x \<in> - A \<inter> - B" by simp
  qed
next
  show "- A \<inter> - B \<subseteq> - (A \<union> B)"
  proof
    fix x
    assume "x \<in> - A \<inter> - B"
    then have "x \<in> - A \<and> x \<in> - B" by simp
    then have "x \<notin> A \<and> x \<notin> B" by simp
    then have "x \<notin> A \<union> B" by simp
    then show "x \<in> - (A \<union> B)" by simp
  qed
qed

lemma "\<not> (A \<or> B) \<longleftrightarrow> \<not> A \<and> \<not> B"
proof
  assume "\<not> (A \<or> B)"
  show "\<not> A \<and> \<not> B"
  proof
    show "\<not> A"
    proof
      assume A
      then have "A \<or> B" by simp
      with \<open>\<not> (A \<or> B)\<close> show False by simp
    qed
  next
    show "\<not> B"
    proof
      assume B
      then have "A \<or> B" by simp
      with \<open>\<not> (A \<or> B)\<close> show False by simp
    qed
  qed
next
  assume "\<not> A \<and> \<not> B"
  from this have "\<not> A" "\<not> B" by auto
  show "\<not> (A \<or> B)"
  proof
    assume "A \<or> B"
    then show False
    proof
      assume A
      with \<open>\<not> A\<close> show False by simp
    next
      assume B
      with \<open>\<not> B\<close> show False by simp
    qed
  qed
qed

lemma "A \<union> B = B \<union> A"
proof
  show "A \<union> B \<subseteq> B \<union> A"
  proof
    fix x
    assume "x \<in> A \<union> B"
    then have "x \<in> A \<or> x \<in> B" by simp
    then show "x \<in> B \<union> A"
    proof
      assume "x \<in> A"
      then show "x \<in> B \<union> A" by simp
    next
      assume "x \<in> B"
      then show "x \<in> B \<union> A" by simp
    qed
  qed
next
  show "B \<union> A \<subseteq> A \<union> B"
  proof
    fix x
    assume "x \<in> B \<union> A"
    then have "x \<in> B \<or> x \<in> A" by simp
    then show "x \<in> A \<union> B"
    proof
      assume "x \<in> B"
      then show "x \<in> A \<union> B" by simp
    next
      assume "x \<in> A"
      then show "x \<in> A \<union> B" by simp
    qed
  qed
qed

lemma "A \<inter> (B \<union> C) = (A \<inter> B) \<union> (A \<inter> C)"
proof
  show "A \<inter> (B \<union> C) \<subseteq> A \<inter> B \<union> A \<inter> C"
  proof
    fix x
    assume 1:"x \<in> A \<inter> (B \<union> C)"
    then have "x \<in> A" by simp
    from 1 have "x \<in> B \<union> C" by simp
    then have "x \<in> B \<or> x \<in> C" by simp
    then show "x \<in> (A \<inter> B) \<union> (A \<inter> C)"
    proof
      assume "x \<in> B"
      with \<open>x \<in> A\<close> have "x \<in> A \<inter> B" by simp
      then show "x \<in> (A \<inter> B) \<union> (A \<inter> C)" by simp
    next
      assume "x \<in> C"
      with \<open>x \<in> A\<close> have "x \<in> A \<inter> C" by simp
      then show "x \<in> (A \<inter> B) \<union> (A \<inter> C)" by simp
    qed
  qed
next
  show "A \<inter> B \<union> A \<inter> C \<subseteq> A \<inter> (B \<union> C)"
  proof
    fix x
    assume "x \<in> (A \<inter> B) \<union> (A \<inter> C)"
    then have "x \<in> (A \<inter> B) \<or> x \<in> (A \<inter> C)" by simp
    then show "x \<in> A \<inter> (B \<union> C)"
    proof
      assume "x \<in> A \<inter> B"
      then have "x \<in> A \<and> x \<in> B" by simp
      then have "x \<in> A \<and> x \<in> B \<union> C" by simp
      then show "x \<in> A \<inter> (B \<union> C)" by simp
    next
      assume "x \<in> A \<inter> C"
      then have "x \<in> A \<and> x \<in> C" by simp
      then have "x \<in> A \<and> x \<in> B \<union> C" by simp
      then show "x \<in> A \<inter> (B \<union> C)" by simp
    qed
  qed
qed

lemma "A \<union> (B \<inter> C) = (A \<union> B) \<inter> (A \<union> C)"
proof
  show "A \<union> B \<inter> C \<subseteq> (A \<union> B) \<inter> (A \<union> C)"
  proof
    fix x
    assume "x \<in> A \<union> B \<inter> C"
    then have "x \<in> A \<or> x \<in> B \<inter> C" by simp
    then show "x \<in> (A \<union> B) \<inter> (A \<union> C)"
    proof
      assume "x \<in> A"
      then have "x \<in> A \<union> B \<and> x \<in> A \<union> C" by simp
      then show "x \<in> (A \<union> B) \<inter> (A \<union> C)" by simp
    next
      assume "x \<in> B \<inter> C"
      then have "x \<in> B \<and> x \<in> C" by simp
      then have "x \<in> A \<union> B \<and> x \<in> A \<union> C" by simp
      then show "x \<in> (A \<union> B) \<inter> (A \<union> C)" by simp
    qed
  qed
next
  show "(A \<union> B) \<inter> (A \<union> C) \<subseteq> A \<union> B \<inter> C"
  proof
    fix x
    assume "x \<in> (A \<union> B) \<inter> (A \<union> C)"
    then have "x \<in> A \<union> B \<and> x \<in> A \<union> C" by simp
    then show "x \<in> A \<union> B \<inter> C"
    proof
      assume 1:"x \<in> A \<union> B" "x \<in> A \<union> C"
      have "x \<in> A \<or> x \<notin> A" by simp
      then show "x \<in> A \<union> B \<inter> C"
      proof
        assume "x \<in> A"
        then show "x \<in> A \<union> B \<inter> C" by simp
      next
        assume "x \<notin> A"
        with 1 have "x \<in> B \<and> x \<in> C" by simp
        then have "x \<in> B \<inter> C" by simp
        then show "x \<in> A \<union> B \<inter> C" by simp
      qed
    qed
  qed
qed

lemma "A - (B \<inter> C) = (A - B) \<union> (A - C)"
proof
  show "A - B \<inter> C \<subseteq> A - B \<union> (A - C)"
  proof
    fix x
    assume 1:"x \<in> A - B \<inter> C"
    then have "x \<in> A" by simp
    from 1 have "x \<notin> B \<inter> C" by simp
    then have "x \<notin> B \<or> x \<notin> C" by simp
    then show "x \<in> A - B \<union> (A - C)"
    proof
      assume "x \<notin> B"
      with \<open>x \<in> A\<close> have "x \<in> A - B" by simp
      then show "x \<in> A - B \<union> (A - C)" by simp
    next
      assume "x \<notin> C"
      with \<open>x \<in> A\<close> have "x \<in> A - C" by simp
      then show "x \<in> A - B \<union> (A - C)" by simp
    qed
  qed
next
  show "A - B \<union> (A - C) \<subseteq> A - B \<inter> C"
  proof
    fix x
    assume "x \<in> A - B \<union> (A - C)"
    then have "x \<in> A - B \<or> x \<in> A - C" by simp
    then show "x \<in> A - B \<inter> C"
    proof
      assume "x \<in> A - B"
      then have "x \<in> A \<and> x \<notin> B" by simp
      then have "x \<in> A \<and> x \<notin> B \<inter> C" by simp
      then show "x \<in> A - B \<inter> C" by simp
    next
      assume "x \<in> A - C"
      then have "x \<in> A \<and> x \<notin> C" by simp
      then have "x \<in> A \<and> x \<notin> B \<inter> C" by simp
      then show "x \<in> A - B \<inter> C" by simp
    qed
  qed
qed

lemma "A - (B - C) = (A - B) \<union> (A \<inter> C)"
proof
  show "A - (B - C) \<subseteq> A - B \<union> A \<inter> C"
  proof
    fix x
    assume 1:"x \<in> A - (B - C)"
    then have "x \<in> A" by simp
    from 1 have "x \<notin> B - C" by simp
    then have "x \<notin> B \<or> x \<notin> - C" by simp
    then have "x \<notin> B \<or> x \<in> C" by simp
    then show "x \<in> A - B \<union> A \<inter> C"
    proof
      assume "x \<notin> B"
      with \<open>x \<in> A\<close> have "x \<in> A - B" by simp
      then show "x \<in> A - B \<union> A \<inter> C" by simp
    next
      assume "x \<in> C"
      with \<open>x \<in> A\<close> have "x \<in> A \<inter> C" by simp
      then show "x \<in> A - B \<union> A \<inter> C" by simp
    qed
  qed
next
  show "A - B \<union> A \<inter> C \<subseteq> A - (B - C)"
  proof
    fix x
    assume "x \<in> A - B \<union> A \<inter> C"
    then have "x \<in> A - B \<or> x \<in> A \<inter> C" by simp
    then show "x \<in> A - (B - C)"
    proof
      assume "x \<in> A - B" 
      then have "x \<in> A \<and> x \<notin> B" by simp
      then have "x \<in> A \<and> x \<notin> B - C" by simp
      then show "x \<in> A - (B - C)" by simp
    next
      assume "x \<in> A \<inter> C"
      then have "x \<in> A \<and> x \<in> C" by simp
      then have "x \<in> A \<and> x \<notin> B - C" by simp
      then show "x \<in> A - (B - C)" by simp
    qed
  qed
qed


lemma "(A - B) \<inter> (C - D) = (A \<inter> C) - (B \<union> D)"
proof
  show "(A - B) \<inter> (C - D) \<subseteq> A \<inter> C - (B \<union> D)"
  proof
    fix x
    assume "x \<in> (A - B) \<inter> (C - D)"
    then have "x \<in> A - B \<and> x \<in> C - D" by simp
    then have "x \<in> A \<and> x \<notin> B \<and> x \<in> C \<and> x \<notin>  D" by simp
    then have "x \<in> A \<inter> C \<and> x \<notin> B \<union> D" by simp
    then show "x \<in> A \<inter> C - (B \<union> D)" by simp
  qed
next
  show "A \<inter> C - (B \<union> D) \<subseteq> (A - B) \<inter> (C - D)"
  proof
    fix x
    assume "x \<in> A \<inter> C - (B \<union> D)"
    then have "x \<in> A \<inter> C \<and> x \<notin> B \<union> D" by simp
    then have "x \<in> A \<and> x \<in> C \<and> x \<notin> B \<and> x \<notin> D" by simp
    then have "x \<in> A - B \<and> x \<in> C - D" by simp
    then show "x \<in> (A - B) \<inter> (C - D)" by simp
  qed
qed

end