theory IsarProofs
  imports Main

begin

find_theorems "_ \<union> (_ \<union> _)"

lemma "A \<inter> (B \<union> C) = (A \<inter> B) \<union> (A \<inter> C)"
  by auto

lemma "- (A \<union> B) = - A \<inter> - B"
  by auto

lemma "A = B \<longleftrightarrow> A \<subseteq> B \<and> B \<subseteq> A"
  by auto

lemma "A = B \<longleftrightarrow> (\<forall> x. x \<in> A \<longleftrightarrow> x \<in> B)"
  by auto

term "(\<inter>)"
term "(\<in>)"
term "{1, 2, 3}"
term "{1::nat, 2, 3}"

lemma "- (A \<union> B) = - A \<inter> - B"
proof
  show "- (A \<union> B) \<subseteq> - A \<inter> - B"
  proof
    fix x
    assume "x \<in> - (A \<union> B)"
    then have "x \<notin> A \<union> B" by simp
    then have "x \<notin> A \<and> x \<notin> B" by simp
    then have "x \<in> -A \<and> x \<in> -B" by simp
    then show " x \<in> - A \<inter> - B" by simp
  qed
next
  show "- A \<inter> - B \<subseteq> - (A \<union> B)"
  proof
    fix x
    assume "x \<in> -A \<inter> -B"
    then have "x \<in> -A \<and> x \<in> -B" by simp
    then have "x \<notin> A \<and> x \<notin> B" by simp
    then have "x \<notin> (A \<union> B)" by simp
    then show "x \<in> -(A \<union> B)" by simp
    qed
  qed

lemma "\<not> (A \<or> B) \<longleftrightarrow> \<not> A \<and> \<not> B"
(is "?levo \<longleftrightarrow> ?desno")
proof
  assume "?levo"
  show "?desno"
  proof
    show "\<not> A"
    proof
      assume "A"
      from this have "A \<or> B" by simp
      from this and \<open>?levo\<close> show "False" by simp
    qed
    show "\<not> B"
    proof
      assume "B"
      from this have "A \<or> B" by simp
      from this and \<open>?levo\<close> show False by simp
    qed
  qed
next
  assume "?desno"
  from this have "\<not>A" "\<not>B" by auto
  show "?levo"
  proof
    assume "A \<or> B"
    from this
    show False
    proof
      assume "A"
      from this and \<open>\<not>A\<close> 
      show False by simp
    next
      assume "B"
      from this and \<open>\<not>B\<close>
      show False by simp
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
    then have "x \<in> B \<or> x \<in> A" by auto
    then show "x \<in> B \<union> A" by simp
  qed
next
  show "B \<union> A \<subseteq> A \<union> B"
  proof
    fix x
    assume "x \<in> B \<union> A"
    then have "x \<in> B \<or> x \<in> A" by simp
    then have "x \<in> A \<or> x \<in> B" by auto
    then show "x \<in> A \<union> B" by simp
  qed
qed

lemma "A \<union> (B \<inter> C) = (A \<union> B) \<inter> (A \<union> C)" 
(is "?levo = ?desno")
proof
  show "?levo \<subseteq> ?desno"
  proof
    fix x
    assume "x \<in> ?levo"
    from this have "x \<in> A \<or> x \<in> B \<inter> C" by simp
    from this show "x \<in> ?desno"
    proof
      assume "x \<in> A"
      from this have "x \<in> A \<union> B \<and> x \<in> A \<union> C" by simp
      from this show "x \<in> ?desno" by simp
    next
      assume "x \<in> B \<inter> C"
      from this have "x \<in> B \<and> x \<in> C" by simp
      from this have "x \<in> A \<union> B \<and> x \<in> A \<union> C" by simp
      from this show "x \<in> ?desno" by simp
    qed
  qed
next
  show "?desno \<subseteq> ?levo"
  proof 
    fix x
    assume "x \<in> ?desno"
    from this have "x \<in> A \<union> B \<and> x \<in> A \<union> C" by simp
    have "x \<in> A \<or> x \<notin> A" by simp
    from this show "x \<in> ?levo"
    proof
      assume "x \<in> A"
      from this show "x \<in> ?levo" by simp
    next
      assume "x \<notin> A"
      from this and \<open>x \<in> A \<union> B \<and> x \<in> A \<union> C\<close> have "x \<in> B \<and> x \<in> C" by simp
      from this have "x \<in> B \<inter> C" by simp
      from this show "x \<in> ?levo" by simp 
    qed
  qed
qed


lemma "A \<inter> (B \<union> C) = (A \<inter> B) \<union> (A \<inter> C)" (is "?levo = ?desno")
proof
  show "?levo \<subseteq> ?desno"
  proof
    fix x
    assume "x \<in> ?levo"
    then have "x \<in> A" "x \<in> B \<union> C" by auto
    then have "x \<in> B \<or> x \<in> C" by simp
    then show "x \<in> ?desno" 
    proof
      assume "x \<in> B"
      from this and \<open>x \<in> A\<close> have "x \<in> A \<inter> B" by simp
      from this show "x \<in> ?desno" by simp
    next
      assume "x \<in> C"
      from this and \<open>x \<in> A\<close> have "x \<in> A \<inter> C" by simp
      from this show "x \<in> ?desno" by simp
    qed
  qed
next
  show "?desno \<subseteq> ?levo"
  proof
    fix x
    assume "x \<in> ?desno"
    from this have "(x \<in> A \<inter> B) \<or> (x \<in> A \<inter> C)" by simp
    then show "x \<in> ?levo" 
    proof
      assume "x \<in> A \<inter> B"
      then have "x \<in> A \<and> x \<in> B" by simp
      then have "x \<in> A \<and> (x \<in> B \<or> x \<in> C)" by simp
      then have "x \<in> A \<and> (x \<in> B \<union> C)" by simp
      then show "x \<in> ?levo" by simp
    next
      assume "x \<in> A \<inter> C"
      then have "x \<in> A \<and> x \<in> C" by simp
      then have "x \<in> A \<and> (x \<in> B \<or> x \<in> C)" by simp
      then have "x \<in> A \<and> (x \<in> B \<union> C)" by simp
      then show "x \<in> ?levo" by simp
    qed
  qed
qed

lemma "A - (B \<inter> C ) = (A - B) \<union> (A - C )" (is "?left = ?right")
proof
  show "?left \<subseteq> ?right"
  proof
    fix x
    assume "x \<in> ?left"
    then have "x \<in> A" "x \<notin> B \<inter> C" by auto
    then have "x \<notin> B \<or> x \<notin> C" by simp
    then show "x \<in> ?right"
    proof
      assume "x \<notin> B"
      from this and \<open>x \<in> A\<close> have "x \<in> A - B" by simp
      from this show "x \<in> ?right" by simp
    next
      assume "x \<notin> C"
      from this and \<open>x \<in> A\<close> have "x \<in> A - C" by simp
      from this show "x \<in> ?right" by simp
    qed
  qed
  next
    show "?right \<subseteq> ?left"
    proof
      fix x
      assume "x \<in> ?right"
      from this have "x \<in> A - B \<or> x \<in> A - C" by simp
      from this show "x \<in> ?left"
      proof
        assume "x \<in> A - B"
        from this have "x \<in> A \<and> x \<notin> B" by simp
        from this have "x \<in> A \<and> x \<notin> B \<inter> C" by simp
        from this show "x \<in> ?left" by simp
      next
        assume "x \<in> A - C"
        from this have "x \<in> A \<and> x \<notin> C" by simp
        from this have "x \<in> A \<and> x \<notin> B \<inter> C" by simp
        from this show "x \<in> ?left" by simp
      qed
    qed
qed

end