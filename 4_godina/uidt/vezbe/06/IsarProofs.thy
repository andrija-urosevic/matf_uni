theory IsarProofs
  imports Main

begin

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

lemma "A \<union> (B \<inter> C) = (A \<union> B) \<inter> (A \<union> C)" (is "?levo = ?desno")
proof
  show "?levo \<subseteq> ?desno"
  proof
    fix x
    assume "x \<in> ?levo"
    then have "x \<in> A \<or> x \<in> B \<inter> C" by simp
    then show "x \<in> ?desno"
    proof
      assume "x \<in> A"
      then have "x \<in> A \<union> B \<and> x \<in> A \<union> C" by simp
      then show "x \<in> ?desno" by simp
    next
      assume "x \<in> B \<inter> C"
      then have "x \<in> B \<and> x \<in> C" by simp
      then have "x \<in> A \<union> B \<and> x \<in> A \<union> C" by simp
      then show "x \<in> ?desno" by simp
    qed
  qed
next
  show "?desno \<subseteq> ?levo"
  proof
    fix x
    assume "x \<in> ?desno"
    then have "x \<in> A \<union> B \<and> x \<in> A \<union> C" by simp
    then have "x \<in> A \<union> B" "x \<in> A \<union> C" by auto
    have "x \<in> A \<or> x \<notin> A" by simp 
    then show "x \<in> ?levo"
    proof
      assume "x \<in> A"
      then show "x \<in> ?levo" by simp
    next
      assume "x \<notin> A"
      from this \<open>x \<in> A \<union> B\<close> have 1:"x \<in> B" by simp
      from \<open>x \<notin> A\<close> \<open>x \<in> A \<union> C\<close> have 2:"x \<in> C" by simp
      from 1 2 have "x \<in> B \<inter> C" by simp
      then show "x \<in> ?levo" by simp
    qed
  qed
qed

thm inj_def
thm surj_def
thm bij_def
thm image_def
thm vimage_def

lemma "f ` (A \<union> B) = f ` A \<union> f ` B"
proof
  show "f ` (A \<union> B) \<subseteq> f ` A \<union> f ` B"
  proof
    fix y
    assume "y \<in> f ` (A \<union> B)"
    then have "\<exists> x. x \<in> A \<union> B \<and> f x = y" by auto
    then obtain x where "x \<in> A \<union> B" "f x = y" by auto
    then have "x \<in> A \<or> x \<in> B" by auto
    then show "y \<in> f ` A \<union> f ` B"
    proof
      assume "x \<in> A"
      then have "f x \<in> f ` A" by auto
      from this \<open>f x = y\<close> have "y \<in> f ` A" by auto
      then show "y \<in> f ` A \<union> f ` B" by auto
    next
      assume "x \<in> B"
      then have "f x \<in> f ` B" by auto
      from this \<open>f x = y\<close> have "y \<in> f ` B" by auto
      then show "y \<in> f ` A \<union> f ` B" by auto
    qed
  qed
next
  show "f ` A \<union> f ` B \<subseteq> f ` (A \<union> B)"
  proof
    fix y
    assume "y \<in> f ` A \<union> f ` B"
    then have "y \<in> f ` A \<or> y \<in> f ` B" by auto
    then show "y \<in> f ` (A \<union> B)"
    proof
      assume "y \<in> f ` A"
      then have "\<exists> x. x \<in> A \<and> f x = y" by auto
      then obtain x where \<open>x \<in> A\<close> \<open>f x = y\<close> by auto
      then have "x \<in> A \<union> B" by auto
      then have "f x \<in> f ` (A \<union> B)" by auto
      from this \<open>f x = y\<close> show "y \<in> f ` (A \<union> B)" by auto
    next
      assume "y \<in> f ` B"
      then have "\<exists> x. x \<in> B \<and> f x = y" by auto
      then obtain x where \<open>x \<in> B\<close> \<open>f x = y\<close> by auto
      then have "x \<in> A \<union> B" by auto
      then have "f x \<in> f ` (A \<union> B)" by auto
      from this \<open>f x = y\<close> show "y \<in> f ` (A \<union> B)" by auto
    qed
  qed
qed

end