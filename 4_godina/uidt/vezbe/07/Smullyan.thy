theory Smullyan
  imports Main

begin

lemma no_one_admits_kneves:
  assumes "k \<longleftrightarrow> (k \<longleftrightarrow> yes)"
  shows yes
proof (cases k)
  case True
  with assms have "k \<longleftrightarrow> yes" by simp
  with \<open>k\<close> show ?thesis by simp
next
  case False
  with assms have "\<not> (k \<longleftrightarrow> yes)" by simp
  then have "\<not> k \<longrightarrow> yes" by simp
  with \<open>\<not> k\<close> show ?thesis by simp  
qed

lemma Smullyan_1_1:
  assumes "kA \<longleftrightarrow> (kA \<longleftrightarrow> yesA)"
  assumes "kB \<longleftrightarrow> \<not> yesA"
  assumes "kC \<longleftrightarrow> \<not> kB"
  shows "kC"
proof -
  from assms(1) have yesA by (auto simp add: no_one_admits_kneves)
  with assms(2) have "\<not> kB" by simp
  with assms(3) show kC by simp
qed

definition exactly_two where
  "exactly_two A B C \<longleftrightarrow> ((A \<and> B) \<or> (A \<and> C) \<or> (B \<and> C)) \<and> \<not> (A \<and> B \<and> C)"

lemma Smullyan_1_2:
  assumes "kA \<longleftrightarrow> (exactly_two (\<not> kA) (\<not> kB)  (\<not> kC) \<longleftrightarrow> yesA)"
  assumes "kB \<longleftrightarrow> yesA"
  assumes "kC \<longleftrightarrow> \<not> kB"
  shows kC
proof (rule ccontr)
  assume "\<not> kC"
  with assms have kB yesA by auto 
  then show False
  proof (cases kA)
    case True
    with assms(1) \<open>yesA\<close> have "exactly_two (\<not> kA) (\<not> kB) (\<not> kC)" by auto
    with \<open>kA\<close> \<open>kB\<close> \<open>\<not> kC\<close> show False by (auto simp add: exactly_two_def)
  next
    case False
    with assms(1) \<open>yesA\<close> have "\<not> (exactly_two (\<not> kA) (\<not> kB) (\<not> kC))" by auto
    with \<open>\<not> kA\<close> \<open>kB\<close> \<open>\<not> kC\<close> show False by (auto simp add: exactly_two_def)
  qed    
qed

lemma Smullyan_1_2':
  assumes "kA \<longleftrightarrow> (exactly_two kA kB kC \<longleftrightarrow> yesA)"
  assumes "kB \<longleftrightarrow> yesA"
  assumes "kC \<longleftrightarrow> \<not> kB"
  shows "\<not> kC"
proof
  assume "kC"
  with assms have "\<not>kB" "\<not>yesA" by auto
  show False
  proof (cases kA)
    case True
    with assms(1) \<open>\<not> yesA\<close> have "\<not> exactly_two kA kB kC" by simp 
    with \<open>kA\<close> \<open>\<not> kB\<close> \<open>kC\<close> show False by (auto simp add: exactly_two_def)
  next
    case False
    with assms(1) \<open>\<not> yesA\<close> have "exactly_two kA kB kC" by simp
    with \<open>\<not> kA\<close> \<open>\<not> kB\<close> \<open>kC\<close> show False by (auto simp add: exactly_two_def)
  qed
qed

lemma Smullyan_1_3:
  assumes "kA \<longleftrightarrow> \<not> kA \<and> \<not> kB"
  shows "\<not> kA \<and> kB"
proof (cases kA)
  case True
  with assms have "\<not> kA \<and> \<not> kB" by simp
  with \<open>kA\<close> have False by simp
  then show ?thesis by simp
next
  case False
  with assms have "\<not> (\<not> kA \<and> \<not> kB)" by simp
  then have "kA \<or> kB" by simp
  with \<open>\<not> kA\<close> have "kB" by simp
  with \<open>\<not> kA\<close> show ?thesis by simp
qed

lemma Smullyan_1_4:
  assumes "kA \<longleftrightarrow> \<not> kA \<or> \<not> kB"
  shows "kA \<and> \<not> kB"
proof (cases kA)
  case True
  with assms have "\<not> kA \<or> \<not> kB" by simp
  with \<open>kA\<close> have "\<not> kB" by simp
  with \<open>kA\<close> show ?thesis by simp
next
  case False
  with assms have "\<not> (\<not> kA \<or> \<not> kB)" by simp
  then have "kA \<and> kB" by simp
  with \<open>\<not> kA\<close> have False by simp
  then show ?thesis by simp
qed

lemma Smullyan_1_5:
  assumes "kA \<longleftrightarrow> (kA \<longleftrightarrow> kB)"
  shows kB
proof (cases kA)
  case True
  with assms have "kA \<longleftrightarrow> kB" by simp
  with \<open>kA\<close> show ?thesis by simp
next
  case False
  with assms have "\<not> (kA \<longleftrightarrow> kB)" by simp
  then have "\<not> kA \<longrightarrow> kB" by simp
  with \<open>\<not> kA\<close> show ?thesis by simp
qed

lemma Smullyan_1_6:
  assumes "kA \<longleftrightarrow> (kB \<longleftrightarrow> yesA)"
  assumes "kB \<longleftrightarrow> (kA \<longleftrightarrow> yesB)"
  shows "yesA \<longleftrightarrow> yesB"
proof (cases kA)
  case True
  with assms(1) have "kB \<longleftrightarrow> yesA" by simp
  show ?thesis
  proof (cases kB)
    case True
    from assms(2) \<open>kB\<close> have "kA \<longleftrightarrow> yesB" by simp
    from \<open>kB \<longleftrightarrow> yesA\<close> \<open>kB\<close> have yesA by simp
    from \<open>kA \<longleftrightarrow> yesB\<close> \<open>kA\<close> have yesB by simp
    from \<open>yesA\<close> \<open>yesB\<close> show ?thesis by simp
  next
    case False
    from assms(2) \<open>\<not> kB\<close> have "\<not> (kA \<longleftrightarrow> yesB)" by simp
    from \<open>kB \<longleftrightarrow> yesA\<close> \<open>\<not> kB\<close> have "\<not> yesA" by simp
    from \<open>\<not> (kA \<longleftrightarrow> yesB)\<close> \<open>kA\<close> have "\<not> yesB" by simp
    from \<open>\<not> yesA\<close> \<open>\<not> yesB\<close> show ?thesis by simp
  qed
next
  case False
  with assms(1) have "\<not> (kB \<longleftrightarrow> yesA)" by simp
  show ?thesis
  proof (cases kB)
    case True
    from assms(2) \<open>kB\<close> have "kA \<longleftrightarrow> yesB" by simp
    from \<open>kA \<longleftrightarrow> yesB\<close> \<open>\<not> kA\<close> have "\<not> yesB" by simp
    from \<open>\<not> (kB \<longleftrightarrow> yesA)\<close> \<open>kB\<close> have "\<not> yesA" by simp
    from \<open>\<not> yesA\<close> \<open>\<not> yesB\<close> show ?thesis by simp     
  next      
    case False
    from assms(2) \<open>\<not> kB\<close> have "\<not> (kA \<longleftrightarrow> yesB)" by simp
    from \<open>\<not> (kA \<longleftrightarrow> yesB)\<close> \<open>\<not> kA\<close> have "yesB" by simp
    from \<open>\<not> (kB \<longleftrightarrow> yesA)\<close> \<open>\<not> kB\<close> have "yesA" by simp
    from \<open>yesA\<close> \<open>yesB\<close> show ?thesis by simp
  qed
qed

definition exactly_one where
  "exactly_one A B C \<longleftrightarrow> (A \<or> B \<or> C) \<and> \<not>(A \<and> B) \<and> 
\<not>(A \<and> C) \<and> \<not>(B \<and> C)"

lemma Smullyan_1_9:
  assumes "kA \<longleftrightarrow> exactly_one (\<not> kA) (\<not> kB) (\<not> kC)"
  assumes "kB \<longleftrightarrow> exactly_two (\<not> kA) (\<not> kB) (\<not> kC)"
  assumes "kC \<longleftrightarrow> \<not> kA \<and> \<not> kB \<and> \<not> kC"
  shows "\<not> kA \<and> kB \<and> \<not> kC"
proof (cases kC)
  case True
  with assms(3) have "\<not> kA" "\<not> kB" "\<not> kC" by auto
  from \<open>kC\<close> \<open>\<not> kC\<close> have False by simp
  then show ?thesis by simp
next
  case False
  with assms(3) have "\<not> (\<not> kA \<and> \<not> kB \<and> \<not> kC)" by simp
  then have "kA \<or> kB \<or> kC" by simp
  with \<open>\<not> kC\<close> have "kA \<or> kB" by simp
  then show ?thesis
  proof
    assume kA
    with assms(1) have "exactly_one (\<not> kA) (\<not> kB) (\<not> kC)" 
      by simp
    with \<open>kA\<close> \<open>\<not> kC\<close> have kB 
      by (auto simp add: exactly_one_def)
    with assms(2) have "exactly_two (\<not> kA) (\<not> kB) (\<not> kC)" 
      by simp
    with \<open>kA\<close> \<open>kB\<close> \<open>\<not> kC\<close> have False 
      by (auto simp add: exactly_two_def)
    then show ?thesis by simp
  next
    assume kB
    with assms(2) have "exactly_two (\<not> kA) (\<not> kB) (\<not> kC)" 
      by simp
    with \<open>kB\<close> \<open>\<not> kC\<close> have \<open>\<not> kA\<close> 
      by (auto simp add: exactly_two_def)
    from \<open>\<not> kA\<close> \<open>kB\<close> \<open>\<not> kC\<close> show ?thesis by simp
  qed
qed


lemma Smullyan_1_10:
  assumes "Og \<longleftrightarrow> \<not> chief_Og \<and> \<not> Bog"
  assumes "Bog \<longleftrightarrow> \<not> chief_Og \<and> Og"
  shows "chief_Og \<and> \<not> Bog \<and> \<not> Og"
  oops

lemma Smullyan_1_10':
  assumes "A \<longleftrightarrow> \<not> C \<and> \<not> B"
  assumes "B \<longleftrightarrow> \<not> C \<and> A"
  shows "C \<and> \<not> B \<and> \<not> A"
proof (cases A)
  case True
  with assms(1) have "\<not> C" "\<not> B" by auto
  with assms(2) have "\<not> (\<not> C \<and> A)" by simp
  then have "C \<or> \<not> A" by simp
  with \<open>A\<close> have C by simp
  with \<open>\<not> C\<close> have False by simp
  then show ?thesis by simp
next
  case False
  with assms(1) have "\<not> (\<not> C \<and> \<not> B)" by simp
  then have "C \<or> B" by simp
  then show ?thesis 
  proof
    assume C
    then have "C \<or> \<not>A" by simp
    then have "\<not> (\<not> C \<and> A)" by simp
    with assms(2) have "\<not> B" by simp
    from \<open>\<not> A\<close> \<open>\<not> B\<close> \<open>C\<close> show ?thesis by simp
  next
    assume B
    with assms(2) have "\<not> C" "A" by auto
    with assms(1) have "\<not> C" "\<not> B" by auto
    with \<open>B\<close> have False by simp
    then show ?thesis by simp
  qed
qed

lemma NelsonGoodman:
  shows "(k \<longleftrightarrow> (k \<longleftrightarrow> g)) \<longleftrightarrow> g"
  by auto

lemma Smullyan_1_11:
  assumes "k \<longleftrightarrow> ((k \<longleftrightarrow> g) \<longleftrightarrow> yes)"
  shows "yes \<longleftrightarrow> g"
proof (cases k)
  case True
  with assms have "(k \<longleftrightarrow> g) \<longleftrightarrow> yes" by simp
  show ?thesis
  proof (cases g)
    case True
    with \<open>k\<close> \<open>(k \<longleftrightarrow> g) \<longleftrightarrow> yes\<close> have yes by simp
    with \<open>g\<close> show ?thesis by simp 
  next
    case False
    with \<open>k\<close> \<open>(k \<longleftrightarrow> g) \<longleftrightarrow> yes\<close> have "\<not> yes" by simp
    with \<open>\<not> g\<close> show ?thesis by simp  
  qed
next
  case False
  with assms have "\<not> ((k \<longleftrightarrow> g) \<longleftrightarrow> yes)" by simp
  show ?thesis
  proof (cases g)
    case True
    with \<open>\<not> k\<close> \<open>\<not> ((k \<longleftrightarrow> g) \<longleftrightarrow> yes)\<close> have yes by simp
    with \<open>g\<close> show ?thesis by simp
  next
    case False
    with \<open>\<not> k\<close> \<open>\<not> ((k \<longleftrightarrow> g) \<longleftrightarrow> yes)\<close> have "\<not> yes" by simp
    with \<open>\<not> g\<close> show ?thesis by simp
  qed
qed


lemma Smullyan_1_12:
  assumes "k \<longleftrightarrow> ((k \<and> l) \<or> (\<not> k \<and> \<not> l) \<longleftrightarrow> yes)"
  shows "yes \<longleftrightarrow> l"
proof (cases k)
  case True
  with assms have *:"((k \<and> l) \<or> (\<not> k \<and> \<not> l) \<longleftrightarrow> yes)" 
    by simp
  from \<open>k\<close> have **:"k \<and> l \<longleftrightarrow> l" by simp
  from \<open>k\<close> have "\<not> (\<not> k \<and> \<not> l)" by simp
  with * have "k \<and> l \<longleftrightarrow> yes" by simp
  with ** show ?thesis by simp
next
  case False
  with assms have *:"\<not> ((k \<and> l) \<or> (\<not> k \<and> \<not> l) \<longleftrightarrow> yes)" 
    by simp
  from \<open>\<not> k\<close> have **:"\<not> k \<and> \<not> l \<longleftrightarrow> \<not> l" by simp
  from \<open>\<not> k\<close> have "\<not> (k \<and> l)" by simp
  with * have "\<not> (\<not> k \<and> \<not>l) \<longleftrightarrow> yes" by simp
  with ** show ?thesis by simp
qed

lemma Smullyan_2_1:
  assumes "(k \<and> m) \<or> (\<not>k \<and> \<not> m) \<longleftrightarrow> (k \<longleftrightarrow> yes)" 
  shows "yes \<longleftrightarrow> m"
proof (cases m)
  case True
  show ?thesis
  proof (cases k)
    case True
    with assms \<open>m\<close> have "k \<longleftrightarrow> yes" by simp
    with \<open>k\<close> have yes by simp
    with \<open>m\<close> show ?thesis by simp
  next
    case False
    with assms \<open>m\<close> have "\<not> (k \<longleftrightarrow> yes)" by simp
    with \<open>\<not>k\<close> have yes by simp
    with \<open>m\<close> show ?thesis by simp
  qed
next
  case False
  show ?thesis
  proof (cases k)
    case True
    with assms \<open>\<not> m\<close> have "\<not> (k \<longleftrightarrow> yes)" by simp
    with \<open>k\<close> have "\<not> yes" by simp
    with \<open>\<not> m\<close> show ?thesis by simp
  next
    case False
    with assms \<open>\<not> m\<close> have "k \<longleftrightarrow> yes" by simp
    with \<open>\<not> k\<close> have "\<not> yes" by simp
    with \<open>\<not> m\<close> show ?thesis by simp
  qed
qed

lemma Smullyan_2_3:
  assumes "(m \<longleftrightarrow> k) \<longleftrightarrow> (((m \<longleftrightarrow> k) \<longleftrightarrow> married) \<longleftrightarrow> yes)"
  shows "yes \<longleftrightarrow> married"
proof (cases m)
  case True
  show ?thesis
  proof (cases k)
    case True
    with assms \<open>m\<close> show ?thesis by simp
  next
    case False
    with assms \<open>m\<close> show ?thesis by simp
  qed
next
  case False
  show ?thesis
  proof (cases k)
    case True
    with assms \<open>\<not> m\<close> show ?thesis by simp
  next
    case False
    with assms \<open>\<not> m\<close> show ?thesis by simp
  qed
qed

end