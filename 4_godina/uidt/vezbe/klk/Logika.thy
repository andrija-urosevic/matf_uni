theory Logika
  imports Main

begin

lemma
  assumes "\<exists> x. P x"
  assumes "\<forall> x. P x \<longrightarrow> Q x"
  shows "\<exists> x. Q x"
proof-
  from assms(1) obtain x where "P x" by auto
  with assms(2) have "P x \<longrightarrow> Q x" by auto
  with \<open>P x\<close> have "Q x" by auto
  then show "\<exists> x. Q x" by auto
qed

lemma 
  assumes "\<forall> x. covek x \<longrightarrow> smrtan x"
  assumes "\<forall> x. grk x \<longrightarrow> covek x"
  shows "\<forall> x. grk x \<longrightarrow> smrtan x"
proof
  fix Jorgos
  from assms(2) have a1:"grk Jorgos \<longrightarrow> covek Jorgos" by auto
  from assms(1) have a2:"covek Jorgos \<longrightarrow> smrtan Jorgos" by auto
  show "grk Jorgos \<longrightarrow> smrtan Jorgos"
  proof
    assume "grk Jorgos"
    with a1 have "covek Jorgos" by auto
    with a2 show "smrtan Jorgos" by auto
  qed
qed

lemma 
  assumes "(\<forall> a. P a \<longrightarrow> Q a)"
  assumes "(\<forall> b. P b)"
  shows "(\<forall> x. Q x)"
proof
  fix x
  from assms(2) have "P x" by auto
  with assms(1) show "Q x" by auto
qed

lemma 
  assumes "\<exists> x. A x \<or> B x" 
  shows "(\<exists> x. A x) \<or> (\<exists> x. B x)"
proof -
  from assms obtain x where "A x \<or> B x" by auto
  then show "(\<exists> x. A x) \<or> (\<exists> x. B x)"
  proof
    assume "A x"
    then have "\<exists> x. A x" by auto
    then show "(\<exists> x. A x) \<or> (\<exists> x. B x)" by auto
  next
    assume "B x"
    then have "\<exists> x. B x" by auto
    then show "(\<exists> x. A x) \<or> (\<exists> x. B x)" by auto
  qed
qed

lemma
  assumes "\<forall> x. A x \<longrightarrow> \<not> B x"
  shows "\<not> (\<exists> x. A x \<and> B x)"
proof
  assume "\<exists> x. A x \<and> B x"
  then obtain x where "A x" "B x" by auto
  from assms have "A x \<longrightarrow> \<not> B x" by auto
  with \<open>A x\<close> have "\<not> B x" by auto
  with \<open>B x\<close> show False by auto
qed

lemma
  assumes "\<forall> x. \<not> paran x \<longrightarrow> neparan x"
  assumes "\<forall> x. neparan x \<longrightarrow> \<not> paran x"
  shows "\<forall> x. \<not> (paran x \<and> neparan x)"
proof
  fix x
  from assms(1) have 1:"\<not> paran x \<longrightarrow> neparan x" by auto
  from assms(2) have 2:"neparan x \<longrightarrow> \<not> paran x" by auto
  show "\<not> (paran x \<and> neparan x)"
  proof
    assume "paran x \<and> neparan x"
    then show False
    proof
      assume "paran x" "neparan x"
      with 2 have "\<not> paran x" by auto
      with \<open>paran x\<close> show False by auto
    qed
  qed
qed

lemma
  assumes "\<forall> x. \<not> paran x \<longrightarrow> neparan x"
  assumes "\<forall> x. neparan x \<longrightarrow> \<not> paran x"
  shows "\<forall> x. paran x \<or> neparan x"
proof
  fix x
  have "neparan x \<or> \<not> neparan x" by auto
  then show "paran x \<or> neparan x"
  proof
    assume "neparan x"
    then show "paran x \<or> neparan x" by auto
  next
    assume "\<not> neparan x"
    with assms(1) have "paran x" by auto
    then show "paran x \<or> neparan x" by auto
  qed
qed

lemma
  assumes "\<forall> x. konj x \<longrightarrow> potkovice x"
  assumes "\<not> (\<exists> x. covek x \<and> potkovice x)"
  assumes "\<exists> x. covek x"
  shows "\<exists> x. covek x \<and> \<not> konj x"
proof -
  from assms(3) obtain Pera where "covek Pera" by auto
  have "konj Pera \<or> \<not> konj Pera" by auto
  then have "covek Pera \<and> \<not> konj Pera"
  proof
    assume "konj Pera"
    show "covek Pera \<and> \<not> konj Pera"
    proof
      from \<open>covek Pera\<close> show "covek Pera" by auto
    next
      show "\<not> konj Pera"
      proof
        assume "konj Pera"
        with assms(1) have "potkovice Pera" by auto
        with assms(2) have "\<not> covek Pera" by auto
        with \<open>covek Pera\<close> show False by auto
      qed
    qed
  next
    assume "\<not> konj Pera"
    with \<open>covek Pera\<close> show "covek Pera \<and> \<not> konj Pera" by auto
  qed
  then show "\<exists> x. covek x \<and> \<not> konj x" by auto
qed

lemma
  assumes "\<exists> x. macka x \<and> \<not> rep x"
  assumes "\<forall> x. macka x \<longrightarrow> sisar x"
  shows "\<exists> x. sisar x \<and> \<not> rep x"
proof -
  from assms(1) obtain Maca where "macka Maca" "\<not> rep Maca" by auto
  with assms(2) have "sisar Maca" by auto
  with \<open>\<not> rep Maca\<close> have "sisar Maca \<and> \<not> rep Maca" by auto
  then show "\<exists> x. sisar x \<and> \<not> rep x" by auto
qed

lemma "\<not> (A \<and> B) \<longrightarrow> \<not> A \<or> \<not> B"
proof
  assume "\<not> (A \<and> B)"
  show "\<not> A \<or> \<not> B"
  proof (rule ccontr)
    assume "\<not> (\<not> A \<or> \<not> B)"
    have "A \<and> B"
    proof
      show A
      proof (rule ccontr)
        assume "\<not> A"
        then have "\<not> A \<or> \<not> B" by (rule disjI1)
        with \<open>\<not> (\<not> A \<or> \<not> B)\<close> show False by auto
      qed
    next
      show B
      proof (rule ccontr)
        assume "\<not> B"
        then have "\<not> A \<or> \<not> B" by (rule disjI2)
        with \<open>\<not> (\<not> A \<or> \<not> B)\<close> show False by auto
      qed
    qed
    with \<open>\<not> (A \<and> B)\<close> show False by auto
  qed
qed

lemma "((P \<longrightarrow> Q) \<longrightarrow> P) \<longrightarrow>P"
  apply (rule impI)
  apply (rule ccontr)
  apply (erule impE)
   apply (rule impI)
   apply (erule notE)
   apply assumption
  apply (erule notE)
  apply assumption
  done

lemma "((P \<longrightarrow> Q) \<longrightarrow> P) \<longrightarrow> P"
proof
  assume "(P \<longrightarrow> Q) \<longrightarrow> P"
  show "P"
  proof (rule ccontr)
    assume "\<not> P"
    have "P \<longrightarrow> Q"
    proof
      assume "P"
      with \<open>\<not> P\<close> have False by auto
      then show "Q" by auto
    qed
    with \<open>(P \<longrightarrow> Q) \<longrightarrow> P\<close> have P by auto
    with \<open>\<not> P\<close> show False by auto
  qed
qed

lemma "P \<or> \<not> P"
  apply (rule classical)
  apply (rule disjI1)
  apply (rule classical)
  apply (erule notE)
  apply (rule disjI2)
  apply assumption
  done

lemma "P \<or> \<not> P"
proof (rule classical)
  assume "\<not> (P \<or> \<not> P)"
  show "P \<or> \<not> P"
  proof
    show P
    proof (rule classical)
      assume "\<not> P"
      with \<open>\<not> (P \<or> \<not> P)\<close> have False by auto
      then show P by auto
  qed
qed

lemma 
  assumes "\<not> (\<forall> x. P x)"
  shows "\<exists> x. \<not> P x"
proof (rule classical)
  assume "\<not> (\<exists> x. \<not> P x)"
  have "\<forall> x. P x"
  proof
    fix x
    show "P x"
    proof (rule classical)
      assume "\<not> P x"
      with \<open>\<not> (\<exists> x. \<not> P x)\<close> show "P x" by auto
    qed
  qed
  with assms(1) show "\<exists> x. \<not> P x" by auto
qed



end
