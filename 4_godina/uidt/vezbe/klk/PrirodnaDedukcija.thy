theory PrirodnaDedukcija
  imports Main

begin

lemma "A \<longrightarrow> A \<or> B"
  apply (rule impI)
  apply (rule disjI1)
  apply assumption
  done

lemma "B \<longrightarrow> A \<or> B"
  apply (rule impI)
  apply (rule disjI2)
  apply assumption
  done

lemma "A \<longrightarrow> (A \<or> B) \<and> (B \<or> A)"
  apply (rule impI)
  apply (rule conjI)
   apply (rule disjI1)
   apply assumption
  apply (rule disjI2)
  apply assumption
  done

lemma "A \<and> B \<longrightarrow> B \<and> A"
  apply (rule impI)
  apply (erule conjE)
  apply (rule conjI)
   apply assumption
  apply assumption
  done

lemma "A \<or> B \<longrightarrow> B \<or> A"
  apply (rule impI)
  apply (erule disjE)
   apply (rule disjI2)
   apply assumption
  apply (rule disjI1)
  apply assumption
  done

lemma "A \<and> B \<longrightarrow> A \<or> B"
  apply (rule impI)
  apply (erule conjE)
  apply (rule disjI1)
  apply assumption
  done

lemma "(A \<and> B \<longrightarrow> C) \<longrightarrow> (A \<longrightarrow> (B \<longrightarrow> C))"
  apply (rule impI)
  apply (rule impI)
  apply (rule impI)
  apply (erule impE)
   apply (rule conjI)
    apply assumption
   apply assumption
  apply assumption
  done

lemma "(A \<longrightarrow> (B \<longrightarrow> C)) \<longrightarrow> (A \<and> B \<longrightarrow> C)"
  apply (rule impI)
  apply (rule impI)
  apply (erule conjE)
  apply (erule impE)
   apply assumption
  apply (erule impE)
   apply assumption
  apply assumption
  done

lemma "\<not> (A \<or> B) \<longrightarrow> \<not> A \<and> \<not> B"
  apply (rule impI)
  apply (rule conjI)
   apply (rule notI)
   apply (erule notE)
  apply (rule disjI1)
   apply assumption
  apply (rule notI)
  apply (erule notE)
  apply (rule disjI2)
  apply assumption
  done

lemma "\<not> A \<and> \<not> B \<longrightarrow> \<not> (A \<or> B)"
  apply (rule impI)
  apply (rule notI)
  apply (erule conjE)
  apply (erule disjE)
   apply (erule notE)
   apply assumption
  apply (erule notE)+
  apply assumption
  done

lemma "\<not> (A \<longleftrightarrow> \<not> A)"
  apply (rule notI)
  apply (erule iffE)
  apply (erule impE) back
   apply (rule notI)
   apply (erule impE)
    apply assumption
   apply (erule notE)
   apply assumption
  apply (erule impE)
   apply assumption
  apply (erule notE)
  apply assumption
  done

lemma "(Q \<longrightarrow> R) \<and> (R \<longrightarrow> P \<and> Q) \<and> (P \<longrightarrow> Q \<or> R) \<longrightarrow> (P \<longleftrightarrow> Q)"
  apply (rule impI)
  apply (erule conjE)+
  apply (rule iffI)
   apply (erule impE) back back
    apply assumption
   apply (erule disjE)
    apply assumption
   apply (erule impE) back
    apply assumption
   apply (erule conjE)
   apply assumption
  apply (erule impE)
   apply assumption
  apply (erule impE)
   apply assumption
  apply (erule conjE)
  apply assumption
  done

lemma "(P \<longrightarrow> Q) \<and> (Q \<longrightarrow> R) \<longrightarrow> (P \<longrightarrow> Q \<and> R)"
  apply (rule impI)
  apply (rule impI)
  apply (erule conjE)
  apply (rule conjI)
   apply (erule impE)
    apply assumption+
  apply (erule impE)
   apply assumption
  apply (erule impE)
   apply assumption+
  done

lemma "(P \<longrightarrow> Q) \<and> \<not> Q \<longrightarrow> \<not> P"
  apply (rule impI)
  apply (rule notI)
  apply (erule conjE)
  apply (erule impE)
   apply assumption
  apply (erule notE)
  apply assumption
  done

lemma "(P \<longrightarrow> (Q \<longrightarrow> R)) \<longrightarrow> (Q \<longrightarrow> (P \<longrightarrow> R))"
  apply (rule impI)+
  apply (erule impE)
   apply assumption
  apply (erule impE)
   apply assumption+
  done

lemma "\<not> (P \<and> \<not> P)"
  apply (rule notI)
  apply (erule conjE)
  apply (erule notE)
  apply assumption
  done

lemma "A \<and> (B \<or> C) \<longrightarrow> (A \<and> B) \<or> (A \<and> C)"
  apply (rule impI)
  apply (erule conjE)
  apply (erule disjE)
   apply (rule disjI1)
   apply (rule conjI)
    apply assumption+
  apply (rule disjI2)
  apply (rule conjI)
  apply assumption+
  done

lemma "(A \<longrightarrow> C) \<and> (B \<longrightarrow> \<not> C) \<longrightarrow> \<not> (A \<and> B)"
  apply (rule impI)
  apply (rule notI)
  apply (erule conjE)+
  apply (erule impE)
   apply assumption
  apply (erule impE)
   apply assumption
  apply (erule notE)
  apply assumption
  done

lemma "(A \<and> B) \<longrightarrow> ((A \<longrightarrow> C) \<longrightarrow> \<not> (B \<longrightarrow> \<not> C))"
  apply (rule impI)
  apply (rule impI)
  apply (rule notI)
  apply (erule conjE)
  apply (erule impE)
   apply assumption
  apply (erule impE)
   apply assumption
  apply (erule notE)
  apply assumption
  done

lemma "(A \<longleftrightarrow> B) \<longrightarrow> (\<not> A \<longleftrightarrow> \<not> B)"
  apply (rule impI)
  apply (rule iffI)
   apply (rule notI)
   apply (erule iffE)
   apply (erule impE)+
     apply assumption+
   apply (erule impE)
    apply assumption
  apply (erule notE)
   apply assumption
  apply (erule iffE)
  apply (rule notI)
  apply (erule impE)
   apply assumption
  apply (erule impE)
   apply assumption
  apply (erule notE)
  apply assumption
  done

lemma "A \<longrightarrow> \<not> \<not> A"
  apply (rule impI)
  apply (rule notI)
  apply (erule notE)
  apply assumption
  done

lemma "\<not> (A \<longleftrightarrow> \<not> A)"
  apply (rule notI)
  apply (erule iffE)
  apply (erule impE) back
   apply (rule notI)
   apply (erule impE)
    apply assumption
   apply (erule notE)
   apply assumption
  apply (erule impE)
   apply assumption
  apply (erule notE)
  apply assumption
  done

lemma "(A \<longrightarrow> B) \<longrightarrow> (\<not> B \<longrightarrow> \<not> A)"
  apply (rule impI)
  apply (rule impI)
  apply (rule notI)
  apply (erule impE)
   apply assumption
  apply (erule notE)
  apply assumption
  done

lemma "\<not> A \<or> B \<longrightarrow> (A \<longrightarrow> B)"
  apply (rule impI)+
  apply (erule disjE)
  apply (erule notE)
   apply assumption+
  done

lemma "((\<forall> x. covek x \<longrightarrow> smrtan x) \<and> covek Sokrat) \<longrightarrow> smrtan Sokrat"
  apply (rule impI)
  apply (erule conjE)
  apply (erule_tac x="Sokrat" in allE)
  apply (erule impE)
   apply assumption+
  done

lemma "(\<exists> x. \<not> P x) \<longrightarrow> (\<not> (\<forall> x. P x))"
  apply (rule impI)
  apply (rule notI)
  apply (erule exE)
  apply (erule_tac x="x" in allE)
  apply (erule notE)
  apply assumption
  done

lemma "(\<forall> x. \<not> P x) \<longrightarrow> (\<not> (\<exists> x. P x))"
  apply (rule impI)
  apply (rule notI)
  apply (erule exE)
  apply (erule_tac x="x" in allE)
  apply (erule notE)
  apply assumption
  done

lemma "(\<not> (\<exists> x. P x)) \<longrightarrow> (\<forall> x. \<not> P x)"
  apply (rule impI)
  apply (rule allI)
  apply (rule notI)
  apply (erule notE)
  apply (rule_tac x="x" in exI)
  apply assumption
  done

lemma "(\<exists> x. P x) \<and> (\<forall> x. P x \<longrightarrow> Q x) \<longrightarrow> (\<exists> x. Q x)"
  apply (rule impI)
  apply (erule conjE)
  apply (erule exE)
  apply (erule_tac x="x" in allE)
  apply (rule_tac x="x" in exI)
  apply (erule impE)
   apply assumption+
  done

lemma "(\<forall> c. covek c \<longrightarrow> smrtan c) \<and> (\<forall> g. grk g \<longrightarrow> covek g) \<longrightarrow> (\<forall> a. grk a \<longrightarrow> smrtan a)"
  apply (rule impI)
  apply (erule conjE)
  apply (rule allI)
  apply (erule_tac x="a" in allE)+
  apply (rule impI)
  apply (erule impE)+
    apply assumption+
  done

lemma "(\<forall> a. P a \<longrightarrow> Q a) \<and> (\<forall> b. P b) \<longrightarrow> (\<forall> x. Q x)"
  apply (rule impI)
  apply (erule conjE)
  apply (rule allI)
  apply (erule_tac x="x" in allE)+
  apply (erule impE)
   apply assumption+
  done

lemma "(\<exists> x. A x \<and> B x) \<longrightarrow> (\<exists> x. A x) \<or> (\<exists> x. B x)"
  apply (rule impI)
  apply (erule exE)
  apply (erule conjE)
  apply (rule disjI1)
  apply (rule_tac x="x" in exI)
  apply assumption
  done

lemma "(\<forall> x. A x \<longrightarrow> \<not> B x) \<longrightarrow> \<not> (\<exists> x. A x \<and> B x)"
  apply (rule impI)
  apply (rule notI)
  apply (erule exE)
  apply (erule_tac x="x" in allE)
  apply (erule conjE)
  apply (erule impE)
   apply assumption
  apply (erule notE)
  apply assumption
  done

lemma "(\<forall> x. \<not> paran x \<longrightarrow> neparan x) \<and> (\<forall> x. neparan x \<longrightarrow> \<not> paran x) \<longrightarrow> (\<forall> x. \<not> (paran x \<and> neparan x))"
  apply (rule impI)
  apply (rule allI)
  apply (rule notI)
  apply (erule conjE)
  apply (erule_tac x="x" in allE)+
  apply (erule conjE)
  apply (erule impE)+
    apply assumption+
  apply (erule impE)
   apply assumption
  apply (erule notE)
  apply assumption
  done

lemma "(\<forall> x. konj x \<longrightarrow> potkovice x) \<and> (\<not> (\<exists> x. covek x \<and> potkovice x)) \<and> (\<exists> x. covek x) \<longrightarrow> (\<exists> x. covek x \<and> \<not> konj x)"
  apply (rule impI)
  apply (erule conjE)+
  apply (erule exE)
  apply (rule_tac x="x" in exI)
  apply (rule conjI)
   apply assumption
  apply (rule notI)
  apply (erule_tac x="x" in allE)
  apply (erule impE)
   apply assumption
  apply (erule notE)
  apply (rule_tac x="x" in exI)
  apply (rule conjI)
   apply assumption+
  done

lemma "(\<forall> x. kvadrat x \<longrightarrow> romb x) 
\<and> (\<forall> x. kvadrat x \<longrightarrow> pravougaonik x) 
\<and> (\<exists> x. kvadrat x)
\<longrightarrow> (\<exists> x. romb x \<and> pravougaonik x)"
  apply (rule impI)
  apply (erule conjE)+
  apply (erule exE)
  apply (erule_tac x="x" in allE)+
  apply (rule_tac x="x" in exI)
  apply (rule conjI)
   apply (erule impE)
    apply assumption+
  apply (erule impE) back
   apply assumption+
  done

definition "reflexive R \<longleftrightarrow> (\<forall> x. R x x)"
definition "transitive T \<longleftrightarrow> (\<forall> x y z. T x y \<and> T y z \<longrightarrow> T x z)"
definition "symmetric S \<longleftrightarrow> (\<forall> x y. S x y \<longleftrightarrow> S y x)"

lemma "symmetric R \<and> transitive R \<and> (\<forall> x. \<exists> y. R x y) \<longrightarrow> reflexive R"
  unfolding reflexive_def transitive_def symmetric_def
  apply (rule impI)
  apply (rule allI)
  apply (erule conjE)+
  apply (erule_tac x="x" in allE) back back
  apply (erule exE)
  apply (erule_tac x="x" in allE)
  apply (erule_tac x="x" in allE)
  apply (erule_tac x="y" in allE)
  apply (erule_tac x="y" in allE)
  apply (erule_tac x="x" in allE)
  apply (erule impE)
   apply (rule conjI)
    apply assumption
   apply (erule iffE)
   apply (erule impE)
    apply assumption+
  done

thm ccontr
thm classical

lemma "\<not> \<not> A \<longrightarrow> A"
  apply (rule impI)
  apply (rule ccontr)
  apply (erule notE)
  apply assumption
  done

lemma "(\<not> P \<longrightarrow> P) \<longrightarrow> P"
  apply (rule impI)
  apply (rule classical)
  apply (erule impE)
   apply assumption+
  done

lemma "\<not> (A \<and> B) \<longrightarrow> \<not> A \<or> \<not> B"
  apply (rule impI)
  apply (rule ccontr)
  apply (erule notE)
  apply (rule conjI)
  apply (rule ccontr)
   apply (erule notE)
  apply (rule disjI1)
   apply assumption
  apply (rule ccontr)
  apply (erule notE)
  apply (rule disjI2)
  apply assumption
  done

lemma "(\<not>(\<forall> x. P x)) \<longrightarrow> (\<exists> x. \<not> P x)"
  apply (rule impI)
  apply (rule ccontr)
  apply (erule notE)
  apply (rule allI)
  apply (rule ccontr)
  apply (erule notE)
  apply (rule_tac x="x" in exI)
  apply assumption
  done

lemma "(\<not> B \<longrightarrow> \<not> A) \<longrightarrow> (A \<longrightarrow> B)"
  apply (rule impI)+
  apply (rule ccontr)
  apply (erule impE)
   apply assumption
  apply (erule notE) back
  apply assumption
  done

lemma "(A \<longrightarrow> B) \<longrightarrow> (\<not> A \<or> B)"
  apply (rule impI)
  apply (rule ccontr)
  apply (erule impE)
   apply (rule ccontr)
   apply (erule notE)
   apply (rule disjI1)
   apply assumption
  apply (erule notE)
  apply (rule disjI2)
  apply assumption
  done

lemma "(\<not> P \<longrightarrow> Q) \<longleftrightarrow> (\<not> Q \<longrightarrow> P)"
  apply (rule iffI)
   apply (rule ccontr)
   apply (erule impE)
    apply (rule notI)
    apply (erule notE)
    apply (rule impI)
  apply assumption
   apply (erule notE)
   apply (rule impI)
  apply (erule notE)
   apply assumption
  apply (rule impI)
  apply (rule ccontr)
  apply (erule impE)
   apply assumption
  apply (erule notE)
  apply assumption
  done

lemma "(\<not> P \<longrightarrow> Q) \<longleftrightarrow> (\<not> Q \<longrightarrow> P)"
  apply (rule iffI)
   apply (rule impI)
   apply (rule ccontr)
   apply (erule impE)
    apply assumption
  apply (erule notE)
   apply assumption
  apply (rule impI)
  apply (rule ccontr)
  apply (erule impE)
  apply assumption
  apply (erule notE)
  apply assumption
  done

lemma "((P \<longrightarrow> Q) \<longrightarrow> P) \<longrightarrow> P"
  apply (rule impI)
  apply (rule ccontr)
  apply (erule impE)
   apply (rule impI)
   apply (erule notE)
  apply assumption
  apply (erule notE)
  apply assumption
  done

lemma "(nA \<longleftrightarrow> bA \<or> bB) \<and> (nB \<longleftrightarrow> \<not> bA) \<and> ((nA \<and> nB) \<or> (\<not> nA \<and> \<not> nB)) \<longrightarrow> \<not> bA \<and> bB"
  apply (rule impI)
  apply (erule conjE)+
  apply (erule iffE)+
  apply (erule disjE)
   apply (erule conjE)
   apply (erule impE)
    apply assumption
   apply (erule impE)
    apply assumption
   apply (rule conjI)
    apply (erule impE)
     apply assumption+
   apply (erule disjE)
    apply (rule ccontr)
    apply (erule impE)
     apply assumption
    apply (erule notE) back
    apply assumption +
  apply (erule conjE)
  apply (erule impE) back
   apply (rule ccontr)
   apply (erule impE) back back
    apply (rule notI)
    apply (erule notE) back back
  apply (rule disjI1)
    apply assumption
   apply (erule notE) back
   apply assumption
  apply (erule impE)
   apply assumption
  apply (erule impE) back
   apply (rule notI)
   apply (erule notE)
   apply assumption
  apply (erule impE)
   apply assumption
  apply (rule ccontr)
  apply (erule notE)
  apply assumption
  done

lemma "P \<or> \<not> P"
  apply (rule classical)
  apply (rule disjI1)
  apply (rule ccontr)
  apply (erule notE)
  apply (rule disjI2)
  apply assumption
  done

lemma "(A \<longleftrightarrow> (A \<longleftrightarrow> B)) \<longrightarrow> B"
  apply (rule impI)
  apply (cases A)
   apply (erule iffE)
   apply (erule impE)
    apply assumption
   apply (erule iffE)
   apply (erule impE) back
    apply assumption+
  apply (rule ccontr)
  apply (erule iffE)
  apply (erule impE) back
   apply (rule iffI)
    apply (erule notE)
    apply assumption
   apply (erule notE) back
   apply assumption
  apply (erule notE)
  apply assumption
  done

lemma "\<exists> x. (drunk x \<longrightarrow> (\<forall> x. drunk x))"
  apply (cases "\<forall> x. drunk x")
   apply (rule exI)
   apply (rule impI)
   apply assumption
  apply (rule ccontr)
  apply (erule notE)
  apply (rule allI)
  apply (rule ccontr)
  apply (erule notE)
  apply (rule_tac x="x" in exI)
  apply (rule impI)
  apply (erule notE)
  apply assumption
  done

lemma "(A \<and> B \<longrightarrow> C) \<longrightarrow> (A \<longrightarrow> (B \<longrightarrow> C))"
  apply (rule impI)+
  apply (erule impE)
   apply (rule conjI)
    apply assumption+
  done

lemma "A \<and> (B \<or> C) \<longrightarrow> (A \<and> B) \<or> (A \<and> C)"
  apply (rule impI)
  apply (erule conjE)
  apply (erule disjE)
   apply (rule disjI1)
   apply (rule conjI)
    apply assumption+
  apply (rule disjI2)
  apply (rule conjI)
  apply assumption+
  done

lemma "\<not> (A \<and> B) \<longrightarrow> \<not> A \<or> \<not> B"
  apply (rule impI)
  apply (rule ccontr)
  apply (erule notE)
  apply (rule conjI)
  apply (rule ccontr)
  apply (erule notE)
  apply (rule disjI1)
   apply assumption
  apply (rule ccontr)
  apply (erule notE)
  apply (rule disjI2)
  apply assumption
  done

lemma "(\<not> P \<longrightarrow> Q) \<longleftrightarrow> (\<not> Q \<longrightarrow> P)"
  apply (rule iffI)
   apply (rule impI)
   apply (rule ccontr)
   apply (erule impE)
  apply assumption
  apply (erule notE)
   apply assumption
  apply (rule impI)
  apply (rule ccontr)
  apply (erule impE)
  apply assumption
  apply (erule notE)
  apply assumption
  done

lemma "(\<forall> x. \<not> kvadrat x \<longrightarrow> krug x) \<and> (\<forall> x. krug x \<longrightarrow> \<not> kvadrat x) \<longrightarrow> 
(\<forall> x. (kvadrat x \<or> krug x) \<and> \<not> (kvadrat x \<and> krug x))"
  apply (rule impI)
  apply (erule conjE)
  apply (rule allI)
  apply (erule_tac x="x" in allE)+
  apply (rule conjI)
  apply (rule ccontr)
  apply (erule impE)
    apply (rule notI)
    apply (erule notE)
    apply (rule disjI1)
  apply assumption
   apply (erule impE)
    apply assumption
   apply (erule notE)
   apply (rule disjI2)
   apply assumption
  apply (rule notI)
  apply (erule conjE)
  apply (erule impE) back
   apply assumption
  apply (erule notE)
  apply assumption
  done


end