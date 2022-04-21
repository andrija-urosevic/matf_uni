theory FirstOrder
  imports Main

begin

thm allI (* proizvoljna fiksirana promenljiva *)
thm allE (* unifikovanje promenljive x nekom konkretnom promenljivom *)
thm exI  (* ako postoji konkretna promenljiva, onda postoji neko x *)
thm exE  (*  *)

lemma "((\<forall> x. covek x \<longrightarrow> smrtan x) \<and> covek Sokrat) \<longrightarrow> smrtan Sokrat"
  apply (rule impI)
  apply (erule conjE)
  apply (erule_tac x = "Sokrat" in allE)
  apply (erule impE)
   apply assumption
  apply assumption
  done

lemma de_Morgan_1: "(\<exists> x. \<not> P x) \<longrightarrow> (\<not> (\<forall> x. P x))"
  apply (rule impI)
  apply (rule notI)
  apply (erule exE)
  apply (erule_tac x="x" in allE)
  apply (erule notE)
  apply assumption
  done

lemma de_Morgan_2: "(\<forall> x. \<not> P x) \<longrightarrow> (\<not> (\<exists> x. P x))"
  apply (rule impI)
  apply (rule notI)
  apply (erule exE)
  apply (erule_tac x="x" in allE)
  apply (erule notE)
  apply assumption
  done

lemma de_Morgan_3: "(\<not> (\<exists> x. P x)) \<longrightarrow> (\<forall> x. \<not> P x)"
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
  apply (erule impE)
   apply assumption
  apply (rule_tac x="x" in exI)
  apply assumption
  done

lemma 
"(\<forall> c. covek c \<longrightarrow> smrtan c)
\<and>
(\<forall> g. grk g \<longrightarrow> covek g)
\<longrightarrow>
(\<forall> a. grk a \<longrightarrow> smrtan a)"
  apply (rule impI)
  apply (erule conjE)
  apply (rule allI)
  apply (rule impI)
  apply (erule_tac x="a" in allE)
  apply (erule_tac x="a" in allE)
  apply (erule impE)
   apply (erule impE)
    apply assumption
   apply assumption
  apply assumption
  done

lemma "(\<forall> a. P a \<longrightarrow> Q a) \<and> (\<forall> b. P b) \<longrightarrow> (\<forall> x. Q x)"
  apply (rule impI)
  apply (rule allI)
  apply (erule conjE)
  apply (erule_tac x="x" in allE)
  apply (erule_tac x="x" in allE)
  apply (erule impE)
   apply assumption
  apply assumption
  done

lemma "(\<exists> x. A x \<or> B x) \<longrightarrow> (\<exists> x. A x) \<or> (\<exists> x. B x)"
  apply (rule impI)
  apply (erule exE)
  apply (erule disjE)
   apply (rule disjI1)
   apply (rule_tac x="x" in exI)
   apply assumption
  apply (rule disjI2)
  apply (rule_tac x="x" in exI)
  apply assumption
  done

lemma "(\<forall> x. A x \<longrightarrow> \<not> B x) \<longrightarrow> \<not> (\<exists> x. A x \<and> B x)"
  apply (rule impI)
  apply (rule notI)
  apply (erule exE)
  apply (erule conjE)
  apply (erule_tac x="x" in allE)
  apply (erule impE)
   apply assumption
  apply (erule notE)
  apply assumption
  done

lemma 
"
(\<forall>x. \<not> Paran x \<longrightarrow> Neparan x)
\<and>
(\<forall>x. Neparan x \<longrightarrow> \<not> Paran x)
\<longrightarrow>
(\<forall>x. \<not> (Paran x \<and> Neparan x))
"
  apply (rule impI)
  apply (rule allI)
  apply (rule notI)
  apply (erule conjE)
  apply (erule conjE)
  apply (erule_tac x="x" in allE)
  apply (erule_tac x="x" in allE)
  apply (erule impE)
   apply (erule impE)
    apply assumption
   apply assumption
  apply (erule impE)
  apply assumption
  apply (erule notE)
  apply assumption
  done

lemma 
"
(\<forall>x. \<not> Paran x \<longrightarrow> Neparan x)
\<and>
(\<forall>x. Neparan x \<longrightarrow> \<not> Paran x)
\<longrightarrow>
(\<forall>x. Paran x \<or> Neparan x)
"
  apply (rule impI)
  apply (erule conjE)
  apply (rule allI)
  apply (erule_tac x="x" in allE)
  apply (erule_tac x="x" in allE)
  apply (rule ccontr)
  apply (erule impE)
  apply (rule notI)
   apply (erule impE)
    apply (erule notE)
    apply (rule disjI1)
    apply assumption
   apply (erule notE)
   back
   apply assumption
  apply (erule impE)
   apply assumption
  apply (erule notE)
  apply (rule disjI2)
  apply assumption
  done

lemma 
"
(\<forall>x. Konj x \<longrightarrow> Potkovice x)
\<and>
(\<not>(\<exists>x. Covek x \<and> Potkovice x))
\<and>
(\<exists>x. Covek x)
\<longrightarrow>
(\<exists>x. Covek x \<and> \<not> Konj x)
"
  apply (rule impI)
  apply (erule conjE)
  apply (erule conjE)
  apply (erule exE)
  apply (rule_tac x="x" in exI)
  apply (rule conjI)
   apply assumption
  apply (rule notI)
  apply (erule_tac x="x" in allE)
  apply (erule notE)
  apply (erule impE)
  apply assumption
  apply (rule_tac x="x" in exI)
  apply (rule conjI)
   apply assumption
  apply assumption
  done

lemma
"
(\<forall>x. Kvadrat x \<longrightarrow> Romb x)
\<and>
(\<forall>x. Kvadrat x \<longrightarrow> Pravougaonik x)
\<and>
(\<exists>x. Kvadrat x)
\<longrightarrow>
(\<exists>x. Romb x \<and> Pravougaonik x)
"
  apply (rule impI)
  apply (erule conjE)
  apply (erule conjE)
  apply (erule exE)
  apply (rule_tac x="x" in exI)
  apply (erule_tac x="x" in allE)
  apply (erule_tac x="x" in allE)
  apply (rule conjI)
   apply (erule impE)
  apply assumption
  apply assumption
  apply (erule impE)
   back
  apply assumption
  apply assumption
  done

definition "reflexive R \<longleftrightarrow> (\<forall>x. R x x)"
definition "transitive T \<longleftrightarrow> (\<forall>x.\<forall>y.\<forall>z. T x y \<and> T y z \<longrightarrow> T x z)"
definition "symmetric S \<longleftrightarrow> (\<forall>x.\<forall>y. S x y \<longleftrightarrow> S y x)"

lemma "symmetric R \<and> transitive R \<and> (\<forall>x. \<exists>y. R x y) \<longrightarrow> reflexive R"
  unfolding symmetric_def transitive_def reflexive_def
  apply (rule impI)
  apply (erule conjE)
  apply (erule conjE)
  apply (rule allI)
  apply (erule_tac x="x" in allE)
  apply (erule_tac x="x" in allE)
  apply (erule_tac x="x" in allE)
  apply (erule exE)
  apply (erule_tac x="y" in allE)
  apply (erule_tac x="y" in allE)
  apply (erule_tac x="x" in allE)
  apply (erule impE)
  apply (erule iffE)
  apply (erule impE)
   apply assumption
  apply (erule impE)
    apply assumption
   apply (rule conjI)
  apply assumption
  apply assumption
  apply (erule iffE)
  apply (erule impE)
   apply assumption
  apply assumption
  done

end