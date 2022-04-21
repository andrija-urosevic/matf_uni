theory NatDed
  imports Main

begin

lemma 
"
(\<forall> x y. R x y \<longrightarrow> R y x) 
\<and>
(\<forall> x y z. R x y \<and> R y z \<longrightarrow> R x z)
\<and>
(\<forall> x. \<exists> y. R x y)
\<longrightarrow>
(\<forall> x. R x x)
"
  apply (rule impI)
  apply (erule conjE)+
  apply (rule allI)
  apply (erule_tac x="x" in allE)
  back
  back
  apply (erule exE)
  apply (erule_tac x="x" in allE)
  apply (erule_tac x="y" in allE)
  back
  apply (erule impE)
   apply assumption
  apply (erule_tac x="x" in allE)
  apply (erule_tac x="y" in allE)
  apply (erule_tac x="x" in allE)
  apply (erule impE)
   apply (rule conjI)
    apply assumption
   apply assumption
  apply assumption
  done

lemma 
"
(\<forall> x. m x \<longrightarrow> s x)
\<and>
(\<exists> x. lj x \<and> \<not> s x)
\<longrightarrow>
(\<exists> x. lj x \<and> \<not> m x)
"
  apply (rule impI)
  apply (erule conjE)
  apply (erule exE)
  apply (erule conjE)
  apply (rule_tac x="x" in exI)
  apply (rule conjI)
   apply assumption
  apply (rule notI)
  apply (erule_tac x="x" in allE)
  apply (erule impE)
   apply assumption
  apply (erule notE)
  apply assumption
  done

lemma
"
(\<exists> x. g x)
\<and>
(\<forall> x. g x \<longrightarrow> c x)
\<and>
(\<forall> x. c x \<longrightarrow> s x)
\<longrightarrow>
(\<exists> x. g x \<and> s x)
"
  apply (rule impI)
  apply (erule conjE)+
  apply (erule exE)
  apply (erule_tac x="x" in allE)
  apply (erule impE)
   apply assumption
  apply (erule_tac x="x" in allE)
  apply (erule impE)
   apply assumption
  apply (rule_tac x="x" in exI)
  apply (rule conjI)
   apply assumption
  apply assumption
  done

lemma
"
(\<forall> x. (\<exists> y. voli x y) \<longrightarrow> (\<forall> z. voli z x))
\<and>
(voli Dzon Meri)
\<longrightarrow>
(voli Jago Otelo)
"
  apply (rule impI)
  apply (erule conjE)
  apply (rule_tac x="Otelo" in allE, assumption)
  apply (erule impE)
   apply (rule_tac x="Dzon" in exI)
   apply (erule_tac x="Dzon" in allE)
   apply (erule impE)
    apply (rule_tac x="Meri" in exI)
    apply assumption
   apply (erule_tac x="Otelo" in allE)
   apply assumption
  apply (erule_tac x="Jago" in allE)
  back
  apply assumption
  done

end