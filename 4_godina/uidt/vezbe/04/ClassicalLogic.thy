theory ClassicalLogic
  imports Main

begin

thm ccontr
thm classical

lemma "A \<longrightarrow> \<not>\<not> A"
  apply (rule impI)
  apply (rule notI)
  apply (erule notE)
  apply assumption
  done

lemma "\<not> \<not> A \<longrightarrow> A"
  apply (rule impI)
  (* apply (erule notE) ne moze *)
  apply (rule ccontr)
  apply (erule notE)
  apply assumption
  done

lemma "(\<not> P \<longrightarrow> P) \<longrightarrow> P"
  apply (rule impI)
  (* apply (erule impE) *)
  apply (rule ccontr)
  apply (erule impE)
   apply assumption
  apply (erule notE)
  apply assumption
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

lemma "P \<or> \<not> P"
  apply (rule classical)
  apply (rule disjI1)
  (* apply (erule notE) *)
  apply (rule ccontr)
  apply (erule notE)
  apply (rule disjI2)
  apply assumption
  done

lemma "(\<not> B \<longrightarrow> \<not> A) \<longrightarrow> (A \<longrightarrow> B)"
  apply (rule impI)
  apply (rule impI)
  apply (rule ccontr)
  apply (erule impE)
   apply assumption
  apply (erule notE)
  back
  apply assumption
  done

lemma "(A \<longrightarrow> B) \<longrightarrow> (\<not>A \<or> B)"
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

lemma "(nA \<longleftrightarrow> bA \<or> bB) \<and> (nB \<longleftrightarrow> \<not> bA) \<and> ((nA \<and> nB) \<or> (\<not> nA \<and> \<not> nB)) \<longrightarrow> \<not>
bA \<and> bB"
  apply (rule impI)
  apply (erule conjE)+
  apply (erule iffE)+
  apply (erule disjE)
   apply (erule conjE)
   apply (erule impE)
  apply assumption
   apply (erule impE)
    apply assumption
   apply (erule impE)
    apply assumption
   apply (erule impE)
    apply assumption
   apply (rule conjI)
    apply assumption
   apply (rule ccontr)
  apply (erule disjE)
    apply (erule notE)
    apply assumption
   apply (erule notE) back
   apply assumption
  apply (erule conjE)
  apply (erule impE) back
   apply (rule ccontr)
   apply (erule impE) back back
    apply (rule notI)
    apply (erule notE) back back
    apply (rule disjI1)
    apply assumption
   apply (erule impE) back
    apply assumption
   apply (erule notE) back
   apply assumption
  apply (erule notE)
  apply assumption
  done

lemma "P \<or> \<not>P"
  apply (rule classical)
  apply (rule disjI1)
  apply (rule ccontr)
  apply (erule notE)
  apply (rule disjI2)
  apply assumption
  done

lemma "(A \<longleftrightarrow> (A \<longleftrightarrow> B)) \<longleftrightarrow> B"
  apply (rule iffI)
   apply (cases A)
    apply (erule iffE)
    apply (erule impE)
     apply assumption
    apply (erule iffE)
    apply (erule impE) back
     apply assumption
    apply assumption
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
  apply (rule iffI)
   apply (rule iffI)
    apply assumption
   apply assumption
  apply (erule iffE)
  apply (erule impE) back
  apply assumption
  apply assumption
  done

lemma "\<exists>x. (Drunk x \<longrightarrow> (\<forall>x. Drunk x))"
  apply (cases "\<forall>x. Drunk x")
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

end