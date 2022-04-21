theory NaturalDeduction
  imports Main
begin

thm impI
thm disjI1
thm disjI2
thm conjI
thm iffI
thm notI
thm impE
thm iffE
thm conjE
thm disjE
thm notE

lemma "A \<and> B \<longrightarrow> A"
  apply (rule impI)
  apply (erule conjE)
  apply assumption
  done

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

lemma "B \<longrightarrow> A \<or> B \<or> A"
  apply (rule impI)
  apply (rule disjI2)
  apply (rule disjI1)
  apply assumption
  done

lemma "B \<longrightarrow> A \<or> (A \<or> B)"
  apply (rule impI)
  apply (rule disjI2)
  apply (rule disjI2)
  apply assumption
  done

lemma "A \<longrightarrow> A \<and> A"
  apply (rule impI)
  apply (rule conjI)
   apply assumption
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

lemma "A \<longleftrightarrow> A"
  apply (rule iffI)
   apply assumption
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
  apply (erule impE)
   apply (erule conjE)
   apply assumption
  apply (erule impE)
   apply (erule conjE)
   apply assumption
  apply (erule conjE)
  apply assumption
  done

lemma "\<not>(A \<or> B) \<longrightarrow> \<not>A \<and> \<not>B"
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
  apply (erule notE)
  back
  apply assumption
  done

lemma "\<not> (A \<longleftrightarrow> \<not> A)"
  apply (rule notI)
  apply (erule iffE)
  apply (erule impE) (* alternativa druga premisa *)
   back
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
  apply (erule conjE)
  apply (erule conjE)
  apply (rule iffI)
   apply (erule impE)
    back
    back
  apply assumption
   apply (erule disjE)
    apply assumption
   apply (erule impE)
    apply (erule impE)
     apply assumption
    apply (erule conjE)
    apply assumption
   apply (erule impE)
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

lemma "(P \<longrightarrow> (Q \<longrightarrow> R)) \<longrightarrow> (Q \<longrightarrow> (P \<longrightarrow> R))"
  apply (rule impI)
  apply (rule impI)
  apply (rule impI)
  apply (erule impE)
   apply assumption
  apply (erule impE)
  apply assumption
  apply assumption
  done

lemma "A \<and> (B \<or> C ) \<longrightarrow> (A \<and> B) \<or> (A \<and> C )"
  apply (rule impI)
  apply (erule conjE)
  apply (erule disjE)
   apply (rule disjI1)
   apply (rule conjI)
    apply assumption
   apply assumption
  apply (rule disjI2)
  apply (rule conjI)
  apply assumption
  apply assumption
  done

lemma "\<not> (A \<and> B) \<longrightarrow> (A \<longrightarrow> \<not>B)"
  apply (rule impI)
  apply (rule impI)
  apply (rule notI)
  apply (erule notE)
  apply (rule conjI)
   apply assumption
  apply assumption
  done

lemma "(A \<longrightarrow> C ) \<and> (B \<longrightarrow> \<not> C ) \<longrightarrow> \<not> (A \<and> B)"
  apply (rule impI)
  apply (erule conjE)
  apply (rule notI)
  apply (erule conjE)
  apply (erule impE)
   apply assumption
  apply (erule impE)
   apply assumption
  apply (erule notE)
  apply assumption
  done

lemma "(A \<and> B) \<longrightarrow> ((A \<longrightarrow> C ) \<longrightarrow> \<not> (B \<longrightarrow> \<not> C ))"
  apply (rule impI)
  apply (rule impI)
  apply (erule conjE)
  apply (erule impE)
   apply assumption
  apply (rule notI)
  apply (erule impE)
   apply assumption
  apply (erule notE)
  apply assumption
  done

lemma "(A \<longleftrightarrow> B) \<longrightarrow> (\<not> A \<longleftrightarrow> \<not> B)"
  apply (rule impI)
  apply (rule iffI)
  apply (erule iffE)
   apply (rule notI)
   apply (erule notE)
   apply (erule impE)
    back
    apply assumption
   apply assumption
  apply (erule iffE)
  apply (rule notI)
  apply (erule notE)
  apply (erule impE)
   apply assumption
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
  apply (erule impE)
  back
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
  apply (rule impI)
  apply (rule impI)
  apply (erule disjE)
   apply (erule notE)
   apply assumption
  apply assumption
  done



end