theory Syllogism
  imports Main

begin

lemma 
  assumes "k \<longleftrightarrow> (k \<longrightarrow> g)"
  shows "g \<and> k"
proof (cases k)
  case True
  with assms have "k \<longrightarrow> g" by simp
  with \<open>k\<close> have g by simp
  with \<open>k\<close> show ?thesis by simp
next
  case False
  with assms have "\<not> (k \<longrightarrow> g)" by simp
  then have "\<not> (\<not> k \<or> g)" by simp
  then have "k \<and> \<not> g" by simp
  with \<open>\<not> k\<close> have False by simp
  then show ?thesis by simp
qed

end