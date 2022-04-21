theory Sledbenik
  imports Main

begin

definition sledbenik :: "nat \<Rightarrow> nat" where
"sledbenik x = x + 1"

lemma "sledbenik (sledbenik x) = x + 2"
  unfolding sledbenik_def
  by auto

lemma x_vece_od_0:
  assumes "x > 0"
  shows "sledbenik x > 1"
  unfolding sledbenik_def
  using assms
  by auto

lemma x_manje_od_3:
  assumes "x < 3"
  shows "sledbenik x < 4"
  using assms
  unfolding sledbenik_def
  by auto

lemma x_vece_0_manje_3:
  assumes "x > 0 \<and> x < 3"
  shows "sledbenik x > 1 \<and> sledbenik x < 4"
  using assms
  unfolding sledbenik_def
  by auto

end