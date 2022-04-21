theory InverseImage
  imports Main

begin

thm o_apply
thm vimage_def

lemma 
  assumes "inj f" "inj g"
  shows "inj (f \<circ> g)"
proof
  fix x y
  assume "(f \<circ> g) x = (f \<circ> g) y"
  then have "f (g x) = f (g y)" by simp
  then have "g x = g y" using \<open>inj f\<close> by (simp add: inj_def)
  then show "x = y" using \<open>inj g\<close> by (simp add: inj_def)
qed

lemma "f -` (f ` A) \<supseteq> A"
proof
  fix x
  assume "x \<in> A"
  then have "f x \<in> f ` A" by simp
  then show "x \<in> f -` (f ` A)" by simp
qed

lemma
  assumes "inj f"
  shows "f -` (f ` A) \<subseteq> A"
proof
  fix x
  assume "x \<in> f -` (f ` A)"
  then have "f x \<in> f ` A" by simp
  then obtain x' where "x' \<in> A" "f x = f x'" by auto
  with \<open>inj f\<close> have "x = x'" by (simp add: inj_def)
  with \<open>x' \<in> A\<close> show "x \<in> A" by simp
qed

end