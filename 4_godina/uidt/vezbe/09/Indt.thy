theory Indt
  imports Main

begin

(*
1 1
0 1
\<longrightarrow>
(1, 1, 0, 1)
*)

term "(1, 1, 0, 1) :: nat \<times> nat \<times> nat \<times> nat"

type_synonym mat2 = "nat \<times> nat \<times> nat \<times> nat"

term "(1, 1, 0, 1) :: mat2"

fun mat_mul :: "mat2 \<Rightarrow> mat2 \<Rightarrow> mat2"
  where
    "mat_mul (a1, b1, c1, d1) (a2, b2, c2, d2) = (a1 * a2 + b1 * c2, a1 * b2 + b1 * d2, c1 * a2 + d1 * c2, c1 * b2 + d1 * d2)"

definition I :: mat2 
  where
    "I = (1, 0, 0, 1)"

primrec mat_pow :: "mat2 \<Rightarrow> nat \<Rightarrow> mat2"
  where
    "mat_pow M 0 = I"
  | "mat_pow M (Suc n) = mat_mul (mat_pow M n) M"

value "mat_pow (1,1,0,1) 5"

lemma "mat_pow (1, 1, 0, 1) n = (1, n, 0, 1)"
proof (induction n)
  case 0
  then show ?case 
    by (simp add: I_def)
next
  case (Suc n)
  then show ?case
  proof -
    have "mat_pow (1, 1, 0, 1) (Suc n) = mat_mul (mat_pow (1, 1, 0, 1) n) (1, 1, 0, 1)"
      by (simp only: mat_pow.simps(2))
    also have "... = mat_mul (1, n, 0, 1) (1, 1, 0, 1)"
      using Suc
      by simp
    also have "... = (1, n + 1, 0, 1)"
      by simp
    also have "... = (1, Suc n, 0, 1)"
      by simp
    finally show ?thesis .
  qed
qed

lemma n2:
  fixes n::nat
  assumes "n > 2"
  shows "n^2 > 2*n + 1"
  using assms
proof (induction n)
  case 0
  then show ?case
    by simp
next
  case (Suc n)
  then show ?case
  proof (cases "n = 2")
    case True
    then show ?thesis
      by simp
  next
    case False
    with Suc have "n > 2" by simp
    show ?thesis
    proof -
      have "2 * Suc n + 1 < 2 * Suc n + 2*n"
        using \<open>n > 2\<close>
        by simp
      also have "... = 2*n + 1 + 2*n + 1"
        by simp
      also have "... < n^2 + 2*n + 1"
        using Suc \<open>n > 2\<close>
        by simp
      also have "... = (n + 1)^2"
        by (simp add: power2_eq_square)
      finally show ?thesis 
        by simp
    qed
  qed
qed

lemma
  fixes n::nat
  assumes "n \<ge> 5"
  shows "2^n > n^2"
  using assms
proof (induction n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  then show ?case
  proof (cases "n = 4")
    case True
    then show ?thesis
      by simp
  next
    case False
    with Suc have "n \<ge> 5" using Suc(2) by simp
    show ?thesis
    proof -
      have "(Suc n)^2 = (n^2 + 2*n + 1)"
        by (simp add: power2_eq_square)
      also have "... < n^2 + n^2"
        using Suc(2) n2 \<open>n \<ge> 5\<close>
        by simp
      also have "... = 2 * n^2"
        by simp
      also have "... < 2 * 2^n"
        using Suc \<open>n \<ge> 5\<close>
        by simp
      also have "... = 2^(n + 1)"
        by simp
      also have "... = 2^(Suc n)"
        by simp
      finally show ?thesis .
    qed
  qed
qed

lemma n2':
  fixes n::nat
  assumes "n \<ge> 3"
  shows "n^2 > 2*n + 1"
  using assms
proof (induction n rule: nat_induct_at_least)
  case base
  then show ?case 
    by simp
next
  case (Suc n)
  have "2 * Suc n + 1 < 2 * (Suc n) + 2 * n"
    using \<open>n \<ge> 3\<close>
    by simp
  also have "... = 2 * n + 1 + 2 * n + 1"
    by simp
  also have "... < n^2 + 2 * n + 1"
    using Suc
    by simp
  also have "... = (n + 1)^2"
    by (simp add: power2_eq_square)
  also have "... = (Suc n)^2"
    by simp
  finally show ?case .
qed

lemma
  fixes n::nat
  assumes "n \<ge> 5"
  shows "2^n > n^2"
  using assms
proof (induction n rule: nat_induct_at_least)
  case base
  then show ?case 
    by simp
next
  case (Suc n)
  have "(Suc n)\<^sup>2 = (n + 1)^2"
    by simp
  also have "... = n^2 + 2*n + 1"
    by (simp add: power2_eq_square)
  also have "... < n^2 + n^2"
    using n2' \<open>n \<ge> 5\<close>
    by simp
  also have "... = 2 * n^2"
    by simp
  also have "... < 2 * 2^n"
    using Suc
    by simp
  also have "... = 2^(n+1)"
    by simp
  also have "... = 2^(Suc n)"
    by simp
  finally show ?case . 
qed


end