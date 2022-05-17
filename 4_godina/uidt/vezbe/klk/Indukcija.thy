theory Indukcija
  imports Main


begin

(*
1. 
0 + 1 + 2 + 3 + ... + (n - 1) = n * (n - 1) / 2 

n   s
0 : 0
1 : 0
2 : 1
3 : 3
4 : 6

*)

primrec trougaoni :: "nat \<Rightarrow> nat"
  where
  "trougaoni 0 = 0"
| "trougaoni (Suc n) = (Suc n) + trougaoni n"

value "trougaoni 3"

lemma "trougaoni n = n * (n + 1) div 2"
proof (induction n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  have "trougaoni (Suc n) = (Suc n) + trougaoni n" by simp
  also have "... = (Suc n) + n * (n + 1) div 2" using Suc by simp
  also have "... = n + 1 + n * (n + 1) div 2" by simp
  also have "... = 2 * (n + 1) div 2 + n * (n + 1) div 2" by simp
  also have "... = (2 + n) * (n + 1) div 2" by simp
  also have "... = (1 + Suc n) * (Suc n) div 2" by simp 
  also have "... = Suc n * (Suc n + 1) div 2" by simp
  finally show ?case by simp
qed

(*
2.

1 + 3 + 5 + . . . + (2 \<^emph> n − 1) = n \<^emph> n 
1   2   3                n

2*(n+1) - 1 = 2*n + 1
*)

primrec zbir_neparnih :: "nat \<Rightarrow> nat"
  where
    "zbir_neparnih 0 = 0"
  | "zbir_neparnih (Suc n) = 2*n + 1 + zbir_neparnih n"

lemma "zbir_neparnih n = n * n"
proof (induction n)
  case 0
  then show ?case
    by (simp only: zbir_neparnih.simps(1))
next
  case (Suc n)
  then show ?case
  proof -
    have "zbir_neparnih (Suc n) = 2*n + 1 + zbir_neparnih n"
      by (simp only: zbir_neparnih.simps(2))
    also have "... = 2*n + 1 + n*n" by (simp only: Suc)
    also have "... = (n + 2) * n + 1" by simp
    also have "... = (n + 1 + 1) * n + 1" by simp
    also have "... = (n + 1)*n + n + 1" by simp
    also have "... = (n + 1)*(n + 1)" by simp
    finally show ?thesis by simp
  qed
qed

(*
3.
-1+3-5+. . .+(-1)^n\<^emph>(2\<^emph>n-1) = (-1)^n\<^emph>n
 1 2 3            n        
*)

primrec alternirajuci :: "nat \<Rightarrow> int"
  where
    "alternirajuci 0 = 0"
  | "alternirajuci (Suc n) = (-1)^(Suc n)*((2*(int(Suc n)) - 1)) + alternirajuci n"

lemma "alternirajuci n = (-1)^n * int(n)"
proof (induction n)
  case 0
  then show ?case
    by (simp only: alternirajuci.simps(1))
next
  case (Suc n)
  then show ?case 
  proof -
    have "alternirajuci (Suc n) = (-1)^(Suc n)*((2*(int(Suc n)) - 1)) + alternirajuci n" 
      by (simp only: alternirajuci.simps(2))
    also have "... = (-1)^(Suc n)*(2*(int(Suc n)) - 1) + (-1) ^ n * int n"
      using Suc by simp
    also have "... = (-1)^(n + 1) * int (2 * n + 1) + (-1)^n * int n" by simp
    also have "... = (-1)^(n + 1) * int (2 * n + 1) + (-1)^(n + 1) * (-1) * int n" by simp
    also have "... = (-1)^(n + 1) * (int (2 * n + 1) + (-1) * (int n))"
      by (simp add: distrib_left)
    also have "... = (-1)^(n + 1) * int (n + 1)" by simp
    finally show ?thesis by simp
  qed
qed

(*
4. (1 1 0 1)^n = (1 n 0 1)

(a1 b1  (a2 b2
 c1 d1)  c2 d2)

a1*a2+b1*c2  a1*b2+b1*d2
c1*a2+d1*c2  c1*b2+d1*d2
*)

type_synonym mat2 = "nat \<times> nat \<times> nat \<times> nat"

fun mat_mul :: "mat2 \<Rightarrow> mat2 \<Rightarrow> mat2"
  where
    "mat_mul (a1, b1, c1, d1) (a2, b2, c2, d2) = (a1*a2+b1*c2, a1*b2+b1*d2, c1*a2+d1*c2, c1*b2+d1*d2)"

definition I::mat2 where
  "I = (1, 0, 0, 1)"

primrec mat_pow :: "mat2 \<Rightarrow> nat \<Rightarrow> mat2"
  where
    "mat_pow mat 0 = I"
  | "mat_pow mat (Suc n) = mat_mul (mat_pow mat n) mat"

value "mat_pow (1, 1, 0, 1) 10"

lemma "mat_pow (1, 1, 0, 1) n = (1, n, 0, 1)"
proof (induction n)
  case 0
  then show ?case
    using I_def mat_pow.simps(1) by auto
next
  case (Suc n)
  then show ?case
  proof -
    have "mat_pow (1, 1, 0, 1) (Suc n) =  mat_mul (mat_pow (1, 1, 0, 1) n) (1, 1, 0, 1)" 
      using mat_pow.simps(2) by simp
    also have "... = mat_mul (1, n, 0, 1) (1, 1, 0, 1)" 
      using Suc by simp
    also have "... = (1, n+1, 0, 1)"
      by simp
    finally show ?thesis by simp
    qed
qed

(*
4. 
1 + 4 + 9 + ... + n^2 = n*(n + 1)*(2n + 1) / 6
1   2   3         n
*)

primrec suma_stepena :: "nat \<Rightarrow> nat"
  where
    "suma_stepena 0 = 0"
  | "suma_stepena (Suc n) = (Suc n)*(Suc n) + suma_stepena n"

lemma "suma_stepena n = n * (n + 1) * (2 * n + 1) div 6"
proof (induction n)
  case 0
  then show ?case
    by (simp only: suma_stepena.simps(1))
next
  case (Suc n)
  then show ?case
  proof -
    have "suma_stepena (Suc n) = (Suc n)*(Suc n) + suma_stepena n"
      by (simp only: suma_stepena.simps(2))
    also have "... = (Suc n)*(Suc n) + n*(n+1)*(2*n+1) div 6" 
      using Suc by simp
    also have "... = (n+1)*(n+1) + n*(n+1)*(2*n+1) div 6"
      using Suc by (simp add: algebra_simps)
    also have "... = 6*(n+1)*(n+1) div 6 + n*(n+1)*(2*n+1) div 6"
      by (simp add: algebra_simps)
    also have "... = (6*(n+1) + n*(2*n+1))*(n+1) div 6"
      by (simp add: algebra_simps)
    also have "... = (2*n*n + 7*n + 6)*(n+1) div 6"
      by (simp add: algebra_simps)
    also have "... = (n+1)*(n+2)*(2*n+3) div 6"
      by (simp add: algebra_simps)
    finally show ?thesis 
      by (simp add: algebra_simps)
  qed
qed

lemma fixes n::nat shows "6 dvd n*(n + 1)*(2*n + 1)"
proof (induction n)
  case 0
  then show ?case 
    by simp
next
  case (Suc n)
  then show ?case
  proof
    have "Suc n * (Suc n + 1) * (2 * Suc n + 1) = (n+1) * (n+1 + 1) * (2*(n+1) + 1)"
      by simp
    also have "... = (n+1)*(n+2)*(2*n+3)"
      by (simp add: algebra_simps)
    also have "... = n*(n+1)*(2*n+3) + 2*(n+1)*(2*n+3)"
      by (simp add: algebra_simps)
    also have "... = n*(n+1)*(2*n+1) + 2*n*(n+1) + 2*(n+1)*(2*n+3)"
      by (simp add: algebra_simps)
    also have "... = n*(n+1)*(2*n+1) + 2*(n+1)*(3*n+3)"
      by (simp add: algebra_simps)
    also have "... = n*(n+1)*(2*n+1) + 6*(n+1)*(n+1)"
      by (simp add: algebra_simps)
    finally show ?thesis using Suc
      by (simp del: One_nat_def)
  qed
qed

lemma fixes n::nat shows "(3::nat) dvd 5^n + 2^(n+1)"
proof (induction n)
  case 0
  then show ?case 
    by (simp add: numeral_3_eq_3)
next
  case (Suc n)
  then show ?case
  proof
    have "(5::nat) ^ Suc n + 2 ^ (Suc n + 1) = 5 ^(n + 1) + 2 ^ (n + 1 + 1)" 
      by simp
    also have "... = 5 * 5 ^ n + 2 * 2 ^(n + 1)"
      by (simp add: algebra_simps)
    also have "... = 3*5^n + 2*(5^n + 2^(n+1))"
      by simp
    finally show ?thesis
      by (smt (verit) Suc dvd_add dvd_trans dvd_triv_left dvd_triv_right)
  qed
qed

lemma square_bigger_then_sum:
  fixes n::nat
  assumes "n \<ge> 3"
  shows "n ^ 2 \<ge> 2*n + 1"
  using assms
proof (induction n rule: nat_induct_at_least)
  case base
  then show ?case 
    by simp
next
  case (Suc n)
  then show ?case
  proof -
    have "2*(Suc n) + 1 = 2*(n+1) + 1" 
      by simp
    also have "... < 2*(n+1) + 2*n"
      using Suc.hyps by (simp add: algebra_simps)
    also have "... = 2*n + 1 + 2*n + 1"
      using algebra_simps by simp
    also have "... \<le> n^2 + 2*n + 1"
      using Suc by simp 
    also have "... = (n + 1)*(n+1)"
      using algebra_simps by (simp add: power2_eq_square)
    also have "... = (Suc n)*(Suc n)"
      by simp
    also have "... = (Suc n)^2"
      using algebra_simps by (simp add: power2_eq_square)
    finally show ?thesis 
      by simp
  qed
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
  then show ?case
  proof -
    have "(Suc n)^2 = (Suc n)*(Suc n)"
      by (simp add: power2_eq_square)
    also have "... = (n+1)*(n+1)"
      by (simp add: algebra_simps)
    also have "... = n*n + 2*n + 1"
      using algebra_simps by simp
    also have "... = n^2 + 2*n + 1"
      by (simp add: power2_eq_square)
    also have "... < n^2 + n^2"
      using assms square_bigger_then_sums
  qed
qed

qed



qed


end