theory NatNum
  imports Main HOL.Nat HOL.Real


begin

typ nat
typ int
typ real

term 3
term "3::nat"
term "0::nat"
term "-3::int"

thm distrib_left
thm add_mult_distrib2

lemma
  fixes a b c d :: nat
  shows "a * ((b + c) + d) = (a * b + a * d) + a * c"
proof-
  have "a * ((b + c) + d) = a * (b + c) + a * d"
    by (rule distrib_left)
  also have "... = (a * b + a * c) + a * d"
    by (simp add: add_mult_distrib2)
  also have "... = a * b + (a * c + a * d)"
    by simp
  also have "... = a * b + (a * d + a * c)"
    by simp
  also have "... = (a * b + a * d) + a * c"
    by simp
  finally show ?thesis 
    by simp
qed

find_theorems "(_ + _) * _ = (_ * _) + (_ * _)"
thm add_mult_distrib

(* 
0 + 1 + 2 + ... + (n - 1) = n * (n - 1) / 2 
f(n) = n * (n - 1) / 2

f(0) = 0
f(1) = 0
f(2) = 1
*)
value "0 + 1 + 2::nat" (* n = 3 *)
value "3 * (3 - 1) div 2::nat"

(*
1. Formulacija: 0 + 1 + ... + n = (n + 1) * n / 2
2. Uvodjenje:   g(n) = 0 + 1 + ... + n
  2.1.          g(0) = 0
                g(Suc n) = 0 + 1 + ... + n + Suc n
                         = g(n) + Suc n
3. Dokaz:       g(n) = (n + 1) * n / 2
*)

primrec g :: "nat \<Rightarrow> nat" 
  where
    "g 0 = 0" 
  | "g (Suc n) = g n + Suc n"

value "g 10"

(* Indukcija
1. Baza:              P 0
2. Induktivni korak:  P n \<Rightarrow> P (n + 1)
*)
lemma "g n = (n + 1) * n div 2"
  by (induction n) auto

lemma "g n = (n + 1) * n div 2"
  apply (induction n)
   apply auto
  done

lemma "g n = (n + 1) * n div 2"
proof (induction n)
  case 0
  then show ?case 
    by (simp only: g.simps(1))
next
  case (Suc n)
  then show ?case
  proof -
    have "g (Suc n) = g n + Suc n" 
      by simp
    also have "... = n * (n + 1) div 2 + Suc n"
      using Suc 
      by simp
    also have "... = n * (n + 1) div 2 + 2 * (Suc n) div 2"
      by simp
    also have "... = n * (Suc n) div 2 + 2 * (Suc n) div 2"
      by simp
    also have "... = (Suc n) * (n + 2) div 2"
      by simp
    also have "... = Suc n * (Suc n + 1) div 2" 
      by simp
    also have "... = (Suc n + 1) * (Suc n) div 2"
      by simp
    finally show ?thesis .
  qed
qed

thm algebra_simps
thm field_simps

(*
1           + 3           + 5           + 9           + ... + (2 * n - 1) = n * n
(2 * 1 - 1) + (2 * 2 - 1) + (2 * 3 - 1) + (2 * 4 - 1) + ... + (2 * n - 1) = n * n
1. f(n) = 1 + 3 + 5 + 9 + ... + (2 * n - 1)
2. f 0 = 0
   f Suc n = 

*)

value "1 + 3::nat"
value "2 * 2::nat"

primrec even_sum :: "nat \<Rightarrow> nat"
  where
    "even_sum 0 = 0"
  | "even_sum (Suc n) = even_sum n + 2 * (Suc n) - 1"

lemma "even_sum n = n * n"
proof (induction n)
  case 0
  then show ?case
    by (simp only: even_sum.simps(1))
next
  case (Suc n)
  then show ?case
  proof -
    have "even_sum (Suc n) = even_sum n + 2 * (Suc n) - 1" 
      by (simp only: even_sum.simps(2))
    also have "... = n * n + 2 * (Suc n) - 1"
      using Suc
      by simp
    also have "... = n * n + 2 * n + 2 - 1"
      by simp
    also have "... = n * n + 2 * n + 1"
      by simp
    also have "... = (n + 1) * (n + 1)"
      by simp
    also have "... = (Suc n) * (Suc n)"
      by simp
    finally show ?thesis .
  qed
qed

(*
-1 + 3 - 5 + 7 - 9 + ... + (-1)^n * (2*n - 1) = (-1)^n * n
-1                 + 3                  - 5                  + ... + (-1)^n * (2*n - 1)
(-1)^1 * (2*1 - 1) + (-1)^2 * (2*2 - 1) + (-1)^3 * (2*3 - 1) + ... + (-1)^n * (2*n - 1)
*)

primrec alter_sum :: "nat \<Rightarrow> int"
  where
    "alter_sum 0 = 0"
  | "alter_sum (Suc n) = alter_sum n + (-1)^(Suc n) * (2 * (Suc n) - 1)"

lemma "alter_sum n = (-1)^n * n"
proof (induction n)
  case 0
  then show ?case 
    by (simp only: alter_sum.simps(1))
next
  case (Suc n)
  then show ?case 
  proof -
    have "alter_sum (Suc n) = alter_sum n + (-1)^(Suc n) * (2 * (Suc n) - 1)"
      by (simp only: alter_sum.simps(2))
    also have "... = (-1)^n * n + (-1)^(Suc n) * (2 * (Suc n) - 1)"
      using Suc
      by simp
    also have "... = (-1) * (-1)^(Suc n) * n + (-1)^(Suc n) * (2 * (n + 1) - 1)"
      by simp
    also have "... = (-1) * (-1)^(Suc n) * n + (-1)^(Suc n) * (2 * n + 1)"
      by simp
    also have "... = (-1) ^ (Suc n) * ((-n) + (2*n + 1))"
      by (simp add: algebra_simps)
    also have "... = (-1) ^ (Suc n) * (n + 1)"
      by simp
    also have "... = (-1) ^ (Suc n) * (Suc n)"
      by simp
    finally show ?thesis .
  qed
qed

end