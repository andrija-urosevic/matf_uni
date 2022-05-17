theory Liste
  imports Main

begin

term "[1, 2, 3]"
term "[1::nat, 2 ,3]"
term "[1,2,3] :: nat list"
term "[] :: nat list"

term "(1::nat) # [2, 3]"

datatype 'a lista = Prazna 
                  | Dodaj 'a "'a lista"

primrec duzina' :: "'a lista \<Rightarrow> nat" 
  where
    "duzina' Prazna = 0"
  | "duzina' (Dodaj x xs) = 1 + duzina' xs"

term "Dodaj 1 (Dodaj 2 (Dodaj (3::nat) Prazna))"
value "duzina' (Dodaj 1 (Dodaj 2 (Dodaj (3::nat) Prazna)))"

primrec nadovezi' :: "'a lista \<Rightarrow> 'a lista \<Rightarrow> 'a lista"
  where
    "nadovezi' Prazna ys = ys"
  | "nadovezi' (Dodaj x xs) ys = Dodaj x (nadovezi' xs ys)"

primrec obrni' :: "'a lista \<Rightarrow> 'a lista" 
  where
    "obrni' Prazna = Prazna"
  | "obrni' (Dodaj x xs) = nadovezi' (obrni' xs) (Dodaj x Prazna)"

value "obrni' (Dodaj 1 (Dodaj 2 (Dodaj (3::nat) Prazna)))"

primrec duzina :: "'a list \<Rightarrow> nat"
  where
    "duzina [] = 0" 
  | "duzina (x # xs) = 1 + duzina xs"

value "duzina [1,2,2,3,3::nat]"
value "length [1,2,2,3,3::nat]"

lemma duzina_length:
  shows "duzina xs = length xs"
  by (induction xs) auto

lemma duzina_length_isar:
  shows "duzina xs = length xs"
proof (induction xs)
  case Nil
  then show ?case
    by simp
next
  case (Cons a xs)
  have "duzina (x # xs) = 1 + duzina xs" by simp
  also have "... = 1 + length xs" using Cons by simp
  finally show ?case by simp
qed

primrec prebroj :: "'a list \<Rightarrow> 'a \<Rightarrow> nat" 
  where
    "prebroj [] a = 0"
  | "prebroj  (x # xs) a = (if x = a then 1 else 0) + prebroj xs a"

lemma prebroj_duzina:
  shows "prebroj xs a \<le> duzina xs"
  by (induction xs) auto

lemma prebroj_duzina_isar:
  shows "prebroj xs a \<le> duzina xs"
proof (induction xs)
  case Nil
  then show ?case by simp
next
  case (Cons aa xs)
  have "prebroj (aa # xs) a = (if aa=a then 1 else 0) + prebroj xs a" by simp
  also have "... \<le> 1 + prebroj xs a" by simp
  also have "... \<le> 1 + duzina xs" using Cons by simp
  also have "... = duzina (aa # xs)" by simp  
  finally show ?case by simp
qed

value "count_list [1::nat, 1, 1, 2, 3] 1"

lemma prebroj_count_list:
  shows "prebroj xs x = count_list xs x"
  by (induction xs) auto

primrec sadrzi :: "'a list \<Rightarrow> 'a \<Rightarrow> bool"
  where
    "sadrzi [] a = False"
  | "sadrzi (x # xs) a = (x=a \<or> sadrzi xs a)"

value "sadrzi [1::nat, 2, 3, 4] 2"
value "[1::nat, 2, 3, 4]"
value "set [1::nat, 2, 3, 4]"
value "2 \<in> set [1::nat, 2, 3, 4]"

lemma sadrzi_in_set:
  shows "sadrzi xs a \<longleftrightarrow> a \<in> set xs"
  by (induction xs) auto
    
primrec skup :: "'a list \<Rightarrow> 'a set"
  where
    "skup [] = {}"
  | "skup (x # xs) = {x} \<union> skup xs"

lemma skup_set:
  shows "skup xs = set xs"
  by (induction xs) auto

primrec nadovezi :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list"
  where
    "nadovezi [] ys = ys"
  | "nadovezi (x # xs) ys = x # nadovezi xs ys"

value "nadovezi [1, 2] [3, 4::nat]"
value "[1, 2] @ [3, 4::nat]"

lemma nadovezi_append:
  shows "nadovezi xs ys = xs @ ys"
  by (induction xs) auto

lemma duzina_nadovezi:
  shows "duzina (nadovezi xs ys) = duzina xs + duzina ys"
  by (induction xs) auto

lemma duzina_nadovezi_isar:
  shows "duzina (nadovezi xs ys) = duzina xs + duzina ys"
proof (induction xs)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  have "duzina (nadovezi (a # xs) ys) = duzina (a # nadovezi xs ys)" by simp
  also have "... = 1 + duzina (nadovezi xs ys)" by simp
  also have "... = 1 + duzina xs + duzina ys" using Cons by simp
  also have "... = duzina (a # xs) + duzina ys" by simp
  finally show ?case .
qed

lemma skup_nadovezi:
  shows "skup (nadovezi xs ys) = skup xs \<union> skup ys"
  by (induction xs) auto

lemma sadrzi_nadovezi:
  shows "sadrzi (nadovezi xs ys) a = (sadrzi xs a \<or> sadrzi ys a)"
  by (induction xs) auto

primrec obrni :: "'a list \<Rightarrow> 'a list" 
  where
    "obrni [] = []"
  | "obrni (x # xs) = nadovezi (obrni xs) [x]"

value "obrni [1,2,3::nat]"

lemma obrni_rev:
  shows "obrni xs = rev xs"
  by (induction xs) (auto simp add: nadovezi_append)

lemma obrni_obrni:
  shows "obrni (obrni xs) = xs"
  by (induction xs) (auto simp add: nadovezi_append obrni_rev)

lemma nadovezi_prazno:
  shows "nadovezi xs [] = xs"
  by (induction xs) auto

lemma nadovezi_asoc:
  shows "nadovezi (nadovezi xs ys) zs = nadovezi xs (nadovezi ys zs)"
  by (induction xs) auto

lemma obrni_nadovezi:
  shows "obrni (nadovezi xs ys) = nadovezi (obrni ys) (obrni xs)"
  apply (induction xs) 
   apply (auto simp add: nadovezi_prazno) 
  apply (auto simp add: nadovezi_asoc)
  done

lemma obrni_obrni':
  shows "obrni (obrni xs) = xs"
  by (induction xs) (auto simp add: obrni_nadovezi)

primrec snoc :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a list"
  where
    "snoc [] x = [x]"
  | "snoc (x1 # xs) x = x1 # snoc xs x"

primrec rev_snoc :: "'a list \<Rightarrow> 'a list"
  where
    "rev_snoc [] = []"
  | "rev_snoc (x # xs) = snoc (rev_snoc xs) x"

lemma rev_snoc_snoc:
  shows "rev_snoc (snoc xs x) = x # (rev_snoc xs)"
  by (induction xs) auto

lemma rev_snoc_rev_snoc:
  shows "rev_snoc (rev_snoc xs) = xs"
  by (induction xs) (auto simp add: rev_snoc_snoc)

primrec iter_rev :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list"
  where
    "iter_rev [] acc = acc"
  | "iter_rev (x # xs) acc = iter_rev xs (x # acc)"

lemma iter_rev_append:
  shows "iter_rev xs ys = rev xs @ ys"
  by (induction xs arbitrary: ys) auto 

lemma iter_rev_rev:
  shows "iter_rev xs [] = rev xs"
  by (induction xs) (auto simp add: iter_rev_append)

end