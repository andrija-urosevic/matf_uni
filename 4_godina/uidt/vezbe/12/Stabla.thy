theory Stabla
  imports Main

begin

datatype Drvo_nat = 
    Null_nat
    | Cvor_nat Drvo_nat nat Drvo_nat

term Null_nat
term Cvor_nat
term "Cvor_nat Null_nat 1 Null_nat"

term "Cvor_nat (Cvor_nat Null_nat 1 Null_nat) 3 (Cvor_nat (Cvor_nat Null_nat 4 Null_nat) 2 (Cvor_nat Null_nat 3 Null_nat))"

term "nat list"

datatype 'a Drvo = Prazno | Cvor "'a Drvo" 'a "'a Drvo"

term "Cvor Prazno (1::nat) Prazno"
term "Cvor (Cvor Prazno (4::nat) Prazno) 2 (Cvor Prazno 3 Prazno)"

primrec zbir :: "nat Drvo \<Rightarrow> nat"
  where
    "zbir Prazno = 0"
  | "zbir (Cvor l v d) = zbir l + v + zbir d"

definition test_drvo :: "nat Drvo"
  where
    "test_drvo = Cvor (Cvor Prazno 1 Prazno) 3 (Cvor (Cvor Prazno 4 Prazno) 2 (Cvor Prazno 3 Prazno))"

value "zbir test_drvo"

primrec sadrzi :: "nat Drvo \<Rightarrow> nat \<Rightarrow> bool"
  where
    "sadrzi Prazno _ = False"
  | "sadrzi (Cvor l v d) x = (sadrzi l x \<or> v = x \<or> sadrzi d x)"

value test_drvo
value "sadrzi test_drvo 3"
value "sadrzi test_drvo 5"

primrec skup 
  where
    "skup Prazno = {}"
  | "skup (Cvor l v d) = skup l \<union> {v} \<union> skup d"

value "skup test_drvo"

lemma pripada_skup_sadrzi:
  shows "a \<in> skup drvo \<longleftrightarrow> sadrzi drvo a"
  by (induction drvo) auto

lemma pripada_skup_sadrzi_isar:
  shows "a \<in> skup drvo \<longleftrightarrow> sadrzi drvo a"
proof (induction drvo)
  case Prazno
  then show ?case by simp
next
  case (Cvor l x d)
  have "a \<in> skup (Cvor l x d) \<longleftrightarrow> a \<in> skup l \<union> {x} \<union> skup d" by simp
  also have "... \<longleftrightarrow> a \<in> skup l \<or> a = x \<or> a \<in> skup d" by auto
  also have "... \<longleftrightarrow> sadrzi l a \<or> a = x \<or> sadrzi d a" using Cvor by simp
  also have "... \<longleftrightarrow> sadrzi (Cvor l x d) a" by auto
  finally show ?case .
qed

primrec infiks :: "nat Drvo \<Rightarrow> nat list"
  where
    "infiks Prazno = []"
  | "infiks (Cvor l v d) = infiks l @ [v] @ infiks d"

value "infiks test_drvo"

lemma set_infiks_skup:
  shows "set (infiks drvo) = skup drvo"
  by (induction drvo) auto

primrec infiks_opt' :: "nat Drvo \<Rightarrow> nat list \<Rightarrow> nat list"
  where
    "infiks_opt' Prazno xs = xs"
  | "infiks_opt' (Cvor l v d) xs = infiks_opt' l (v # infiks_opt' d xs)"

definition infiks_opt :: "nat Drvo \<Rightarrow> nat list"
  where
    "infiks_opt drvo = infiks_opt' drvo []"

value "infiks test_drvo"
value "infiks_opt test_drvo"

lemma infiks_opt'_append:
  shows "infiks_opt' drvo xs @ ys = infiks_opt' drvo (xs @ ys)"
  by (induction drvo arbitrary: xs ys) auto

lemma infiks_infiks_opt[code]:
  shows "infiks drvo = infiks_opt drvo"
  unfolding infiks_opt_def
  by (induction drvo) (auto simp add: infiks_opt'_append)

lemma infiks_opt'_append_isar:
  shows "infiks_opt' drvo xs @ ys = infiks_opt' drvo (xs @ ys)"
proof (induction drvo arbitrary: xs ys)
  case Prazno
  then show ?case by simp
next
  case (Cvor l x d)
  have "infiks_opt' (Cvor l x d) xs @ ys = infiks_opt' l (x # infiks_opt' d xs) @ ys" by simp
  also have "... = infiks_opt' l (x # infiks_opt' d xs @ ys)" using Cvor by simp
  also have "... = infiks_opt' l (x # infiks_opt' d (xs @ ys))" using Cvor by simp
  also have "... = infiks_opt' (Cvor l x d) (xs @ ys)" by simp
  finally show ?case .
qed

lemma infiks_infiks_opt_isar:
  shows "infiks drvo = infiks_opt drvo"
  unfolding infiks_opt_def
proof (induction drvo)
  case Prazno
  then show ?case by simp
next
  case (Cvor l x d)
  have "infiks (Cvor l x d) = infiks l @ [x] @ infiks d" by simp
  also have "... = infiks_opt' l [] @ [x] @ infiks_opt' d []" using Cvor by simp
  also have "... = infiks_opt' l [] @ (x # infiks_opt' d [])" by simp
  also have "... = infiks_opt' l (x # infiks_opt' d [])" by (simp add: infiks_opt'_append_isar)
  also have "... = infiks_opt' (Cvor l x d) []" by simp
  finally show ?case .
qed

primrec sortirano 
  where
    "sortirano Prazno \<longleftrightarrow> True"
  | "sortirano (Cvor l v d) \<longleftrightarrow> sortirano l \<and> sortirano d \<and> 
                                (\<forall> x \<in> skup l. x \<le> v) \<and> (\<forall> x \<in> skup d. v \<le> x)"

value test_drvo
value "sortirano test_drvo"
value "infiks test_drvo"

definition test_drvo_sortirano :: "nat Drvo"
  where
    "test_drvo_sortirano = Cvor (Cvor Prazno 1 (Cvor Prazno 2 Prazno)) 3 (Cvor (Cvor Prazno 3 Prazno) 4 Prazno)"

value test_drvo_sortirano
value "sortirano test_drvo_sortirano"
value "infiks test_drvo_sortirano"

lemma sortirano_sorted_infiks:
  assumes "sortirano drvo"
  shows "sorted (infiks drvo)"
  using assms
  by (induction drvo) (auto simp add: sorted_append le_trans set_infiks_skup)


primrec ubaci :: "nat \<Rightarrow> nat Drvo \<Rightarrow> nat Drvo"
  where
    "ubaci v Prazno = (Cvor Prazno v Prazno)"
  | "ubaci v (Cvor l v' d) = (if v \<le> v' then Cvor (ubaci v l) v' d else Cvor l v' (ubaci v d))"

value "ubaci 3 Prazno"
value "ubaci 1 test_drvo_sortirano"

lemma sadrzi_ubaci:
  shows "sadrzi (ubaci x drvo) x"
  by (induction drvo) auto

lemma skup_ubaci:
  shows "skup (ubaci x drvo) = {x} \<union> skup drvo"
  by (induction drvo) auto

lemma zbir_ubaci:
  shows "zbir (ubaci x drvo) = x + zbir drvo"
  by (induction drvo) auto

lemma sortirano_ubaci:
  assumes "sortirano drvo"
  shows "sortirano (ubaci x drvo)"
  using assms
  by (induction drvo) (auto simp add: skup_ubaci)

primrec listaUDrvo :: "nat list \<Rightarrow> nat Drvo" 
  where
    "listaUDrvo [] = Prazno"
  | "listaUDrvo (x # xs) = ubaci x (listaUDrvo xs)"

value "listaUDrvo [3, 4, 7, 2, 1, 6]"

lemma skup_listaUDrvo:
  shows "skup (listaUDrvo xs) = set xs"
  by (induction xs) (auto simp add: skup_ubaci)

lemma zbir_listaUDrvo:
  shows "zbir (listaUDrvo xs) = sum_list xs"
  by (induction xs) (auto simp add: zbir_ubaci)

lemma sortirano_listaUDrvo:
  shows "sortirano (listaUDrvo xs)"
  by (induction xs) (auto simp add: sortirano_ubaci)

definition sortiraj :: "nat list \<Rightarrow> nat list"
  where
    "sortiraj xs = infiks (listaUDrvo xs)"

value "sortiraj [3, 4, 7, 2, 1, 6]"

lemma "sorted (sortiraj xs)"
  using sortiraj_def sortirano_listaUDrvo sortirano_sorted_infiks
  by auto

lemma "set (sortiraj xs) = set xs"
  unfolding sortiraj_def
  using set_infiks_skup skup_listaUDrvo
  by auto


fun maks :: "nat Drvo \<Rightarrow> nat"
  where
    "maks Prazno = 0"
  | "maks (Cvor Prazno v Prazno) = v"
  | "maks (Cvor l v Prazno) = max (maks l) v"
  | "maks (Cvor Prazno v d) = max v (maks d)"
  | "maks (Cvor l v d) = (let maksl = maks l; maksd = maks d in max (max maksl v) maksd)"
        
value "maks (listaUDrvo [3, 4, 1, 7, 6, 3, 2])"

lemma maks_max:
  assumes "sortirano drvo" "drvo \<noteq> Prazno"
  shows "\<forall> x \<in> skup drvo. maks drvo \<ge> x"
  using assms
  sorry

primrec glava :: "nat list \<Rightarrow> nat"
  where
    "glava (x # xs) = x"

primrec kraj :: "nat list \<Rightarrow> nat"
  where
    "kraj (x # xs) = (if xs = [] then x else kraj xs)"

primrec sortirana' :: "nat list \<Rightarrow> bool"
  where
    "sortirana' [] \<longleftrightarrow> True"
  | "sortirana' (x # xs) \<longleftrightarrow> sortirana' xs \<and> (if xs = [] then True else x \<le> glava xs)"

primrec sortirana :: "nat list \<Rightarrow> bool"
  where
    "sortirana [] \<longleftrightarrow> True"
  | "sortirana (x # xs) \<longleftrightarrow> sortirana xs \<and> (\<forall> a \<in> set xs. x \<le> a)"

lemma sortitana_glava_najmanja:
  assumes "xs \<noteq> []" "sortirana xs"
  shows "\<forall> x \<in> set xs. hd xs \<le> x"
  using assms
  by (induction xs) auto

lemma sortirana_sortirana':
  shows "sortirana xs \<longleftrightarrow> sortirana' xs"
  apply (induction xs) 
   apply auto
  apply (metis glava.simps hd_in_set list.exhaust_sel)
  by (metis glava.simps le_trans list.sel(1) list.set_cases sortitana_glava_najmanja)

lemma sortirana_Cons:
  shows "sortirana (x # xs) \<longleftrightarrow> sortirana xs \<and> (\<forall> x' \<in> set xs. x \<le> x')"
  by (induction xs) auto

lemma sortirana_append:
  shows "sortirana (xs @ ys) \<longleftrightarrow> sortirana xs \<and> sortirana ys \<and> (\<forall> x \<in> set xs. \<forall> y \<in> set ys. x \<le> y)"
  by (induction xs) auto

primrec mirror :: "'a Drvo \<Rightarrow> 'a Drvo"
  where
    "mirror Prazno = Prazno"
  | "mirror (Cvor l v d) = Cvor (mirror d) v (mirror l)"

lemma mirror_id: 
  shows "mirror (mirror drvo) = drvo"
  by (induction drvo) auto

lemma mirror_id_isar:
  shows "mirror (mirror drvo) = drvo"
proof (induction drvo)
  case Prazno
  then show ?case by simp
next
  case (Cvor l x d)
  have "mirror (mirror (Cvor l x d)) = mirror (Cvor (mirror d) x (mirror l))" by simp
  also have "... = Cvor (mirror (mirror l)) x (mirror (mirror d))" by simp
  also have "... = Cvor l x d" using Cvor by simp
  finally show ?case .
qed

primrec prefiks :: "nat Drvo \<Rightarrow> nat list"
  where
    "prefiks Prazno = []"
  | "prefiks (Cvor l v d) = [v] @ prefiks l @ prefiks d"

primrec postfiks :: "nat Drvo \<Rightarrow> nat list"
  where
    "postfiks Prazno = []"
  | "postfiks (Cvor l v d) = postfiks l @ postfiks d @ [v]"

value test_drvo
value "infiks test_drvo"
value "prefiks test_drvo"
value "postfiks test_drvo"

lemma prefiks_mirror_postfiks:
  shows "prefiks (mirror drvo) = rev (postfiks drvo)"
  by (induction drvo) auto

lemma prefiks_mirror_postfiks_isar:
  shows "prefiks (mirror drvo) = rev (postfiks drvo)"
proof (induction drvo)
  case Prazno
  then show ?case by simp
next
  case (Cvor l x d)
  have "prefiks (mirror (Cvor l x d)) = prefiks (Cvor (mirror d) x (mirror l))" by simp
  also have "... = [x] @ prefiks (mirror d) @ prefiks (mirror l)" by simp
  also have "... = [x] @ rev (postfiks d) @ rev (postfiks l)" using Cvor by simp
  also have "... = [x] @ rev (postfiks l @ postfiks d)" by simp
  also have "... = rev [x] @ rev (postfiks l @ postfiks d)" by simp
  also have "... = rev (postfiks l @ postfiks d @ [x])" by simp
  also have "... = rev (postfiks (Cvor l x d))" by simp
  finally show ?case .
qed


(*
datatype Izraz = 
    Const nat 
  | PlusI Izraz Izraz 
  | MinusI Izraz Izraz
  | PutaI Izraz Izraz

term PutaI
term "PutaI (Const 2) (Const 1)"
term "PutaI (Const 2)"

primrec vrednost :: "Izraz \<Rightarrow> nat"
  where
    "vrednost (Const x) = x"
  | "vrednost (PlusI x y) = vrednost x + vrednost y"
  | "vrednost (MinusI x y) = vrednost x - vrednost y"
  | "vrednost (PutaI x y) = vrednost x * vrednost y"

value "vrednost (Const 3)"
value "vrednost (PlusI (Const 3) (Const 2))"
value "vrednost (MinusI (Const 3) (Const 2))"
value "vrednost (PutaI (Const 3) (Const 2))"
value "vrednost (MinusI (Const 2) (Const 3))"

definition x1 :: "Izraz" 
  where
    "x1 = PlusI (Const 3) (Const 5)"

value "vrednost x1"

definition x2 :: "Izraz"
  where
    "x2 = PutaI (Const 3) (MinusI (Const 5) (Const 2))"

value "vrednost x2"

definition x3 :: "Izraz"
  where
    "x3 = PutaI (PlusI (Const 3) (Const 4)) (MinusI (Const 5) (Const 2))"

value "vrednost x3"

datatype Operacija = 
      OpPlus 
    | OpMinus 
    | OpPuta 
    | OpPush nat

type_synonym Stek = "nat list"

fun izvrsiOp :: "Operacija \<Rightarrow> Stek \<Rightarrow> Stek"
  where
    "izvrsiOp (OpPush x) xs = x # xs"
  | "izvrsiOp OpPlus (x # y # xs) = (x + y) # xs"
  | "izvrsiOp OpMinus (x # y # xs) = (x - y) # xs"
  | "izvrsiOp OpPuta (x # y # xs) = (x * y) # xs"

type_synonym Program = "Operacija list"
primrec prevedi :: "Izraz \<Rightarrow> Program"
  where
    "prevedi (Const x) = [(OpPush x)]"
  | "prevedi (PlusI x y) = OpPlus # prevedi x @ prevedi y"
  | "prevedi (MinusI x y) = OpMinus # prevedi x @ prevedi y"
  | "prevedi (PutaI x y) = OpPuta # prevedi x @ prevedi y"

value x1
value "prevedi x1"
value x2
value "prevedi x2"
value x3
value "prevedi x3"

primrec izvrsiProgram :: "Program \<Rightarrow> Stek \<Rightarrow> Stek"
  where
    "izvrsiProgram [] s = s"
  | "izvrsiProgram (x # xs) s = izvrsiOp x (izvrsiProgram xs s)"

value "izvrsiProgram (prevedi x1) []"
value "izvrsiProgram (prevedi x2) []"
value "izvrsiProgram (prevedi x3) []"

definition racunar
  where
    "racunar x = hd (izvrsiProgram (prevedi x) [])"

value "racunar x1"

lemma izvrsiProgram_append:
  shows "izvrsiProgram (p1 @ p2) s = izvrsiProgram  p1 (izvrsiProgram p2 s)"
  by (induction p1) auto

lemma izvrsiProgram_prevedi:
  shows "izvrsiProgram (prevedi x) s = vrednost x # s"
  using izvrsiProgram_append
  by (induction x arbitrary:s) auto

lemma racunar_vrednost:
  shows "racunar x = vrednost x"
  unfolding racunar_def
  using izvrsiProgram_append izvrsiProgram_prevedi
  by (induction x) auto
*)

end