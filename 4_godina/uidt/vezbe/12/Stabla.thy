theory Stabla
  imports Main

begin

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

end