theory Verify
  imports Main

begin

datatype prirodni = nula | Sled prirodni

typ prirodni

term nula
term "Sled nula"
term "Sled (Sled nula)"

primrec saberi :: "prirodni \<Rightarrow> prirodni \<Rightarrow> prirodni"
  where
    "saberi nula y = y" 
  | "saberi (Sled x) y = Sled (saberi x y)"

record ('o, 'm) Category =
  Obj :: "'o set" ("obj1" 70)
  Mor :: "'m set" ("mor1" 70)
  Dom :: "'m \<Rightarrow> 'o" ("dom1 _" [80] 70)
  Cod :: "'m \<Rightarrow> 'o" ("cod1 _" [80] 70)
  Id :: "'o \<Rightarrow> 'm" ("id1 _" [80] 75)
  Comp :: "'m \<Rightarrow> 'm \<Rightarrow> 'm" (infixl ";;1" 70)

definition
"MapsTo C f X Y \<equiv>
  f \<in> Mor C \<and> Dom C f = X \<and> Cod C f = Y"

definition CompDefined:
  "CompDefined C f g \<equiv>
    f \<in> Mor C \<and> g \<in> Mor C \<and> Cod C f = Dom C g"

locale ExtCategory =
  fixes C :: "('o, 'm, 'a) Category_scheme" (structure)
  assumes CdomExt: "(Dom C) \<in> extensional (Mor C)"
  and     CcodExt: "(Cod C) \<in> extensional (Mor C)"
  and     CidExt: "(Id C) \<in> extensional (Obj C)"
  and     CcompExt:
    "(split (Comp C)) \<in> extensional ({(f, g) | f g . f = g})"

end