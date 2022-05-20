theory Category
  imports "HOL-ZF.MainZF" "HOL-Library.FuncSet"

begin

locale Universe =
  fixes \<U> :: ZF (structure)
  assumes Uempty: "Elem Empty \<U>"
  assumes Usubset: "Elem u \<U> \<Longrightarrow> subset u \<U>"
  assumes Usingleton: "Elem u \<U> \<Longrightarrow> Elem (Singleton u) \<U>"  
  assumes Upower: "Elem u \<U> \<Longrightarrow> Elem (Power u) \<U>"
  assumes Uim: "\<lbrakk>Elem I \<U>; Elem u (Fun I \<U>)\<rbrakk> \<Longrightarrow> Elem (Sum (Range u)) \<U>"
  assumes Unat: "Elem Nat \<U>"
begin

lemma "Elem u \<U> \<Longrightarrow> Elem (Sum u) \<U>"
  sorry

lemma 
  assumes "Universe \<U>" "Elem u \<U>" "Elem v \<U>"
  shows "Elem (CartProd u v) \<U>"
  sorry

lemma 
  assumes "Universe \<U>" "Elem v \<U>" "subset u v"
  shows "Elem u \<U>"
proof -
  have "subset v \<U>" using Universe.Usubset assms(1) assms(2) by auto
  then have "subset u \<U>" using assms(3) subset_def by auto
  then show ?thesis using Power Universe.Upower Universe.Usubset assms subset_def by blast
qed

definition Uset :: "ZF \<Rightarrow> bool" where
    "Uset A = Elem A \<U>"

end

locale Order =
  fixes I :: ZF
    and leq :: "ZF \<Rightarrow> ZF \<Rightarrow> bool"
  assumes Reflexive: "Elem i I \<Longrightarrow> leq i i"
      and Transitive: "\<lbrakk>Elem i I; Elem j I; Elem k I; leq i j; leq j k\<rbrakk> \<Longrightarrow> leq i k"
      and Anti_symmetric: "\<lbrakk>Elem i I; Elem j I; leq i j; leq j i\<rbrakk> \<Longrightarrow> i = j"
begin

definition (in Order) directed
  where
    "directed \<longleftrightarrow> (Empty \<noteq> I) \<and> (\<forall> i j . Elem i I \<and> Elem i I \<and> (\<exists> k. Elem k I \<and> leq i k \<and> leq j k))"

definition (in Order) total
  where
    "total \<longleftrightarrow> (\<forall> i j. Elem i I \<and> Elem j I \<and> (leq i j \<or> leq j i))"

definition (in Order) upper_bounded
  where
    "upper_bounded J \<longleftrightarrow> (\<exists> a. Elem a I \<and> (\<forall> j. Elem j J \<and> leq j a))"

definition (in Order) inductively_ordered
  where
    "inductively_ordered \<longleftrightarrow> (\<exists> J. subset J I \<and> upper_bounded J)"

definition (in Order) le
  where
    "le x y = (leq x y \<and> x \<noteq> y)"

end

locale Category =
  fixes Ob :: "'o set"
    and Hom :: "'o \<Rightarrow> 'o \<Rightarrow> 'm set"
    and Id :: "'o \<Rightarrow> 'm"
    and Comp :: "'o \<Rightarrow> 'o \<Rightarrow> 'o \<Rightarrow> 'm \<Rightarrow> 'm \<Rightarrow> 'm"
  assumes Id_Hom:   "X \<in> Ob \<Longrightarrow> Id X \<in> Hom X X"
      and Comp_Hom: "\<lbrakk> X \<in> Ob; Y \<in> Ob; Z \<in> Ob; f \<in> Hom X Y; g \<in> Hom Y Z \<rbrakk> \<Longrightarrow> Comp Z Y X g f \<in> Hom X Z"
      and Comp_Id_Hom: "\<lbrakk> X \<in> Ob; f \<in> Hom X Y \<rbrakk> \<Longrightarrow> Comp Y X X (Id X) f = f"
      and Comp_Hom_Id: "\<lbrakk> Y \<in> Ob; f \<in> Hom X Y \<rbrakk> \<Longrightarrow> Comp Y Y X f (Id Y) = f"
      and Comp_Asoc: "\<lbrakk> X \<in> Ob; Y \<in> Ob; Z \<in> Ob; W \<in> Ob; f \<in> Hom X Y; g \<in> Hom Y Z; h \<in> Hom Z W\<rbrakk> \<Longrightarrow> 
            Comp W Z X h (Comp Z Y X g f) = Comp W Y X (Comp W Z Y h g) f "
begin

lemma Uniq_Id: "X \<in> Ob \<Longrightarrow> \<exists>! Y. (Y = Id X \<and> Y \<in> Hom X X)"
  using Id_Hom by auto

datatype ('oo, 'mm) arrow = MkArrow 'oo 'oo 'mm

fun Dom :: "('o, 'm) arrow \<Rightarrow> 'o"
  where
    "Dom (MkArrow X Y f) = X"

fun Cod :: "('o, 'm) arrow \<Rightarrow> 'o"
  where
    "Cod (MkArrow X Y f) = Y"

fun Map :: "('o, 'm) arrow \<Rightarrow> 'm"
  where
    "Map (MkArrow X Y f) = f"

abbreviation Arrow
  where 
    "Arrow f \<equiv> Dom f \<in> Ob \<and> Cod f \<in> Ob \<and> Map f \<in> Hom (Dom f) (Cod f) "

abbreviation MkIdentity
  where
    "MkIdentity X \<equiv> MkArrow X X (Id X)"

abbreviation Identity
  where
    "Identity i \<equiv> Dom i \<in> Ob \<and> Cod i \<in> Ob \<and> Dom i = Cod i \<and> Map i = Id (Dom i)" 

definition isomorphism where
  "isomorphism = True"
  

end


end