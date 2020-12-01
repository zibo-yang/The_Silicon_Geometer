theory Comm_Ring_Theory
  imports "Jacobson_Basic_Algebra.Ring_Theory"
          "Group_Further_Theory"

begin

section \<open>Commutative Rings\<close>

no_notation plus (infixl "+" 65)

locale comm_ring = ring R "(+)" "(\<cdot>)" "\<zero>" "\<one>" 
  for R and addition (infixl "+" 65) and multiplication (infixl "\<cdot>" 70) and zero ("\<zero>") and unit ("\<one>") +
  assumes commutative_mult: "\<lbrakk> a \<in> R; b \<in> R \<rbrakk> \<Longrightarrow> a \<cdot> b = b \<cdot> a"

(* def 0.13 *)
definition (in ring) zero_divisor :: "'a \<Rightarrow> 'a \<Rightarrow> bool" 
  where "zero_divisor x y \<equiv> (x \<noteq> \<zero>) \<and> (y \<noteq> \<zero>) \<and> (x \<cdot> y = \<zero>)"

(* def 0.14 *)
locale entire_ring = comm_ring + assumes units_neq: "\<one> \<noteq> \<zero>" and 
no_zero_divisors: "\<lbrakk> x \<in> R; y \<in> R\<rbrakk> \<Longrightarrow> \<not>(zero_divisor x y)"

begin

(* ex. 0.16 *)
lemma shows "ideal R R (+) (\<cdot>) \<zero> \<one>" sorry 

lemma shows "ideal {\<zero>} R (+) (\<cdot>) \<zero> \<one>" sorry

definition ideal_gen_by_prod :: "'a set \<Rightarrow> 'a set \<Rightarrow> 'a set"
  where "ideal_gen_by_prod \<aa> \<bb> \<equiv> additive.subgroup_generated {x. \<exists>a b. x = a \<cdot> b \<and> a \<in> \<aa> \<and> b \<in> \<bb>}"

(* I don't know if this could be useful, but the ideal defined above is also the intersection of 
all ideals containing {a\<cdot>b | a \<in> \<aa>, b \<in> \<bb>}. *)

(* ex. 0.12 *)
lemma 
  assumes "ideal \<aa> R (+) (\<cdot>) \<zero> \<one>" and "ideal \<bb> R (+) (\<cdot>) \<zero> \<one>"
  shows "ideal (ideal_gen_by_prod \<aa> \<bb>) R (+) (\<cdot>) \<zero> \<one>" sorry

end (* entire_ring *)

(* def. 0.18, see remark 0.20 *)
locale prime_ideal = entire_ring R "(+)" "(\<cdot>)" "\<zero>" "\<one>" + ideal I  R "(+)" "(\<cdot>)" "\<zero>" "\<one>" 
  for I and R and addition (infixl "+" 65) and multiplication (infixl "\<cdot>" 70) and zero ("\<zero>") and 
unit ("\<one>") + 
assumes carrier_neq: "I \<noteq> R" and absorbent: "\<lbrakk>x \<in> R; y \<in> R\<rbrakk> \<Longrightarrow> (x \<cdot> y \<in> I) \<Longrightarrow> (x \<in> I \<or> y \<in> I)"

begin

(* remark 0.21 *)
lemma shows "\<one> \<notin> I" sorry

(* ex. 0.22 *)
lemma
  assumes "S = {x \<in> R. x \<notin> I}"
  shows "submonoid R S (\<cdot>) \<one>" sorry

end (* prime_ideal *)

context entire_ring
begin

definition spectrum :: "('a set) set" ("Spec")
  where "Spec \<equiv> {I. prime_ideal I R (+) (\<cdot>) \<zero> \<one>}"

(* Notation 1 *)
definition closed_subsets :: "'a set \<Rightarrow> ('a set) set" ("\<V> _")
  where "\<V> \<aa> \<equiv> {I. prime_ideal I R (+) (\<cdot>) \<zero> \<one> \<and> \<aa> \<subseteq> I}"

(* remark 0.11 *)
lemma 
  shows "\<V> R = {}" sorry

lemma
  shows "\<V> {} = Spec" sorry

(* ex. 0.13 *)
lemma
  assumes "ideal \<aa> R (+) (\<cdot>) \<zero> \<one>" and "ideal \<bb> R (+) (\<cdot>) \<zero> \<one>"
  shows "\<V> (ideal_gen_by_prod \<aa> \<bb>) = (\<V> \<aa>) \<union> (\<V> \<bb>)" sorry

end (* entire_ring *)


end