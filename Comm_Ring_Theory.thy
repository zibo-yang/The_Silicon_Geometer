theory Comm_Ring_Theory
  imports "Jacobson_Basic_Algebra.Ring_Theory"
          "Group_Further_Theory"
          "Topological_Space_Theory"

begin

section \<open>Commutative Rings\<close> 

subsection \<open>Commutative Rings\<close>

no_notation plus (infixl "+" 65)

locale comm_ring = ring R "(+)" "(\<cdot>)" "\<zero>" "\<one>" 
  for R and addition (infixl "+" 65) and multiplication (infixl "\<cdot>" 70) and zero ("\<zero>") and unit ("\<one>") +
  assumes commutative_mult: "\<lbrakk> a \<in> R; b \<in> R \<rbrakk> \<Longrightarrow> a \<cdot> b = b \<cdot> a"

(* def 0.13 *)
definition (in ring) zero_divisor :: "'a \<Rightarrow> 'a \<Rightarrow> bool" 
  where "zero_divisor x y \<equiv> (x \<noteq> \<zero>) \<and> (y \<noteq> \<zero>) \<and> (x \<cdot> y = \<zero>)"

subsection \<open>Entire Rings\<close>

(* def 0.14 *)
locale entire_ring = comm_ring + assumes units_neq: "\<one> \<noteq> \<zero>" and 
no_zero_divisors: "\<lbrakk> x \<in> R; y \<in> R\<rbrakk> \<Longrightarrow> \<not>(zero_divisor x y)"

subsection \<open>Ideals\<close>

context entire_ring begin

(* ex. 0.16 *)
lemma shows "ideal R R (+) (\<cdot>) \<zero> \<one>" sorry 

lemma shows "ideal {\<zero>} R (+) (\<cdot>) \<zero> \<one>" sorry

definition ideal_gen_by_prod :: "'a set \<Rightarrow> 'a set \<Rightarrow> 'a set"
  where "ideal_gen_by_prod \<aa> \<bb> \<equiv> additive.subgroup_generated {x. \<exists>a b. x = a \<cdot> b \<and> a \<in> \<aa> \<and> b \<in> \<bb>}"

(* I don't know if this could be useful, but the ideal defined above is also the intersection of 
all ideals containing {a\<cdot>b | a \<in> \<aa>, b \<in> \<bb>}. So, we have the following lemma: *)

lemma
  assumes "ideal \<aa> R (+) (\<cdot>) \<zero> \<one>" and "ideal \<bb> R (+) (\<cdot>) \<zero> \<one>"
  shows "ideal_gen_by_prod \<aa> \<bb> = (\<Inter>I\<in>{I. ideal I R (+) (\<cdot>) \<zero> \<one> \<and> {x. \<exists>a b. x = a \<cdot> b \<and> a \<in> \<aa> \<and> b \<in> \<bb>} \<subseteq> I}. I)" sorry

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

subsection \<open>Spectrum of a ring\<close>

context entire_ring begin

(* notation 2 *)
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

(* The ideal defined in ex. 0.14 is also the intersection of all ideals containing \<Union>i\<in>I. \<aa>\<^sub>i *)
(* ex. 0.15 *)
lemma
  fixes J :: "'b set" and \<aa> :: "'b \<Rightarrow> 'a set"
  assumes "ideal (\<aa> j) R (+) (\<cdot>) \<zero> \<one>"
  shows "\<V> (\<Inter>I\<in>{I. ideal I R (+) (\<cdot>) \<zero> \<one> \<and> (\<Union>j\<in>J. \<aa> j) \<subseteq> I}. I) = (\<Inter>j\<in>J. \<V> (\<aa> j))" sorry

(* ex 0.16 *)
lemma zarisky_is_topological_space:
  shows "topological_space Spec (generated_topology {U. \<exists>\<aa>. ideal \<aa> R (+) (\<cdot>) \<zero> \<one> \<and> U = Spec - \<V> \<aa>})"
  sorry

end (* entire_ring *)

subsection \<open>Presheaves of Rings\<close>

(* def. 0.17 *)
(* First version using a record:

record 'a ring = 
  carrier:: "'a set"
  add:: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
  mult:: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
  zero:: "'a"
  one:: "'a"

definition trivial_ring :: "'a \<Rightarrow> 'a ring"
  where "trivial_ring a \<equiv> \<lparr>carrier = {a}, add = \<lambda>x y. a, mult = \<lambda>x y. a,zero = a, one = a\<rparr>"

locale presheaf_of_rings = topological_space + fixes \<FF>:: "'a set \<Rightarrow> 'a ring" and 
\<rho>:: "'a set \<Rightarrow> 'a set \<Rightarrow> ('a \<Rightarrow> 'a)" and a:: "'a" 
assumes is_ring: "\<And>U. is_open U \<Longrightarrow> ring (carrier (\<FF> U)) (add (\<FF> U)) (mult (\<FF> U)) (zero (\<FF> U)) (one (\<FF> U))"
and is_homomorphism: 
"\<And>U V. is_open U \<Longrightarrow> is_open V \<Longrightarrow> V \<subseteq> U \<Longrightarrow> ring_homomorphism (\<rho> U V) 
                                   (carrier (\<FF> U)) (add (\<FF> U)) (mult (\<FF> U)) (zero (\<FF> U)) (one (\<FF> U)) 
                                   (carrier (\<FF> V)) (add (\<FF> V)) (mult (\<FF> V)) (zero (\<FF> V)) (one (\<FF> V))"
and ring_of_empty: "\<FF> {} = trivial_ring a"
and identity_map: "\<And>U. is_open U \<Longrightarrow> \<rho> U U = id"
and assoc_comp: 
"\<And>U V W. is_open U \<Longrightarrow> is_open V \<Longrightarrow> is_open W \<Longrightarrow> V \<subseteq> U \<Longrightarrow> W \<subseteq> V \<Longrightarrow> \<rho> U W = \<rho> V W \<circ> \<rho> U V"
*)

(* Second version of def 0.17 without records: *)
locale presheaf_of_rings = topological_space + fixes \<FF>:: "'a set \<Rightarrow> 'a set" and 
\<rho>:: "'a set \<Rightarrow> 'a set \<Rightarrow> ('a \<Rightarrow> 'a)" and a:: "'a" 
assumes is_homomorphism: 
"\<And>U V. is_open U \<Longrightarrow> is_open V \<Longrightarrow> V \<subseteq> U \<Longrightarrow> 
  (\<exists>add mult zero one add' mult' zero' one'. ring_homomorphism (\<rho> U V) 
                                              (\<FF> U) add mult zero one (\<FF> V) add' mult' zero' one')"
and ring_of_empty: "\<FF> {} = {a}"
and identity_map: "\<And>U. is_open U \<Longrightarrow> \<rho> U U = id"
and assoc_comp: 
"\<And>U V W. is_open U \<Longrightarrow> is_open V \<Longrightarrow> is_open W \<Longrightarrow> V \<subseteq> U \<Longrightarrow> W \<subseteq> V \<Longrightarrow> \<rho> U W = \<rho> V W \<circ> \<rho> U V"

begin

lemma is_ring_from_is_homomorphism:
  shows "\<And>U. is_open U \<Longrightarrow> (\<exists>add mult zero one. ring (\<FF> U) add mult zero one)"
  using is_homomorphism ring_homomorphism.axioms(2) by fastforce

end (* presheaf_of_rings *)


end