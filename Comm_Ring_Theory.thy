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
lemma ideal_R_R: "ideal R R (+) (\<cdot>) \<zero> \<one>"
proof qed auto

lemma ideal_0_R: "ideal {\<zero>} R (+) (\<cdot>) \<zero> \<one>"
proof
  show "monoid.invertible {\<zero>} (+) \<zero> u"
    if "u \<in> {\<zero>}"
    for u :: 'a
  proof (rule monoid.invertibleI)
    show "Group_Theory.monoid {\<zero>} (+) \<zero>"
    proof qed (use that in auto)
  qed (use that in auto)
qed auto

definition ideal_gen_by_prod :: "'a set \<Rightarrow> 'a set \<Rightarrow> 'a set"
  where "ideal_gen_by_prod \<aa> \<bb> \<equiv> additive.subgroup_generated {x. \<exists>a b. x = a \<cdot> b \<and> a \<in> \<aa> \<and> b \<in> \<bb>}"

lemma ideal_zero: "ideal A R add mult zero unit \<Longrightarrow> zero \<in> A"
  by (simp add: ideal_def subgroup_of_additive_group_of_ring_def subgroup_def submonoid_def submonoid_axioms_def)

lemma ideal_implies_subset:
  assumes "ideal A R add mult zero unit"
  shows "A \<subseteq> R"
  by (meson assms ideal_def subgroup_def subgroup_of_additive_group_of_ring_def submonoid_axioms_def submonoid_def)

lemma ideal_inverse:
  assumes "a \<in> A" "ideal A R (+) mult zero unit"
  shows "additive.inverse a \<in> A"
  by (meson additive.invertible assms entire_ring.ideal_implies_subset entire_ring_axioms ideal_def subgroup.subgroup_inverse_iff subgroup_of_additive_group_of_ring_def subsetD)

lemma ideal_add:
  assumes "a \<in> A"  "b \<in> A" "ideal A R add mult zero unit"
  shows "add a b \<in> A"
  by (meson Group_Theory.group_def assms ideal_def monoid.composition_closed subgroup_def subgroup_of_additive_group_of_ring_def)

lemma ideal_mult_in_subgroup_generated:
  assumes \<aa>: "ideal \<aa> R (+) (\<cdot>) \<zero> \<one>" and \<bb>: "ideal \<bb> R (+) (\<cdot>) \<zero> \<one>" and "a \<in> \<aa>" "b \<in> \<bb>"
  shows "a \<cdot> b \<in> ideal_gen_by_prod \<aa> \<bb>"
  proof -
  have "\<exists>x y. a \<cdot> b = x \<cdot> y \<and> x \<in> \<aa> \<and> y \<in> \<bb>"
    using assms ideal_implies_subset by blast
  with ideal_implies_subset show ?thesis
    unfolding additive.subgroup_generated_def ideal_gen_by_prod_def
    using assms ideal_implies_subset by (blast intro: additive.generate.incl)    
qed

subsection \<open>Exercises\<close>

(* I don't know if this could be useful, but the ideal defined above is also the intersection of 
all ideals containing {a\<cdot>b | a \<in> \<aa>, b \<in> \<bb>}. So, we have the following lemma: *)

lemma ideal_gen_by_prod_aux:
  assumes \<aa>: "ideal \<aa> R (+) (\<cdot>) \<zero> \<one>" and \<bb>: "ideal \<bb> R (+) (\<cdot>) \<zero> \<one>"
    and "a \<in> R" and b: "b \<in> ideal_gen_by_prod \<aa> \<bb>"
  shows "a \<cdot> b \<in> ideal_gen_by_prod \<aa> \<bb>"
  using b \<open>a \<in> R\<close>
  unfolding additive.subgroup_generated_def ideal_gen_by_prod_def
proof (induction arbitrary: a)
  case unit
  then show ?case
    by (simp add: additive.generate.unit)
next
  case (incl x u)
  with \<aa> \<bb> have "\<And>a b. \<lbrakk>a \<cdot> b \<in> R; a \<in> \<aa>; b \<in> \<bb>\<rbrakk> \<Longrightarrow> \<exists>x y. u \<cdot> (a \<cdot> b) = x \<cdot> y \<and> x \<in> \<aa> \<and> y \<in> \<bb>"
    by simp (metis ideal.ideal(1) ideal_implies_subset multiplicative.associative subset_iff)
  then show ?case
    using additive.generate.incl incl.hyps incl.prems by force 
next
  case (inv u v)
  then show ?case 
  proof clarsimp
    fix a b
    assume "v \<in> R" "a \<cdot> b \<in> R" "a \<in> \<aa>" "b \<in> \<bb>"
    then have "v \<cdot> (- a \<cdot> b) = v \<cdot> a \<cdot> (- b) \<and> v \<cdot> a \<in> \<aa> \<and> - b \<in> \<bb>"
      by (metis \<aa> \<bb> ideal.ideal(1) ideal_implies_subset ideal_inverse in_mono local.right_minus multiplicative.associative)
    then show "v \<cdot> (- a \<cdot> b) \<in> additive.generate (R \<inter> {a \<cdot> b |a b. a \<in> \<aa> \<and> b \<in> \<bb>})"
      using \<aa> \<bb> additive.subgroup_generated_def ideal_mult_in_subgroup_generated 
      unfolding ideal_gen_by_prod_def
      by presburger
  qed
next
  case (mult u v)
  then show ?case
    using additive.generate.mult additive.generate_into_G distributive(1) by force
qed


lemma ideal_subgroup_generated:
  assumes "ideal \<aa> R (+) (\<cdot>) \<zero> \<one>" and "ideal \<bb> R (+) (\<cdot>) \<zero> \<one>"
  shows "ideal (ideal_gen_by_prod \<aa> \<bb>) R (+) (\<cdot>) \<zero> \<one>"
  proof
  show "ideal_gen_by_prod \<aa> \<bb> \<subseteq> R"
    by (simp add: additive.subgroup_generated_is_subset ideal_gen_by_prod_def)
  show "a + b \<in> ideal_gen_by_prod \<aa> \<bb>"
    if "a \<in> ideal_gen_by_prod \<aa> \<bb>" "b \<in> ideal_gen_by_prod \<aa> \<bb>"
    for a b
    using that additive.subgroup_generated_is_monoid monoid.composition_closed 
    by (fastforce simp: ideal_gen_by_prod_def)
  show "\<zero> \<in> ideal_gen_by_prod \<aa> \<bb>"
    using additive.generate.unit additive.subgroup_generated_def ideal_gen_by_prod_def by presburger
  show "a + b + c = a + (b + c)"
    if "a \<in> ideal_gen_by_prod \<aa> \<bb>" "b \<in> ideal_gen_by_prod \<aa> \<bb>" "c \<in> ideal_gen_by_prod \<aa> \<bb>"
    for a b c
    using that additive.subgroup_generated_is_subset 
    unfolding ideal_gen_by_prod_def
    by blast
  show "\<zero> + a = a" "a + \<zero> = a"
    if "a \<in> ideal_gen_by_prod \<aa> \<bb>" for a
    using that additive.subgroup_generated_is_subset unfolding ideal_gen_by_prod_def    
    by blast+
  show "monoid.invertible (ideal_gen_by_prod \<aa> \<bb>) (+) \<zero> u"
    if "u \<in> ideal_gen_by_prod \<aa> \<bb>" for u 
    using that additive.subgroup_generated_is_subgroup group.invertible 
    unfolding ideal_gen_by_prod_def subgroup_def
    by fastforce
  show "a \<cdot> b \<in> ideal_gen_by_prod \<aa> \<bb>"
    if "a \<in> R" "b \<in> ideal_gen_by_prod \<aa> \<bb>" for a b
    using that by (simp add: assms ideal_gen_by_prod_aux)
  then show "b \<cdot> a \<in> ideal_gen_by_prod \<aa> \<bb>"
    if "a \<in> R" "b \<in> ideal_gen_by_prod \<aa> \<bb>" for a b
    using that
    by (metis \<open>ideal_gen_by_prod \<aa> \<bb> \<subseteq> R\<close> commutative_mult in_mono)
qed

lemma ideal_gen_by_prod_is_Inter:
  assumes "ideal \<aa> R (+) (\<cdot>) \<zero> \<one>" and "ideal \<bb> R (+) (\<cdot>) \<zero> \<one>"
  shows "ideal_gen_by_prod \<aa> \<bb> = \<Inter> {I. ideal I R (+) (\<cdot>) \<zero> \<one> \<and> {a \<cdot> b |a b. a \<in> \<aa> \<and> b \<in> \<bb>} \<subseteq> I}" 
    (is "?lhs = ?rhs")
proof
  have "x \<in> ?rhs" if "x \<in> ?lhs" for x
    using that
    unfolding ideal_gen_by_prod_def additive.subgroup_generated_def
    by induction (force simp: ideal_zero ideal_inverse ideal_add)+
  then show "?lhs \<subseteq> ?rhs" by blast
  show "?rhs \<subseteq> ?lhs" 
    using assms ideal_subgroup_generated by (force simp: ideal_mult_in_subgroup_generated)
qed

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
locale presheaf_of_rings = topological_space + fixes \<FF>:: "'a set \<Rightarrow> 'a set"
(* Is it possible to express in some way that the type 'a depends on the argument U of \<FF>? 
If no, then the \<FF> U 's are forced to be sets of elements of the same type 'a. *)
and \<rho>:: "'a set \<Rightarrow> 'a set \<Rightarrow> ('a \<Rightarrow> 'a)" and a:: "'a" 
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

locale morphism_presheaves_of_rings = source: presheaf_of_rings X is_open \<FF> \<rho> a + 
target: presheaf_of_rings X is_open \<FF>' \<rho>' a'
for X and is_open and \<FF> and \<rho> and a and \<FF>' and \<rho>' and a' + 
fixes fam_morphisms:: "'a set \<Rightarrow> ('a \<Rightarrow> 'a)"
(* Is it possible to express that we require a morphism "fam_morphisms U" only if U is open? 
If no, it's not a problem since for U not open one can still define "fam_morphisms U" to be the 
morphism constant equal to a *)
assumes is_ring_homomorphism: "\<And>U. is_open U \<Longrightarrow> (\<exists>add mult zero one add' mult' zero' one'. 
                                                    ring_homomorphism (fam_morphisms U) 
                                                                      (\<FF> U) add mult zero one 
                                                                      (\<FF>' U) add' mult' zero' one')"
and comm_diagrams: "\<And>U V. is_open U \<Longrightarrow> is_open V \<Longrightarrow> V \<subseteq> U \<Longrightarrow> 
                      (\<rho>' U V) \<circ> fam_morphisms U = fam_morphisms V \<circ> (\<rho> U V)" 

end