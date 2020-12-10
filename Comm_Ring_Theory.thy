theory Comm_Ring_Theory
  imports 
          "Group_Further_Theory"
          "Topological_Space_Theory" Sketch_and_Explore
          "Jacobson_Basic_Algebra.Ring_Theory"
          "Set_Further_Theory"

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

(* ex. 0.12 *)
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


end (* entire_ring *)

text \<open>def. 0.18, see remark 0.20\<close>
locale prime_ideal = entire_ring R "(+)" "(\<cdot>)" "\<zero>" "\<one>" + ideal I  R "(+)" "(\<cdot>)" "\<zero>" "\<one>" 
  for I and R and addition (infixl "+" 65) and multiplication (infixl "\<cdot>" 70) and zero ("\<zero>") and 
unit ("\<one>") + 
assumes carrier_neq: "I \<noteq> R" and absorbent: "\<lbrakk>x \<in> R; y \<in> R\<rbrakk> \<Longrightarrow> (x \<cdot> y \<in> I) \<Longrightarrow> (x \<in> I \<or> y \<in> I)"

begin

text \<open>remark 0.21\<close>
lemma shows "\<one> \<notin> I"
proof
  assume "\<one> \<in> I"
  then have "\<And>x. \<lbrakk>\<one> \<in> I; x \<in> R\<rbrakk> \<Longrightarrow> x \<in> I"
    by (metis ideal(1) multiplicative.right_unit)
  with \<open>\<one> \<in> I\<close> have "I = R"
    by auto
  then show False
    using carrier_neq by blast
qed


text \<open>ex. 0.22\<close>
lemma
  assumes "S = {x \<in> R. x \<notin> I}"
  shows "submonoid S R (\<cdot>) \<one>"
proof
  show "S \<subseteq> R"
    using assms by force
  show "a \<cdot> b \<in> S"
    if "a \<in> S"
      and "b \<in> S"
    for a :: 'a
      and b :: 'a
    using that
    using absorbent assms by blast
  show "\<one> \<in> S"
    using assms carrier_neq ideal(1) by fastforce
qed

end (* prime_ideal *)

subsection \<open>Spectrum of a ring\<close>

context entire_ring begin

text \<open>Notation 1\<close>
definition closed_subsets :: "'a set \<Rightarrow> ('a set) set" ("\<V> _" [900] 900)
  where "\<V> \<aa> \<equiv> {I. prime_ideal I R (+) (\<cdot>) \<zero> \<one> \<and> \<aa> \<subseteq> I}"

text \<open>Notation 2\<close>
definition spectrum :: "('a set) set" ("Spec")
  where "Spec \<equiv> {I. prime_ideal I R (+) (\<cdot>) \<zero> \<one>}"

text \<open>remark 0.11\<close>
lemma closed_subsets_R [simp]:
  shows "\<V> R = {}"
  using ideal_implies_subset
  by (auto simp: closed_subsets_def prime_ideal_axioms_def prime_ideal_def)

lemma closed_subsets_empty [simp]:
  shows "\<V> {} = Spec"
  using closed_subsets_def spectrum_def by force 

lemma closed_subsets_ideal_aux:
  assumes \<aa>: "ideal \<aa> R (+) (\<cdot>) \<zero> \<one>" and \<bb>: "ideal \<bb> R (+) (\<cdot>) \<zero> \<one>"
      and prime: "prime_ideal x R (+) (\<cdot>) \<zero> \<one>" and disj: "\<aa> \<subseteq> x \<or> \<bb> \<subseteq> x" 
  shows "ideal_gen_by_prod \<aa> \<bb> \<subseteq> x"
  unfolding ideal_gen_by_prod_def additive.subgroup_generated_def
proof
  fix u
  assume u: "u \<in> additive.generate (R \<inter> {a \<cdot> b |a b. a \<in> \<aa> \<and> b \<in> \<bb>})"
  have "\<aa> \<subseteq> R" "\<bb> \<subseteq> R"
    using \<aa> \<bb> ideal_implies_subset by auto
  show "u \<in> x" using u
  proof induction
    case unit
    then show ?case
      by (meson entire_ring.ideal_zero prime prime_ideal_def)
  next
    case (incl a)
    then have "a \<in> R"
      by blast
    with incl prime_ideal.axioms [OF prime] show ?case
      by clarsimp (metis \<open>\<aa> \<subseteq> R\<close> \<open>\<bb> \<subseteq> R\<close> disj ideal.ideal subset_iff)
  next
    case (inv a)
    then have "a \<in> R"
      by blast
    with inv prime_ideal.axioms [OF prime] show ?case
      by clarsimp (metis \<open>\<aa> \<subseteq> R\<close> \<open>\<bb> \<subseteq> R\<close> disj ideal.ideal ideal_inverse subset_iff)
  next
    case (mult a b)
    then show ?case
      by (meson prime entire_ring.ideal_add prime_ideal_def)
  qed
qed


text \<open>ex. 0.13\<close>
lemma closed_subsets_ideal_iff:
  assumes "ideal \<aa> R (+) (\<cdot>) \<zero> \<one>" and "ideal \<bb> R (+) (\<cdot>) \<zero> \<one>"
  shows "\<V> (ideal_gen_by_prod \<aa> \<bb>) = (\<V> \<aa>) \<union> (\<V> \<bb>)" (is "?lhs = ?rhs")
proof
  show "?lhs \<subseteq> ?rhs"
    unfolding closed_subsets_def
    by clarsimp (meson assms ideal_implies_subset ideal_mult_in_subgroup_generated in_mono prime_ideal.absorbent)
  show "?rhs \<subseteq> ?lhs"
    unfolding closed_subsets_def
    using closed_subsets_ideal_aux [OF assms] by auto
qed

definition finsum:: "'b set \<Rightarrow> ('b \<Rightarrow> 'a) \<Rightarrow> 'a"
  where "finsum I f \<equiv> additive.finprod I f"

(* ex. 0.15 *)
lemma
  fixes J :: "'b set" and \<aa> :: "'b \<Rightarrow> 'a set"
  assumes "J \<noteq> {}" and "\<And>j. j\<in>J \<Longrightarrow> ideal (\<aa> j) R (+) (\<cdot>) \<zero> \<one>"
  shows "\<V> ({x. \<exists>I f. x = finsum I f \<and> I \<subseteq> J \<and> finite I \<and> (\<forall>i. i\<in>I \<longrightarrow> f i \<in> \<aa> i)}) = (\<Inter>j\<in>J. \<V> (\<aa> j))"
  sorry

(* ex 0.16 *)

definition is_zariski_open:: "'a set set \<Rightarrow> bool"
  where "is_zariski_open U \<equiv> generated_topology {U. \<exists>\<aa>. ideal \<aa> R (+) (\<cdot>) \<zero> \<one> \<and> U = Spec - \<V> \<aa>} U"

lemma zarisky_is_topological_space:
  shows "topological_space Spec is_zariski_open"
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
locale presheaf_of_rings = topological_space + fixes \<FF>:: "'a set \<Rightarrow> 'b set"
and \<rho>:: "'a set \<Rightarrow> 'a set \<Rightarrow> ('b \<Rightarrow> 'b)" and b:: "'b" 
assumes is_homomorphism: 
"\<And>U V. is_open U \<Longrightarrow> is_open V \<Longrightarrow> V \<subseteq> U \<Longrightarrow> 
  (\<exists>add mult zero one add' mult' zero' one'. ring_homomorphism (\<rho> U V) 
                                              (\<FF> U) add mult zero one (\<FF> V) add' mult' zero' one')"
and ring_of_empty: "\<FF> {} = {b}"
and identity_map: "\<And>U. is_open U \<Longrightarrow> \<rho> U U = id"
and assoc_comp: 
"\<And>U V W. is_open U \<Longrightarrow> is_open V \<Longrightarrow> is_open W \<Longrightarrow> V \<subseteq> U \<Longrightarrow> W \<subseteq> V \<Longrightarrow> \<rho> U W = \<rho> V W \<circ> \<rho> U V"

begin

lemma is_ring_from_is_homomorphism:
  shows "\<And>U. is_open U \<Longrightarrow> (\<exists>add mult zero one. ring (\<FF> U) add mult zero one)"
  using is_homomorphism ring_homomorphism.axioms(2) by fastforce

end (* presheaf_of_rings *)

locale morphism_presheaves_of_rings = source: presheaf_of_rings X is_open \<FF> \<rho> b + 
target: presheaf_of_rings X is_open \<FF>' \<rho>' c
for X and is_open and \<FF> and \<rho> and b and \<FF>' and \<rho>' and c + 
fixes fam_morphisms:: "'a set \<Rightarrow> ('b \<Rightarrow> 'c)"
(* Is it possible to express that we require a morphism "fam_morphisms U" only if U is open? 
If no, it's not a problem since for U not open one can still define "fam_morphisms U" to be the 
morphism constant equal to c *)
assumes is_ring_homomorphism: "\<And>U. is_open U \<Longrightarrow> (\<exists>add mult zero one add' mult' zero' one'. 
                                                    ring_homomorphism (fam_morphisms U) 
                                                                      (\<FF> U) add mult zero one 
                                                                      (\<FF>' U) add' mult' zero' one')"
and comm_diagrams: "\<And>U V. is_open U \<Longrightarrow> is_open V \<Longrightarrow> V \<subseteq> U \<Longrightarrow> 
                      (\<rho>' U V) \<circ> fam_morphisms U = fam_morphisms V \<circ> (\<rho> U V)" 

(* def 0.19 *)
locale sheaf_of_rings = presheaf_of_rings X is_open \<FF> \<rho> b 
  for X and is_open and \<FF> and \<rho> and b + 
  assumes locality: "\<forall>U I V s. open_cover_of_open_subset X is_open U I V \<longrightarrow> (\<forall>i. i\<in>I \<longrightarrow> V i \<subseteq> U) \<longrightarrow> 
s \<in> \<FF> U \<longrightarrow> (\<forall>i. i\<in>I \<longrightarrow> (\<exists>add mult zero one addi multi zeroi onei. ring (\<FF> U) add mult zero one \<longrightarrow> 
ring (\<FF> (V i)) addi multi zeroi onei \<longrightarrow> \<rho> U (V i) s = zeroi \<longrightarrow> s = zero))" and
glueing: "\<forall>U I V s. open_cover_of_open_subset X is_open U I V \<longrightarrow> (\<forall>i. i\<in>I \<longrightarrow> V i \<subseteq> U \<and> s i \<in> \<FF> (V i)) \<longrightarrow> 
(\<forall>i j. i\<in>I \<longrightarrow> j\<in>I \<longrightarrow> \<rho> (V i) (V i \<inter> V j) (s i) = \<rho> (V j) (V i \<inter> V j) (s j)) \<longrightarrow> 
(\<exists>t. t \<in> \<FF> U \<and> (\<forall>i. i\<in>I \<longrightarrow> \<rho> U (V i) t = s i))"
(* Why do we have these additional type variables? *)

(* def. 0.20 *)
locale morphism_sheaves_of_rings = morphism_presheaves_of_rings

(* ex. 0.21 *)
locale cxt_induced_sheaf = sheaf_of_rings X is_open \<FF> \<rho> b + induced_topology X is_open U
  for X and is_open and \<FF> and \<rho> and b and U +
  assumes is_open_subset: "is_open U"
begin

definition induced_sheaf:: "'a set \<Rightarrow> 'b set"
  where "induced_sheaf V \<equiv> \<FF> (U \<inter> V)"

definition induced_ring_morphisms:: "'a set \<Rightarrow> 'a set \<Rightarrow> ('b \<Rightarrow> 'b)"
  where "induced_ring_morphisms V W \<equiv> \<rho> (U \<inter> V) (U \<inter> W)"

(* Below we have an error certainly due to the additional type variables in the locale sheaf_of_rings *)
lemma induced_sheaf_is_sheaf:
  shows "sheaf_of_rings U (is_open_wrt_induced_top) induced_sheaf induced_ring_morphisms b" sorry

end (* cxt_induced_sheaf*)

(* context for construction 0.22 *) 
locale cxt_direct_image_sheaf = continuous_map X is_open X' is_open' f + 
sheaf_of_rings X is_open \<FF> \<rho> b 
for X and is_open and X' and is_open' and f and \<FF> and \<rho> and b
begin

(* def 0.24 *)
definition direct_image_sheaf:: "'b set => 'c set"
  where "direct_image_sheaf V \<equiv> \<FF> ({x. f x \<in> V})"

definition direct_image_sheaf_ring_morphisms:: "'b set \<Rightarrow> 'b set \<Rightarrow> ('c \<Rightarrow> 'c)"
  where "direct_image_sheaf_ring_morphisms U V \<equiv> \<rho> {x. f x \<in> U} {x. f x \<in> V}"

(* ex 0.23 *)
lemma 
  shows "sheaf_of_rings X' (is_open') direct_image_sheaf direct_image_sheaf_ring_morphisms b" sorry

end (* cxt_direct_image_sheaf *)


subsection \<open>Quotient Ring\<close>

locale cxt_quotient_ring = entire_ring R "(+)" "(\<cdot>)" "\<zero>" "\<one>" + submonoid S R "(\<cdot>)" "\<one>" 
  for S and R and addition (infixl "+" 65) and multiplication (infixl "\<cdot>" 70) and zero ("\<zero>") and 
unit ("\<one>")
begin

definition rel:: "('a \<times> 'a) \<Rightarrow> ('a \<times> 'a) \<Rightarrow> bool" (infix "\<sim>" 80)
  where "x \<sim> y \<equiv> \<exists>s1. s1 \<in> S \<and> s1 \<cdot> (snd y \<cdot> fst x - snd x \<cdot> fst y) = \<zero>"

lemma rel_is_equivalence:
  shows "equivalence (R \<times> S) {(x,y). x \<sim> y}" sorry

notation equivalence.Partition (infixl "'/" 75)

definition frac:: "'a \<Rightarrow> 'a \<Rightarrow> ('a \<times> 'a) set" (infixl "'/" 75)
  where "r / s \<equiv> equivalence.Class (R \<times> S) {(x,y). x \<sim> y} (r, s)"

definition add_rel_aux:: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> ('a \<times> 'a) set"
  where "add_rel_aux r s r' s' \<equiv> (r\<cdot>s' + r'\<cdot>s) / (s\<cdot>s')"

definition add_rel:: "('a \<times> 'a) set \<Rightarrow> ('a \<times> 'a) set \<Rightarrow> ('a \<times> 'a) set"
  where "add_rel X Y \<equiv> 
  let x = (SOME x. x \<in> X) in 
  let y = (SOME y. y \<in> Y) in
  add_rel_aux (fst x) (snd x) (fst y) (snd y)"

definition mult_rel_aux:: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> ('a \<times> 'a) set"
  where "mult_rel_aux r s r' s' \<equiv> (r\<cdot>r') / (s\<cdot>s')"

definition mult_rel:: "('a \<times> 'a) set \<Rightarrow> ('a \<times> 'a) set \<Rightarrow> ('a \<times> 'a) set"
  where "mult_rel X Y \<equiv>
  let x = (SOME x. x \<in> X) in
  let y = (SOME y. y \<in> Y) in
  mult_rel_aux (fst x) (snd x) (fst y) (snd y)"

definition carrier_quotient_ring:: "('a \<times> 'a) set set"
  where "carrier_quotient_ring \<equiv> equivalence.Partition (R \<times> S) {(x,y). x \<sim> y}"

(* ex. 0.26 *)
lemma
  shows "ring carrier_quotient_ring add_rel mult_rel (\<zero> / \<one>) (\<one> / \<one>)" sorry

end (* cxt_quotient_ring *)

context prime_ideal 
begin

lemma
  shows "submonoid (R \<setminus> I) R (\<cdot>) \<one>" sorry

(* definition 0.28 *)
definition carrier_local_ring_at:: "('a \<times> 'a) set set"
  where "carrier_local_ring_at \<equiv> cxt_quotient_ring.carrier_quotient_ring (R \<setminus> I) R (+) (\<cdot>) \<zero>"

end (* prime_ideal *)

(* construction 0.29 *)
context entire_ring
begin

definition is_regular:: "('a set \<Rightarrow> ('a \<times> 'a) set) \<Rightarrow> ('a set) set \<Rightarrow> bool" 
  where "is_regular s U \<equiv> 
(\<forall>\<pp>. \<pp> \<in> U \<longrightarrow> s \<pp> \<in> prime_ideal.carrier_local_ring_at \<pp> R (+) (\<cdot>) \<zero>)
\<and> (\<forall>\<pp>. \<pp> \<in> U \<longrightarrow> 
              (\<exists>V. V \<subseteq> U \<and> \<pp> \<in> V \<and> (\<exists>r f. r \<in> R \<and> f \<in> R \<and> (\<forall>\<qq>. \<qq> \<in> V \<longrightarrow> 
                                                                        f \<notin> \<qq> 
                                                                          \<and> 
                                                                        s \<qq> = cxt_quotient_ring.frac (R \<setminus> \<qq>) R (+) (\<cdot>) \<zero> r f
))))"

(* Some syntactic sugar, namely R\<^sub>\<pp>, would be good instead of prime_ideal.carrier_local_ring_at \<pp> R (+) (\<cdot>) \<zero>. 
Also, how to use the notation r/f, which stands for  cxt_quotient_ring.frac (R \<setminus> \<qq>) R (+) (\<cdot>) \<zero> r f,
outside the locale where it was defined? *)

definition sheaf_on_spec:: "('a set) set \<Rightarrow> ('a set \<Rightarrow> ('a \<times> 'a) set) set" ("\<O> _")
  where "\<O> U \<equiv> {s. (Set_Theory.map s U (\<Union>\<pp>\<in>U. prime_ideal.carrier_local_ring_at \<pp> R (+) (\<cdot>) \<zero>)) 
                  \<and> is_regular s U}"

definition add_sheaf_on_spec:: "('a set) set \<Rightarrow> ('a set \<Rightarrow> ('a \<times> 'a) set) \<Rightarrow> ('a set \<Rightarrow> ('a \<times> 'a) set) \<Rightarrow> ('a set \<Rightarrow> ('a \<times> 'a) set)"
  where "add_sheaf_on_spec U s s' \<equiv> \<lambda>\<pp>\<in>U. cxt_quotient_ring.add_rel (R \<setminus> \<pp>) R (+) (\<cdot>) \<zero> (s \<pp>) (s' \<pp>)"

lemma
  assumes "is_zariski_open U" and "is_regular s U" and "is_regular s' U" 
  shows "is_regular (add_sheaf_on_spec U s s') U" sorry

definition mult_sheaf_on_spec:: "('a set) set \<Rightarrow> ('a set \<Rightarrow> ('a \<times> 'a) set) \<Rightarrow> ('a set \<Rightarrow> ('a \<times> 'a) set) \<Rightarrow> ('a set \<Rightarrow> ('a \<times> 'a) set)"
  where "mult_sheaf_on_spec U s s' \<equiv> \<lambda>\<pp>\<in>U. cxt_quotient_ring.mult_rel (R \<setminus> \<pp>) R (+) (\<cdot>) \<zero> (s \<pp>) (s' \<pp>)"

lemma
  assumes "is_zariski_open U" and "is_regular s U" and "is_regular s' U" 
  shows "is_regular (mult_sheaf_on_spec U s s') U" sorry

definition zero_sheaf_on_spec:: "'a set set \<Rightarrow> ('a set \<Rightarrow> ('a \<times> 'a) set)"
  where "zero_sheaf_on_spec U \<equiv> \<lambda>\<pp>\<in>U. cxt_quotient_ring.frac (R \<setminus> \<pp>) R (+) (\<cdot>) \<zero> \<zero> \<one>"

lemma 
  assumes "is_zariski_open U"
  shows "is_regular (zero_sheaf_on_spec U) U" sorry

definition one_sheaf_on_spec:: "'a set set \<Rightarrow> ('a set \<Rightarrow> ('a \<times> 'a) set)"
  where "one_sheaf_on_spec U \<equiv> \<lambda>\<pp>\<in>U. cxt_quotient_ring.frac (R \<setminus> \<pp>) R (+) (\<cdot>) \<zero> \<one> \<one>"

lemma 
  assumes "is_zariski_open U"
  shows "is_regular (one_sheaf_on_spec U) U" sorry

lemma 
  assumes "is_zariski_open U"
  shows "ring (\<O> U) (add_sheaf_on_spec U) (mult_sheaf_on_spec U) (zero_sheaf_on_spec U) (one_sheaf_on_spec U)"
  sorry

definition sheaf_on_spec_ring_morphisms:: 
"'a set set \<Rightarrow> 'a set set \<Rightarrow> (('a set \<Rightarrow> ('a \<times> 'a) set) \<Rightarrow> ('a set \<Rightarrow> ('a \<times> 'a) set))"
where "sheaf_on_spec_ring_morphisms U V \<equiv> \<lambda>s. restrict s V"

lemma 
  assumes "is_zariski_open U" and "is_zariski_open V" and "V \<subseteq> U"
  shows "ring_homomorphism (sheaf_on_spec_ring_morphisms U V)
                            (\<O> U) (add_sheaf_on_spec U) (mult_sheaf_on_spec U) (zero_sheaf_on_spec U) (one_sheaf_on_spec U)
                            (\<O> V) (add_sheaf_on_spec V) (mult_sheaf_on_spec V) (zero_sheaf_on_spec V) (one_sheaf_on_spec V)"
  sorry

(* ex. 0.30 *)
lemma
  fixes a:: "'a"
  shows "sheaf_of_rings Spec is_zariski_open sheaf_on_spec sheaf_on_spec_ring_morphisms (\<lambda>\<pp>. {(a,a)})"
  sorry

end (* entire_ring *)

(* definition 0.32 *)
locale ringed_space = topological_space X is_open + sheaf_of_rings X is_open \<O> \<rho> b
  for X and is_open and \<O> and \<rho> and b

context entire_ring
begin

lemma 
  shows "ringed_space Spec is_zariski_open sheaf_on_spec sheaf_on_spec_ring_morphisms (\<lambda>\<pp>. {(a,a)})"
  sorry

end (* entire_ring *)

end