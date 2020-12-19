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

locale comm_ring = ring +
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
  for R and I and addition (infixl "+" 65) and multiplication (infixl "\<cdot>" 70) and zero ("\<zero>") and 
unit ("\<one>")
(* 
Note that in the locale prime ideal the order of I and R is reversed wrt the locale ideal,
so that we can introduce some syntactic sugar later. 
*)
+ assumes carrier_neq: "I \<noteq> R" and absorbent: "\<lbrakk>x \<in> R; y \<in> R\<rbrakk> \<Longrightarrow> (x \<cdot> y \<in> I) \<Longrightarrow> (x \<in> I \<or> y \<in> I)"

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


section \<open>Spectrum of a ring\<close>

subsection \<open>The Zariski Topology\<close>

context entire_ring begin

text \<open>Notation 1\<close>
definition closed_subsets :: "'a set \<Rightarrow> ('a set) set" ("\<V> _" [900] 900)
  where "\<V> \<aa> \<equiv> {I. prime_ideal R I (+) (\<cdot>) \<zero> \<one> \<and> \<aa> \<subseteq> I}"

text \<open>Notation 2\<close>
definition spectrum :: "('a set) set" ("Spec")
  where "Spec \<equiv> {I. prime_ideal R I (+) (\<cdot>) \<zero> \<one>}"

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
      and prime: "prime_ideal R x (+) (\<cdot>) \<zero> \<one>" and disj: "\<aa> \<subseteq> x \<or> \<bb> \<subseteq> x" 
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

(* def 0.17 *)
locale presheaf_of_rings = topological_space + fixes \<FF>:: "'a set \<Rightarrow> 'b set"
and \<rho>:: "'a set \<Rightarrow> 'a set \<Rightarrow> ('b \<Rightarrow> 'b)" and b:: "'b" 
and add_str:: "'a set \<Rightarrow> ('b \<Rightarrow> 'b \<Rightarrow> 'b)" (infixl "+\<^bsub>_\<^esub>" 65) 
and mult_str:: "'a set \<Rightarrow> ('b \<Rightarrow> 'b \<Rightarrow> 'b)" (infixl "\<cdot>\<^bsub>_\<^esub>" 70) 
and zero_str:: "'a set \<Rightarrow> 'b" ("\<zero>\<^bsub>_\<^esub>") and one_str:: "'a set \<Rightarrow> 'b" ("\<one>\<^bsub>_\<^esub>")
assumes is_ring_morphism: 
"\<And>U V. is_open U \<Longrightarrow> is_open V \<Longrightarrow> V \<subseteq> U \<Longrightarrow> ring_homomorphism (\<rho> U V) 
                                              (\<FF> U) (+\<^bsub>U\<^esub>) (\<cdot>\<^bsub>U\<^esub>) \<zero>\<^bsub>U\<^esub> \<one>\<^bsub>U\<^esub> 
                                              (\<FF> V) (+\<^bsub>V\<^esub>) (\<cdot>\<^bsub>V\<^esub>) \<zero>\<^bsub>V\<^esub> \<one>\<^bsub>V\<^esub>"
and ring_of_empty: "\<FF> {} = {b}"
and identity_map: "\<And>U. is_open U \<Longrightarrow> \<rho> U U = id"
and assoc_comp: 
"\<And>U V W. is_open U \<Longrightarrow> is_open V \<Longrightarrow> is_open W \<Longrightarrow> V \<subseteq> U \<Longrightarrow> W \<subseteq> V \<Longrightarrow> \<rho> U W = \<rho> V W \<circ> \<rho> U V"
begin

lemma is_ring_from_is_homomorphism:
  shows "\<And>U. is_open U \<Longrightarrow> ring (\<FF> U) (+\<^bsub>U\<^esub>) (\<cdot>\<^bsub>U\<^esub>) \<zero>\<^bsub>U\<^esub> \<one>\<^bsub>U\<^esub>"
  using is_ring_morphism ring_homomorphism.axioms(2) by fastforce

(* The small lemma below should be useful later in various places. *)
lemma
  assumes "is_open U" and "is_open V" and "is_open W" and "W \<subseteq> U \<inter> V" and "s \<in> \<FF> U" and "t \<in> \<FF> V"
and "\<rho> U W s = \<rho> V W t" and "is_open W'" and "W' \<subseteq> W"
  shows "\<rho> U W' s = \<rho> V W' t" sorry

end (* presheaf_of_rings *)

locale morphism_presheaves_of_rings = source: presheaf_of_rings X is_open \<FF> \<rho> b add_str mult_str zero_str one_str 
+ target: presheaf_of_rings X is_open \<FF>' \<rho>' c add_str' mult_str' zero_str' one_str'
for X and is_open 
and \<FF> and \<rho> and b and add_str (infixl "+\<^bsub>_\<^esub>" 65) and mult_str (infixl "\<cdot>\<^bsub>_\<^esub>" 70) 
and zero_str ("\<zero>\<^bsub>_\<^esub>") and one_str ("\<one>\<^bsub>_\<^esub>") 
and \<FF>' and \<rho>' and c and add_str' (infixl "+''\<^bsub>_\<^esub>" 65) and mult_str' (infixl "\<cdot>''\<^bsub>_\<^esub>" 70) 
and zero_str' ("\<zero>''\<^bsub>_\<^esub>") and one_str' ("\<one>''\<^bsub>_\<^esub>") + 
fixes fam_morphisms:: "'a set \<Rightarrow> ('b \<Rightarrow> 'c)"
assumes is_ring_morphism: "\<And>U. is_open U \<Longrightarrow> ring_homomorphism (fam_morphisms U) 
                                                                (\<FF> U) (+\<^bsub>U\<^esub>) (\<cdot>\<^bsub>U\<^esub>) \<zero>\<^bsub>U\<^esub> \<one>\<^bsub>U\<^esub> 
                                                                (\<FF>' U) (+'\<^bsub>U\<^esub>) (\<cdot>'\<^bsub>U\<^esub>) \<zero>'\<^bsub>U\<^esub> \<one>'\<^bsub>U\<^esub>"
and comm_diagrams: "\<And>U V. is_open U \<Longrightarrow> is_open V \<Longrightarrow> V \<subseteq> U \<Longrightarrow>
                      (\<rho>' U V) \<circ> fam_morphisms U = fam_morphisms V \<circ> (\<rho> U V)" 

(* Identity presheaf *)
lemma (in presheaf_of_rings)
  shows "morphism_presheaves_of_rings X is_open \<FF> \<rho> b add_str mult_str zero_str one_str \<FF> \<rho> b add_str mult_str zero_str one_str (\<lambda>U. id)"
  sorry

(* Composition of presheaves *)
lemma 
  assumes 
"morphism_presheaves_of_rings X is_open \<FF> \<rho> b add_str mult_str zero_str one_str \<FF>' \<rho>' b' add_str' mult_str' zero_str' one_str' \<phi>"
and 
"morphism_presheaves_of_rings X is_open \<FF>' \<rho>' b' add_str' mult_str' zero_str' one_str' \<FF>'' \<rho>'' b'' add_str'' mult_str'' zero_str'' one_str'' \<phi>'"
shows "morphism_presheaves_of_rings X is_open \<FF> \<rho> b add_str mult_str zero_str one_str \<FF>'' \<rho>'' b'' add_str'' mult_str'' zero_str'' one_str'' (\<lambda>U. \<phi>' U \<circ> \<phi> U)"
  sorry

locale iso_presheaves_of_rings =
f: morphism_presheaves_of_rings X is_open \<FF> \<rho> b add_str mult_str zero_str one_str \<FF>' \<rho>' b' add_str' mult_str' zero_str' one_str' \<phi>  
for X is_open \<FF> \<rho> b add_str mult_str zero_str one_str \<FF>' \<rho>' b' add_str' mult_str' zero_str' one_str' \<phi>
+ assumes is_inv: "\<exists>\<psi>. morphism_presheaves_of_rings X is_open \<FF>' \<rho>' b' add_str' mult_str' zero_str' one_str' \<FF> \<rho> b add_str mult_str zero_str one_str \<psi> 
\<and> (\<forall>U. is_open U \<longrightarrow> \<phi> U \<circ> \<psi> U = id \<and> \<psi> U \<circ> \<phi> U = id)"

subsection \<open>Sheaves of Rings\<close>

(* def 0.19 *)
locale sheaf_of_rings = presheaf_of_rings + 
  assumes locality: "\<forall>U I V s. open_cover_of_open_subset X is_open U I V \<longrightarrow> (\<forall>i. i\<in>I \<longrightarrow> V i \<subseteq> U) \<longrightarrow> 
s \<in> \<FF> U \<longrightarrow> (\<forall>i. i\<in>I \<longrightarrow> \<rho> U (V i) s = zero_str (V i)) \<longrightarrow> s = \<zero>\<^bsub>U\<^esub>" and
glueing: "\<forall>U I V s. open_cover_of_open_subset X is_open U I V \<longrightarrow> (\<forall>i. i\<in>I \<longrightarrow> V i \<subseteq> U \<and> s i \<in> \<FF> (V i)) \<longrightarrow> 
(\<forall>i j. i\<in>I \<longrightarrow> j\<in>I \<longrightarrow> \<rho> (V i) (V i \<inter> V j) (s i) = \<rho> (V j) (V i \<inter> V j) (s j)) \<longrightarrow> 
(\<exists>t. t \<in> \<FF> U \<and> (\<forall>i. i\<in>I \<longrightarrow> \<rho> U (V i) t = s i))"

(* def. 0.20 *)
locale morphism_sheaves_of_rings = morphism_presheaves_of_rings

locale iso_sheaves_of_rings = iso_presheaves_of_rings 

(* ex. 0.21 *)
locale cxt_ind_sheaf = sheaf_of_rings X is_open \<FF> \<rho> b add_str mult_str zero_str one_str + 
ind_topology X is_open U
for X and is_open and \<FF> and \<rho> and b and add_str (infixl "+\<^bsub>_\<^esub>" 65) and mult_str (infixl "\<cdot>\<^bsub>_\<^esub>" 70) 
and zero_str ("\<zero>\<^bsub>_\<^esub>") and one_str ("\<one>\<^bsub>_\<^esub>") and U +
  assumes is_open_subset: "is_open U"
begin

definition ind_sheaf:: "'a set \<Rightarrow> 'b set"
  where "ind_sheaf V \<equiv> \<FF> (U \<inter> V)"

definition ind_ring_morphisms:: "'a set \<Rightarrow> 'a set \<Rightarrow> ('b \<Rightarrow> 'b)"
  where "ind_ring_morphisms V W \<equiv> \<rho> (U \<inter> V) (U \<inter> W)"

definition ind_add_str:: "'a set \<Rightarrow> ('b \<Rightarrow> 'b \<Rightarrow> 'b)"
  where "ind_add_str V x y \<equiv> add_str (U\<inter>V) x y"

definition ind_mult_str:: "'a set \<Rightarrow> ('b \<Rightarrow> 'b \<Rightarrow> 'b)"
  where "ind_mult_str V x y \<equiv> mult_str (U\<inter>V) x y"

definition ind_zero_str:: "'a set \<Rightarrow> 'b"
  where "ind_zero_str V \<equiv> \<zero>\<^bsub>(U\<inter>V)\<^esub>"

definition ind_one_str:: "'a set \<Rightarrow> 'b"
  where "ind_one_str V \<equiv> \<one>\<^bsub>(U\<inter>V)\<^esub>"

lemma ind_sheaf_is_sheaf:
  shows "sheaf_of_rings U (ind_is_open) ind_sheaf ind_ring_morphisms b
ind_add_str ind_mult_str ind_zero_str ind_one_str"
  sorry

end (* cxt_ind_sheaf*)

(* context for construction 0.22 *)
locale cxt_direct_im_sheaf = continuous_map + sheaf_of_rings
begin

(* def 0.24 *)
definition direct_im_sheaf:: "'b set => 'c set"
  where "direct_im_sheaf V \<equiv> \<FF> (f\<^sup>\<inverse> V)"

definition direct_im_sheaf_ring_morphisms:: "'b set \<Rightarrow> 'b set \<Rightarrow> ('c \<Rightarrow> 'c)"
  where "direct_im_sheaf_ring_morphisms U V \<equiv> \<rho> (f\<^sup>\<inverse> U) (f\<^sup>\<inverse> V)"

(* ex 0.23 *)
lemma 
  shows "sheaf_of_rings X' (is_open') direct_im_sheaf direct_im_sheaf_ring_morphisms b
(\<lambda>V x y. add_str (f\<^sup>\<inverse> V) x y) (\<lambda>V x y. mult_str (f\<^sup>\<inverse> V) x y) (\<lambda>V. zero_str (f\<^sup>\<inverse> V)) (\<lambda>V. one_str (f\<^sup>\<inverse> V))"
  sorry

end (* cxt_direct_im_sheaf *)


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

notation cxt_quotient_ring.carrier_quotient_ring ("_ \<^sup>\<inverse> _\<^bsub>_ _ _\<^esub>")


subsection \<open>Local Rings at Prime Ideals\<close>

context prime_ideal 
begin

lemma
  shows "submonoid (R \<setminus> I) R (\<cdot>) \<one>" sorry

(* definition 0.28 *)
definition carrier_local_ring_at:: "('a \<times> 'a) set set"
  where "carrier_local_ring_at \<equiv> (R \<setminus> I)\<^sup>\<inverse> R\<^bsub>(+) (\<cdot>) \<zero>\<^esub>"

definition add_local_ring_at:: "('a \<times> 'a) set \<Rightarrow> ('a \<times> 'a) set \<Rightarrow> ('a \<times> 'a) set"
  where "add_local_ring_at X Y \<equiv> cxt_quotient_ring.add_rel (R \<setminus> I) R (+) (\<cdot>) \<zero> X Y"

definition mult_local_ring_at:: "('a \<times> 'a) set \<Rightarrow> ('a \<times> 'a) set \<Rightarrow> ('a \<times> 'a) set"
  where "mult_local_ring_at X Y \<equiv> cxt_quotient_ring.mult_rel (R \<setminus> I) R (+) (\<cdot>) \<zero> X Y"

definition zero_local_ring_at:: "('a \<times> 'a) set"
  where "zero_local_ring_at \<equiv> cxt_quotient_ring.frac (R \<setminus> I) R (+) (\<cdot>) \<zero> \<zero> \<one>"

definition one_local_ring_at:: "('a \<times> 'a) set"
  where "one_local_ring_at \<equiv> cxt_quotient_ring.frac (R \<setminus> I) R (+) (\<cdot>) \<zero> \<one> \<one>"

end (* prime_ideal *)

notation prime_ideal.carrier_local_ring_at ("_ \<^bsub>_ _ _ _\<^esub>")

subsection \<open>Spectrum of a Ring\<close>

(* construction 0.29 *)
context entire_ring
begin

definition is_regular:: "('a set \<Rightarrow> ('a \<times> 'a) set) \<Rightarrow> ('a set) set \<Rightarrow> bool" 
  where "is_regular s U \<equiv> 
(\<forall>\<pp>. \<pp> \<in> U \<longrightarrow> s \<pp> \<in> R\<^bsub>\<pp> (+) (\<cdot>) \<zero>\<^esub>)
\<and> (\<forall>\<pp>. \<pp> \<in> U \<longrightarrow> 
              (\<exists>V. V \<subseteq> U \<and> \<pp> \<in> V \<and> (\<exists>r f. r \<in> R \<and> f \<in> R \<and> (\<forall>\<qq>. \<qq> \<in> V \<longrightarrow> 
                                                                        f \<notin> \<qq> 
                                                                          \<and> 
                                                                        s \<qq> = cxt_quotient_ring.frac (R \<setminus> \<qq>) R (+) (\<cdot>) \<zero> r f
))))"

definition sheaf_on_spec:: "('a set) set \<Rightarrow> ('a set \<Rightarrow> ('a \<times> 'a) set) set"
  where "sheaf_on_spec U \<equiv> {s. (Set_Theory.map s U (\<Union>\<pp>\<in>U. (R\<^bsub>\<pp> (+) (\<cdot>) \<zero>\<^esub>))) 
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
  shows "sheaf_of_rings Spec is_zariski_open sheaf_on_spec sheaf_on_spec_ring_morphisms (\<lambda>\<pp>. {(a,a)})
(\<lambda>U. add_sheaf_on_spec U) (\<lambda>U. mult_sheaf_on_spec U) (\<lambda>U. zero_sheaf_on_spec U) (\<lambda>U. one_sheaf_on_spec U)"
  sorry

end (* entire_ring *)


section \<open>Schemes\<close>

subsection \<open>Ringed Spaces\<close>

(* definition 0.32 *)
locale ringed_space = topological_space X is_open + sheaf_of_rings X is_open \<O> \<rho> b add_str mult_str zero_str one_str
  for X and is_open and \<O> and \<rho> and b and add_str and mult_str and zero_str and one_str

context entire_ring
begin

lemma 
  shows "ringed_space Spec is_zariski_open sheaf_on_spec sheaf_on_spec_ring_morphisms (\<lambda>\<pp>. {(a,a)})
(\<lambda>U. add_sheaf_on_spec U) (\<lambda>U. mult_sheaf_on_spec U) (\<lambda>U. zero_sheaf_on_spec U) (\<lambda>U. one_sheaf_on_spec U)"
  sorry

end (* entire_ring *)

(* definition 0.33 *)
locale morphism_ringed_spaces = source: ringed_space X is_open\<^sub>X \<O>\<^sub>X \<rho>\<^sub>X b add_str\<^sub>X mult_str\<^sub>X zero_str\<^sub>X one_str\<^sub>X 
+ target: ringed_space Y is_open\<^sub>Y \<O>\<^sub>Y \<rho>\<^sub>Y d add_str\<^sub>Y mult_str\<^sub>Y zero_str\<^sub>Y one_str\<^sub>Y
for X and is_open\<^sub>X and \<O>\<^sub>X and \<rho>\<^sub>X and b and add_str\<^sub>X and mult_str\<^sub>X and zero_str\<^sub>X and one_str\<^sub>X 
and Y and is_open\<^sub>Y and \<O>\<^sub>Y and \<rho>\<^sub>Y and d and add_str\<^sub>Y and mult_str\<^sub>Y and zero_str\<^sub>Y and one_str\<^sub>Y +
fixes f:: "'a \<Rightarrow> 'c" and \<phi>\<^sub>f:: "'c set \<Rightarrow> ('d \<Rightarrow> 'b)"
assumes is_continuous: "continuous_map X is_open\<^sub>X Y is_open\<^sub>Y f"
and is_morphism_of_sheaves: "morphism_sheaves_of_rings Y is_open\<^sub>Y \<O>\<^sub>Y \<rho>\<^sub>Y d add_str\<^sub>Y mult_str\<^sub>Y zero_str\<^sub>Y one_str\<^sub>Y 
(cxt_direct_im_sheaf.direct_im_sheaf f \<O>\<^sub>X) 
(cxt_direct_im_sheaf.direct_im_sheaf_ring_morphisms f \<rho>\<^sub>X) 
b 
(\<lambda>V x y. add_str\<^sub>X (f\<^sup>\<inverse> V) x y) 
(\<lambda>V x y. mult_str\<^sub>X (f\<^sup>\<inverse> V) x y) 
(\<lambda>V. zero_str\<^sub>X (f\<^sup>\<inverse> V)) 
(\<lambda>V. one_str\<^sub>X (f\<^sup>\<inverse> V))
\<phi>\<^sub>f"


subsection \<open>Direct Limits of Rings\<close>

(* construction 0.34 *)
locale cxt_direct_lim = sheaf_of_rings + fixes I:: "'a set set"
  assumes subset_of_opens: "\<And>U. U \<in> I \<Longrightarrow> is_open U" and 
has_lower_bound: "\<lbrakk> U\<in>I; V\<in>I \<rbrakk> \<Longrightarrow> \<exists>W\<in>I. W \<subseteq> U \<inter> V"
begin

definition rel:: "('a set \<times> 'b) \<Rightarrow> ('a set \<times> 'b) \<Rightarrow> bool" (infix "\<sim>" 80)
  where "x \<sim> y \<equiv> (fst x \<in> I \<and> fst y \<in> I) \<and> (snd x \<in> \<FF> (fst x) \<and> snd y \<in> \<FF> (fst y)) \<and>
(\<exists>W. (W \<in> I) \<and> (W \<subseteq> fst x \<inter> fst y) \<and> \<rho> (fst x \<inter> fst y) W (snd x) = \<rho> (fst x \<inter> fst y) W (snd y))"

lemma rel_is_equivalence:
  shows "equivalence (Sigma I \<FF>) {(x, y). x \<sim> y}" sorry

definition class_of:: "'a set \<Rightarrow> 'b \<Rightarrow> ('a set \<times> 'b) set" ("\<lfloor> _ , _ \<rfloor>")
  where "\<lfloor>U,s\<rfloor> \<equiv> equivalence.Class (Sigma I \<FF>) {(x, y). x \<sim> y} (U, s)"

lemma 
  assumes "U \<in> I" and "U' \<in> I"
  shows "\<lfloor>U, \<zero>\<^bsub>U\<^esub>\<rfloor> = \<lfloor>U', \<zero>\<^bsub>U'\<^esub>\<rfloor>" sorry

lemma 
  assumes "U \<in> I" and "U' \<in> I"
  shows "\<lfloor>U, \<one>\<^bsub>U\<^esub>\<rfloor> = \<lfloor>U', \<one>\<^bsub>U'\<^esub>\<rfloor>" sorry

definition op_rel_aux:: "('a set \<times> 'b) \<Rightarrow> ('a set \<times> 'b) \<Rightarrow> 'a set \<Rightarrow> bool"
  where "op_rel_aux x y z \<equiv> (z \<in> I) \<and> (z \<subseteq> fst x \<inter> fst y)"

definition add_rel:: "('a set \<times> 'b) set \<Rightarrow> ('a set \<times> 'b) set \<Rightarrow> ('a set \<times> 'b) set"
  where "add_rel \<equiv> \<lambda>X Y.
let x = (SOME x. x \<in> X) in
let y = (SOME y. y \<in> Y) in 
let z = (SOME z. op_rel_aux x y z) in
\<lfloor>z, add_str z (\<rho> (fst x) z (snd x)) (\<rho> (fst y) z (snd y))\<rfloor>"

definition mult_rel:: "('a set \<times> 'b) set \<Rightarrow> ('a set \<times> 'b) set \<Rightarrow> ('a set \<times> 'b) set"
  where "mult_rel \<equiv> \<lambda>X Y.
let x = (SOME x. x \<in> X) in
let y = (SOME y. y \<in> Y) in 
let z = (SOME z. op_rel_aux x y z) in
\<lfloor>z, mult_str z (\<rho> (fst x) z (snd x)) (\<rho> (fst y) z (snd y))\<rfloor>"

definition carrier_direct_lim:: "('a set \<times> 'b) set set"
  where "carrier_direct_lim \<equiv> equivalence.Partition (Sigma I \<FF>) {(x, y). x \<sim> y}"

(* exercise 0.35 *)
lemma
  assumes "U \<in> I"
  shows "ring carrier_direct_lim add_rel mult_rel \<lfloor>U, \<zero>\<^bsub>U\<^esub>\<rfloor> \<lfloor>U, \<one>\<^bsub>U\<^esub>\<rfloor>" sorry

(* The canonical function from \<FF> U into lim \<FF> for U \<in> I: *)
definition canonical_fun:: "'a set \<Rightarrow> 'b \<Rightarrow> ('a set \<times> 'b) set"
  where "canonical_fun U x = \<lfloor>U, x\<rfloor>"

end (* cxt_direct_lim *)

notation cxt_direct_lim.carrier_direct_lim ("lim _ _ _")

subsubsection \<open>Universal property of direct limits\<close>

lemma (in cxt_direct_lim)
  fixes A:: "'c set" and \<psi>:: "'a set \<Rightarrow> ('b \<Rightarrow> 'c)" and add:: "'c \<Rightarrow> 'c \<Rightarrow> 'c"
and mult:: "'c \<Rightarrow> 'c \<Rightarrow> 'c" and zero:: "'c" and one:: "'c" 
  assumes "ring A add mult zero one" and 
"\<And>U. U \<in> I \<Longrightarrow> ring_homomorphism (\<psi> U) (\<FF> U) (+\<^bsub>U\<^esub>) (\<cdot>\<^bsub>U\<^esub>) \<zero>\<^bsub>U\<^esub> \<one>\<^bsub>U\<^esub> A add mult zero one" 
and "\<And>U V. U \<in> I \<Longrightarrow> V \<in> I \<Longrightarrow> V \<subseteq> U \<Longrightarrow> (\<psi> V) \<circ> (\<rho> U V) = \<psi> U"
  shows "\<exists>!u. \<forall>U. U \<in> I \<longrightarrow> 
  ring_homomorphism u carrier_direct_lim add_rel mult_rel \<lfloor>U,\<zero>\<^bsub>U\<^esub>\<rfloor> \<lfloor>U,\<one>\<^bsub>U\<^esub>\<rfloor> A add mult zero one 
\<and> u \<circ> (canonical_fun U) = \<psi> U"
  sorry


subsection \<open>Locally Ringed Spaces\<close>

context presheaf_of_rings
begin

(* definition 0.37 *)
definition stalk_at:: "'a \<Rightarrow> ('a set \<times> 'b) set set"
  where "stalk_at x \<equiv> lim \<FF> \<rho> {U. is_open U \<and> x \<in> U}"

definition add_stalk_at:: "'a \<Rightarrow> ('a set \<times> 'b) set \<Rightarrow> ('a set \<times> 'b) set \<Rightarrow> ('a set \<times> 'b) set"
  where "add_stalk_at x \<equiv> cxt_direct_lim.add_rel \<FF> \<rho> add_str {U. is_open U \<and> x \<in> U}"

definition mult_stalk_at:: "'a \<Rightarrow> ('a set \<times> 'b) set \<Rightarrow> ('a set \<times> 'b) set \<Rightarrow> ('a set \<times> 'b) set"
  where "mult_stalk_at x \<equiv> cxt_direct_lim.mult_rel \<FF> \<rho> mult_str {U. is_open U \<and> x \<in> U}"

definition zero_stalk_at:: "'a \<Rightarrow> 'a set \<Rightarrow> ('a set \<times> 'b) set"
  where "zero_stalk_at x U \<equiv> cxt_direct_lim.class_of \<FF> \<rho> {U. is_open U \<and> x \<in> U} U \<zero>\<^bsub>U\<^esub>"

definition one_stalk_at:: "'a \<Rightarrow> 'a set \<Rightarrow> ('a set \<times> 'b) set"
  where "one_stalk_at x U \<equiv> cxt_direct_lim.class_of \<FF> \<rho> {U. is_open U \<and> x \<in> U} U \<one>\<^bsub>U\<^esub>"

definition class_of:: "'a \<Rightarrow> ('a set \<times> 'b) \<Rightarrow> ('a set \<times> 'b) set"
  where "class_of x p \<equiv> cxt_direct_lim.class_of \<FF> \<rho> {U. is_open U \<and> x \<in> U} (fst p) (snd p)"

end (* presheaf_of_rings *)

(* definition 0.38 *)

locale max_ideal = entire_ring R "(+)" "(\<cdot>)" "\<zero>" "\<one>" + ideal I  R "(+)" "(\<cdot>)" "\<zero>" "\<one>" 
  for R and I and addition (infixl "+" 65) and multiplication (infixl "\<cdot>" 70) and zero ("\<zero>") and 
unit ("\<one>") +
assumes neq_ring: "I \<noteq> R" and is_max: "\<And>\<aa>. ideal \<aa> R (+) (\<cdot>) \<zero> \<one> \<Longrightarrow> \<aa> \<noteq> R \<Longrightarrow> I \<subseteq> \<aa> \<Longrightarrow> I = \<aa>"
begin
lemma
  shows "\<not>(\<exists>\<aa>. ideal \<aa> R (+) (\<cdot>) \<zero> \<one> \<and> \<aa> \<noteq> R \<and> I \<subset> \<aa>)" sorry

(* A maximal ideal is prime: *)
lemma 
  shows "prime_ideal I R (+) (\<cdot>) \<zero> \<one>" sorry

end (* locale max_ideal *)

(* definition 0.39 *)
locale local_ring = entire_ring +
assumes is_unique: "\<lbrakk>I \<subseteq> R; J \<subseteq> R\<rbrakk> \<Longrightarrow> max_ideal R I (+) (\<cdot>) \<zero> \<one> \<Longrightarrow> max_ideal R J (+) (\<cdot>) \<zero> \<one> \<Longrightarrow> I = J"
and has_max_ideal: "\<exists>\<ww>. max_ideal R \<ww> (+) (\<cdot>) \<zero> \<one>"
context prime_ideal
begin

(* ex. 0.40 *)
lemma
  shows "local_ring (carrier_local_ring_at) (add_local_ring_at) (mult_local_ring_at) 
(zero_local_ring_at) (one_local_ring_at)"
  sorry

end (* prime_ideal*)

(* def. 0.41 *)
locale local_ring_morphism = 
source: local_ring A "(+)" "(\<cdot>)" \<zero> \<one> + target: local_ring B "(+')" "(\<cdot>')" "\<zero>'" "\<one>'"
+ ring_homomorphism f A "(+)" "(\<cdot>)" "\<zero>" "\<one>" B "(+')" "(\<cdot>')" "\<zero>'" "\<one>'"
for f and 
A and addition (infixl "+" 65) and multiplication (infixl "\<cdot>" 70) and zero ("\<zero>") and unit ("\<one>") and 
B and addition' (infixl "+''" 65) and multiplication' (infixl "\<cdot>''" 70) and zero' ("\<zero>''") and unit' ("\<one>''")
+ assumes preimage_of_max_ideal: 
"\<lbrakk>\<ww>\<^sub>A \<subseteq> A; \<ww>\<^sub>B \<subseteq> B\<rbrakk> \<Longrightarrow> max_ideal \<ww>\<^sub>A A (+) (\<cdot>) \<zero> \<one> \<Longrightarrow> max_ideal \<ww>\<^sub>B B (+') (\<cdot>') \<zero>' \<one>' \<Longrightarrow> {x. f x \<in> \<ww>\<^sub>B} = \<ww>\<^sub>A"

(* def. 0.42 *)
locale locally_ringed_space = ringed_space +
  assumes is_local_ring: "\<And>x U. x \<in> U \<Longrightarrow> is_open U \<Longrightarrow>
local_ring (stalk_at x) (add_stalk_at x) (mult_stalk_at x) (zero_stalk_at x U) (one_stalk_at x U)"
context entire_ring
begin

(* ex. 0.43 *)
lemma
  fixes a:: "'a"
  shows "locally_ringed_space Spec is_zariski_open sheaf_on_spec sheaf_on_spec_ring_morphisms (\<lambda>\<pp>. {(a,a)})
(\<lambda>U. add_sheaf_on_spec U) (\<lambda>U. mult_sheaf_on_spec U) (\<lambda>U. zero_sheaf_on_spec U) (\<lambda>U. one_sheaf_on_spec U)"
  sorry

end (* entire_ring *)

(* Construction 0.44: induced morphism between direct limits *)
locale cxt_ind_morphism_bwt_lim = 
morphism_ringed_spaces + fixes x::"'a"
begin

definition index:: "'c set set"
  where "index \<equiv> {V. is_open\<^sub>Y V \<and> f x \<in> V}"

definition induced_morphism:: "('c set \<times> 'd) set \<Rightarrow> ('a set \<times> 'b) set"
  where "induced_morphism C \<equiv> 
let r = (SOME r. r \<in> C) in
presheaf_of_rings.class_of is_open\<^sub>X \<O>\<^sub>X \<rho>\<^sub>X x (f\<^sup>\<inverse> (fst r), \<phi>\<^sub>f (fst r) (snd r))
"
(* 
One should think of fst r as a V in index, and snd r as a d in \<O>\<^sub>Y V. 
Since induced morphism is defined on a representative of the class C, one should check that it
is well defined. 
*)

lemma 
  assumes "V \<in> index"
  shows "ring_homomorphism induced_morphism
(presheaf_of_rings.stalk_at is_open\<^sub>Y \<O>\<^sub>Y \<rho>\<^sub>Y (f x))
(presheaf_of_rings.add_stalk_at is_open\<^sub>Y \<O>\<^sub>Y \<rho>\<^sub>Y add_str\<^sub>Y (f x))
(presheaf_of_rings.mult_stalk_at is_open\<^sub>Y \<O>\<^sub>Y \<rho>\<^sub>Y mult_str\<^sub>Y (f x))
(presheaf_of_rings.zero_stalk_at is_open\<^sub>Y \<O>\<^sub>Y \<rho>\<^sub>Y zero_str\<^sub>Y (f x) V)
(presheaf_of_rings.one_stalk_at is_open\<^sub>Y \<O>\<^sub>Y \<rho>\<^sub>Y one_str\<^sub>Y (f x) V)
(presheaf_of_rings.stalk_at is_open\<^sub>X \<O>\<^sub>X \<rho>\<^sub>X x)
(presheaf_of_rings.add_stalk_at is_open\<^sub>X \<O>\<^sub>X \<rho>\<^sub>X add_str\<^sub>X x)
(presheaf_of_rings.mult_stalk_at is_open\<^sub>X \<O>\<^sub>X \<rho>\<^sub>X mult_str\<^sub>X x)
(presheaf_of_rings.zero_stalk_at is_open\<^sub>X \<O>\<^sub>X \<rho>\<^sub>X zero_str\<^sub>X x (f\<^sup>\<inverse> V))
(presheaf_of_rings.one_stalk_at is_open\<^sub>X \<O>\<^sub>X \<rho>\<^sub>X one_str\<^sub>X x (f\<^sup>\<inverse> V))
"
  sorry

end (* cxt_ind_morphism_bwt_lim *)

notation cxt_ind_morphism_bwt_lim.induced_morphism ("\<phi>\<^bsub>_ _ _ _ _ _\<^esub>")

(* definition 0.45 *)

locale morphism_locally_ringed_spaces = 
morphism_ringed_spaces +
assumes is_local_morphism: "\<And>x. x \<in> X \<Longrightarrow> local_ring_morphism \<phi>\<^bsub>is_open\<^sub>X \<O>\<^sub>X \<rho>\<^sub>X f \<phi>\<^sub>f x\<^esub> 
(presheaf_of_rings.stalk_at is_open\<^sub>Y \<O>\<^sub>Y \<rho>\<^sub>Y (f x))
(presheaf_of_rings.add_stalk_at is_open\<^sub>Y \<O>\<^sub>Y \<rho>\<^sub>Y add_str\<^sub>Y (f x))
(presheaf_of_rings.mult_stalk_at is_open\<^sub>Y \<O>\<^sub>Y \<rho>\<^sub>Y mult_str\<^sub>Y (f x))
(presheaf_of_rings.zero_stalk_at is_open\<^sub>Y \<O>\<^sub>Y \<rho>\<^sub>Y zero_str\<^sub>Y (f x) V)
(presheaf_of_rings.one_stalk_at is_open\<^sub>Y \<O>\<^sub>Y \<rho>\<^sub>Y one_str\<^sub>Y (f x) V)
(presheaf_of_rings.stalk_at is_open\<^sub>X \<O>\<^sub>X \<rho>\<^sub>X x)
(presheaf_of_rings.add_stalk_at is_open\<^sub>X \<O>\<^sub>X \<rho>\<^sub>X add_str\<^sub>X x)
(presheaf_of_rings.mult_stalk_at is_open\<^sub>X \<O>\<^sub>X \<rho>\<^sub>X mult_str\<^sub>X x)
(presheaf_of_rings.zero_stalk_at is_open\<^sub>X \<O>\<^sub>X \<rho>\<^sub>X zero_str\<^sub>X x (f\<^sup>\<inverse> V))
(presheaf_of_rings.one_stalk_at is_open\<^sub>X \<O>\<^sub>X \<rho>\<^sub>X one_str\<^sub>X x (f\<^sup>\<inverse> V))
"

locale iso_locally_ringed_spaces =
morphism_locally_ringed_spaces + homeomorphism X is_open\<^sub>X Y is_open\<^sub>Y f +
iso_presheaves_of_rings Y is_open\<^sub>Y \<O>\<^sub>Y \<rho>\<^sub>Y d add_str\<^sub>Y mult_str\<^sub>Y zero_str\<^sub>Y one_str\<^sub>Y
"cxt_direct_im_sheaf.direct_im_sheaf f \<O>\<^sub>X" 
"cxt_direct_im_sheaf.direct_im_sheaf_ring_morphisms f \<rho>\<^sub>X" 
b 
"\<lambda>V x y. add_str\<^sub>X (f\<^sup>\<inverse> V) x y" 
"\<lambda>V x y. mult_str\<^sub>X (f\<^sup>\<inverse> V) x y" 
"\<lambda>V. zero_str\<^sub>X (f\<^sup>\<inverse> V)" 
"\<lambda>V. one_str\<^sub>X (f\<^sup>\<inverse> V)"
\<phi>\<^sub>f


subsection \<open>Affine Schemes\<close>

(* definition 0.46 *)
locale affine_scheme = locally_ringed_space + entire_ring +
  fixes c:: "'c"
  assumes is_iso_to_spec: "\<exists>f \<phi>\<^sub>f. iso_locally_ringed_spaces X is_open \<O> \<rho> b add_str mult_str zero_str one_str
Spec is_zariski_open sheaf_on_spec sheaf_on_spec_ring_morphisms (\<lambda>\<pp>. {(c, c)}) (\<lambda>U. add_sheaf_on_spec U)
(\<lambda>U. mult_sheaf_on_spec U) (\<lambda>U. zero_sheaf_on_spec U) (\<lambda>U. one_sheaf_on_spec U) f \<phi>\<^sub>f"


subsection \<open>Schemes\<close>

(* def. 0.47 *)
locale scheme = locally_ringed_space + entire_ring +
  fixes c:: "'c"
  assumes are_affine_schemes: "\<forall>x. x \<in> X \<longrightarrow> (\<exists>U. is_open U \<and> x \<in> U \<and> 
affine_scheme U (ind_topology.ind_is_open is_open U) (cxt_ind_sheaf.ind_sheaf \<O> U) 
(cxt_ind_sheaf.ind_ring_morphisms \<rho> U) b (cxt_ind_sheaf.ind_add_str add_str U)
(cxt_ind_sheaf.ind_mult_str mult_str U) (cxt_ind_sheaf.ind_zero_str zero_str U)
(cxt_ind_sheaf.ind_one_str one_str U) R (+) (\<cdot>) \<zero> \<one> c
)"

context affine_scheme
begin

lemma affine_scheme_is_scheme:
  shows "scheme X is_open \<O> \<rho> b add_str mult_str zero_str one_str R (+) (\<cdot>) \<zero> \<one> c"
  sorry

end (* affine_scheme*)


end