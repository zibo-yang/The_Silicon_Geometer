theory Comm_Ring_Theory
  imports 
          "Group_Further_Theory"
          "Topological_Space_Theory" 
          "Jacobson_Basic_Algebra.Ring_Theory"
          "Set_Further_Theory"

begin

section \<open>Commutative Rings\<close> 

subsection \<open>Commutative Rings\<close>

locale comm_ring = ring +
  assumes commutative_mult: "\<lbrakk> a \<in> R; b \<in> R \<rbrakk> \<Longrightarrow> a \<cdot> b = b \<cdot> a"

text \<open>The zero ring is a commutative ring.\<close>

lemma invertible_0: "monoid.invertible {0} (\<lambda>n m. 0) 0 0"
    using Group_Theory.monoid.intro monoid.unit_invertible by force

lemma zero_ring_is_ring:
  shows "ring {0::nat} (\<lambda>n m. 0) (\<lambda>n m. 0) 0 0"
  using invertible_0 by unfold_locales auto

lemma zero_ring_is_comm_ring:
  shows "comm_ring {0::nat} (\<lambda>n m. 0) (\<lambda>n m. 0) 0 0"
  by (simp add: comm_ring_axioms_def comm_ring_def zero_ring_is_ring)

no_notation plus (infixl "+" 65)

(* def 0.13 *)
definition (in ring) zero_divisor :: "'a \<Rightarrow> 'a \<Rightarrow> bool" 
  where "zero_divisor x y \<equiv> (x \<noteq> \<zero>) \<and> (y \<noteq> \<zero>) \<and> (x \<cdot> y = \<zero>)"

subsection \<open>Entire Rings\<close>

(* def 0.14 *)
locale entire_ring = comm_ring + assumes units_neq: "\<one> \<noteq> \<zero>" and 
no_zero_divisors: "\<lbrakk> x \<in> R; y \<in> R\<rbrakk> \<Longrightarrow> \<not>(zero_divisor x y)"

subsection \<open>Ideals\<close>

context comm_ring begin

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
  by (meson additive.invertible assms comm_ring.ideal_implies_subset comm_ring_axioms ideal_def subgroup.subgroup_inverse_iff subgroup_of_additive_group_of_ring_def subsetD)

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
locale prime_ideal = comm_ring R "(+)" "(\<cdot>)" "\<zero>" "\<one>" + ideal I R "(+)" "(\<cdot>)" "\<zero>" "\<one>" 
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

context comm_ring begin

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
      by (meson comm_ring.ideal_zero prime prime_ideal_def)
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
      by (meson prime comm_ring.ideal_add prime_ideal_def)
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

abbreviation finsum:: "'b set \<Rightarrow> ('b \<Rightarrow> 'a) \<Rightarrow> 'a"
  where "finsum I f \<equiv> additive.finprod I f"

lemma finsum_empty [simp]: "finsum {} f = \<zero>"
  by (simp add: additive.finprod_def)

lemma finsum_insert: 
  assumes "finite I" "i \<notin> I"
    and R: "f i \<in> R" "\<And>j. j \<in> I \<Longrightarrow> f j \<in> R"
  shows "finsum (insert i I) f = f i + finsum I f"
  unfolding additive.finprod_def
proof (subst LCD.foldD_insert [where B = "insert i I"])
  show "LCD (insert i I) R ((+) \<circ> f)"
  proof
    show "((+) \<circ> f) x (((+) \<circ> f) y z) = ((+) \<circ> f) y (((+) \<circ> f) x z)"
      if "x \<in> insert i I" "y \<in> insert i I" "z \<in> R" for x y z
      using that additive.associative additive.commutative R by auto
    show "((+) \<circ> f) x y \<in> R"
      if "x \<in> insert i I" "y \<in> R" for x y
      using that R by force
  qed
qed (use assms in auto)

lemma finsum_singleton [simp]: 
  assumes "f i \<in> R" 
  shows "finsum {i} f = f i"
  by (metis additive.right_unit assms finite.emptyI finsum_empty finsum_insert insert_absorb insert_not_empty)


(* ex. 0.15 *)
lemma ex_15:
  fixes J :: "'b set" and \<aa> :: "'b \<Rightarrow> 'a set"
  assumes "J \<noteq> {}" and J: "\<And>j. j\<in>J \<Longrightarrow> ideal (\<aa> j) R (+) (\<cdot>) \<zero> \<one>"
  shows "\<V> ({x. \<exists>I f. x = finsum I f \<and> I \<subseteq> J \<and> finite I \<and> (\<forall>i. i\<in>I \<longrightarrow> f i \<in> \<aa> i)}) = (\<Inter>j\<in>J. \<V> (\<aa> j))"
  proof -
  have "y \<in> U"
    if j: "j \<in> J" "y \<in> \<aa> j"
      and "prime_ideal R U (+) (\<cdot>) \<zero> \<one>"
      and U: "{finsum I f |I f. I \<subseteq> J \<and> finite I \<and> (\<forall>i. i \<in> I \<longrightarrow> f i \<in> \<aa> i)} \<subseteq> U"
    for U j y
  proof -
    have "y \<in> R"
      using J j ideal_implies_subset by blast
    then have y: "y = finsum {j} (\<lambda>_. y)"
      by simp
    then have "y \<in> {finsum I f |I f. I \<subseteq> J \<and> finite I \<and> (\<forall>i. i \<in> I \<longrightarrow> f i \<in> \<aa> i)}"
      using that by blast
    then show ?thesis
      by (rule subsetD [OF U])
  qed
  moreover have PI: "prime_ideal R x (+) (\<cdot>) \<zero> \<one>" if "\<forall>j\<in>J. prime_ideal R x (+) (\<cdot>) \<zero> \<one> \<and> \<aa> j \<subseteq> x" for x 
    using that assms(1) by fastforce
  moreover have "finsum I f \<in> U"
    if "finite I"
      and "\<forall>j\<in>J. prime_ideal R U (+) (\<cdot>) \<zero> \<one> \<and> \<aa> j \<subseteq> U"
      and "I \<subseteq> J" "\<forall>i. i \<in> I \<longrightarrow> f i \<in> \<aa> i" for U I f
    using that
  proof (induction I rule: finite_induct)
    case empty
    then show ?case
      using PI assms ideal_zero by fastforce
  next
    case (insert i I)
    then have "finsum (insert i I) f = f i + finsum I f"
      by (metis assms(2) finsum_insert ideal_implies_subset insertCI subset_iff)
    also have "... \<in> U"
      using insert by (metis ideal_add insertCI prime_ideal.axioms(2) subset_eq)
    finally show ?case .
  qed
  ultimately show ?thesis
    by (auto simp: closed_subsets_def)
qed

(* ex 0.16 *)

definition is_zariski_open:: "'a set set \<Rightarrow> bool"
  where "is_zariski_open U \<equiv> generated_topology {U. \<exists>\<aa>. ideal \<aa> R (+) (\<cdot>) \<zero> \<one> \<and> U = Spec - \<V> \<aa>} U"

lemma zarisky_is_topological_space:
  shows "topological_space Spec is_zariski_open"
proof qed (auto simp: is_zariski_open_def spectrum_def  UNIV)

end (* comm_ring *)


subsection \<open>Presheaves of Rings\<close>

(* def 0.17 *)
locale presheaf_of_rings = topological_space + fixes \<FF>:: "'a set \<Rightarrow> 'b set"
  and \<rho>:: "'a set \<Rightarrow> 'a set \<Rightarrow> ('b \<Rightarrow> 'b)" and b:: "'b" 
  and add_str:: "'a set \<Rightarrow> ('b \<Rightarrow> 'b \<Rightarrow> 'b)" ("+\<^bsub>_\<^esub>") 
  and mult_str:: "'a set \<Rightarrow> ('b \<Rightarrow> 'b \<Rightarrow> 'b)" ("\<cdot>\<^bsub>_\<^esub>") 
  and zero_str:: "'a set \<Rightarrow> 'b" ("\<zero>\<^bsub>_\<^esub>") and one_str:: "'a set \<Rightarrow> 'b" ("\<one>\<^bsub>_\<^esub>")
assumes is_ring_morphism: 
  "\<And>U V. is_open U \<Longrightarrow> is_open V \<Longrightarrow> V \<subseteq> U \<Longrightarrow> ring_homomorphism (\<rho> U V) 
                                                  (\<FF> U) (+\<^bsub>U\<^esub>) (\<cdot>\<^bsub>U\<^esub>) \<zero>\<^bsub>U\<^esub> \<one>\<^bsub>U\<^esub> 
                                                  (\<FF> V) (+\<^bsub>V\<^esub>) (\<cdot>\<^bsub>V\<^esub>) \<zero>\<^bsub>V\<^esub> \<one>\<^bsub>V\<^esub>"
  and ring_of_empty [simp]: "\<FF> {} = {b}"
  and identity_map [simp]: "\<And>U. is_open U \<Longrightarrow> \<rho> U U = id"
  and assoc_comp: 
  "\<And>U V W. is_open U \<Longrightarrow> is_open V \<Longrightarrow> is_open W \<Longrightarrow> V \<subseteq> U \<Longrightarrow> W \<subseteq> V \<Longrightarrow> \<rho> U W = \<rho> V W \<circ> \<rho> U V"
begin

lemma is_ring_from_is_homomorphism:
  shows "\<And>U. is_open U \<Longrightarrow> ring (\<FF> U) (+\<^bsub>U\<^esub>) (\<cdot>\<^bsub>U\<^esub>) \<zero>\<^bsub>U\<^esub> \<one>\<^bsub>U\<^esub>"
  using is_ring_morphism ring_homomorphism.axioms(2) by fastforce

lemma is_map_from_is_homomorphism:
  assumes "is_open U" and "is_open V" and "V \<subseteq> U"
  shows "Set_Theory.map (\<rho> U V) (\<FF> U) (\<FF> V)"
  using assms by (meson is_ring_morphism ring_homomorphism.axioms(1))

lemma id_is_identity:
  assumes "is_open U"
  shows "\<rho> U U = identity (\<FF> U)"
  using assms identity_map
  by (metis PiE_restrict Set_Theory.map_def eq_id_iff is_map_from_is_homomorphism subset_refl)

lemma 
  assumes "is_open U" and "is_open V" and "is_open W" and "V \<subseteq> U" and "W \<subseteq> V"
  shows "\<And>x. x \<in> (\<FF> U) \<Longrightarrow> \<rho> U W x = (\<rho> V W \<circ> \<rho> U V) x"
  using assms assoc_comp by presburger

(* The small lemma below should be useful later in various places. *)
lemma eq_\<rho>:
  assumes "is_open U" and "is_open V" and "is_open W" and "W \<subseteq> U \<inter> V" 
    and "\<rho> U W s = \<rho> V W t" and "is_open W'" and "W' \<subseteq> W"
  shows "\<rho> U W' s = \<rho> V W' t"
  by (metis Int_subset_iff assms assoc_comp comp_apply)

end (* presheaf_of_rings *)

locale morphism_presheaves_of_rings = source: presheaf_of_rings X is_open \<FF> \<rho> b add_str mult_str zero_str one_str 
  + target: presheaf_of_rings X is_open \<FF>' \<rho>' c add_str' mult_str' zero_str' one_str'
  for X and is_open 
    and \<FF> and \<rho> and b and add_str ("+\<^bsub>_\<^esub>") and mult_str ("\<cdot>\<^bsub>_\<^esub>") 
    and zero_str ("\<zero>\<^bsub>_\<^esub>") and one_str ("\<one>\<^bsub>_\<^esub>") 
    and \<FF>' and \<rho>' and c and add_str' ("+''\<^bsub>_\<^esub>") and mult_str' ("\<cdot>''\<^bsub>_\<^esub>") 
    and zero_str' ("\<zero>''\<^bsub>_\<^esub>") and one_str' ("\<one>''\<^bsub>_\<^esub>") + 
  fixes fam_morphisms:: "'a set \<Rightarrow> ('b \<Rightarrow> 'c)"
  assumes is_ring_morphism: "\<And>U. is_open U \<Longrightarrow> ring_homomorphism (fam_morphisms U) 
                                                                (\<FF> U) (+\<^bsub>U\<^esub>) (\<cdot>\<^bsub>U\<^esub>) \<zero>\<^bsub>U\<^esub> \<one>\<^bsub>U\<^esub> 
                                                                (\<FF>' U) (+'\<^bsub>U\<^esub>) (\<cdot>'\<^bsub>U\<^esub>) \<zero>'\<^bsub>U\<^esub> \<one>'\<^bsub>U\<^esub>"
    and comm_diagrams: "\<And>U V. is_open U \<Longrightarrow> is_open V \<Longrightarrow> V \<subseteq> U \<Longrightarrow>
                      (\<rho>' U V) \<circ> fam_morphisms U \<down> \<FF> U = fam_morphisms V \<circ> (\<rho> U V) \<down> \<FF> U"
begin

lemma fam_morphisms_are_maps:
  assumes "is_open U"
  shows "Set_Theory.map (fam_morphisms U) (\<FF> U) (\<FF>' U)"
  using assms is_ring_morphism by (simp add: ring_homomorphism_def)

end (* morphism_presheaves_of_rings *)

(* Identity presheaf *)
lemma
  assumes "presheaf_of_rings X is_open \<FF> \<rho> b add_str mult_str zero_str one_str"
  shows "morphism_presheaves_of_rings X is_open \<FF> \<rho> b add_str mult_str zero_str one_str \<FF> \<rho> b add_str mult_str zero_str one_str (\<lambda>U. id)"
proof (intro morphism_presheaves_of_rings.intro morphism_presheaves_of_rings_axioms.intro)
  show "\<And>U. is_open U \<Longrightarrow> ring_homomorphism id 
                                           (\<FF> U) (add_str U) (mult_str U) (zero_str U) (one_str U) 
                                           (\<FF> U) (add_str U) (mult_str U) (zero_str U) (one_str U)"
    using assms presheaf_of_rings.identity_map presheaf_of_rings.is_ring_morphism by fastforce
  show "\<And>U V. \<lbrakk>is_open U; is_open V; V \<subseteq> U\<rbrakk>
           \<Longrightarrow> \<rho> U V \<circ> id \<down> \<FF> U = id \<circ> \<rho> U V \<down> \<FF> U"
    by (auto simp: compose_def fun_eq_iff)
qed (use assms in auto)

lemma comp_ring_morphisms:
  assumes "ring_homomorphism \<eta> A addA multA zeroA oneA B addB multB zeroB oneB" 
and "ring_homomorphism \<theta> B addB multB zeroB oneB C addC multC zeroC oneC"
shows "ring_homomorphism (compose A \<theta> \<eta>) A addA multA zeroA oneA C addC multC zeroC oneC"
  using comp_monoid_morphisms comp_group_morphisms assms 
  by (metis monoid_homomorphism_def ring_homomorphism_def)


(* Composition of presheaves *)
lemma composition_of_presheaves:
  assumes 1: "morphism_presheaves_of_rings X is_open \<FF> \<rho> b add_str mult_str zero_str one_str \<FF>' \<rho>' b' add_str' mult_str' zero_str' one_str' \<phi>"
    and 2: "morphism_presheaves_of_rings X is_open \<FF>' \<rho>' b' add_str' mult_str' zero_str' one_str' \<FF>'' \<rho>'' b'' add_str'' mult_str'' zero_str'' one_str'' \<phi>'"
  shows "morphism_presheaves_of_rings X is_open \<FF> \<rho> b add_str mult_str zero_str one_str \<FF>'' \<rho>'' b'' add_str'' mult_str'' zero_str'' one_str'' (\<lambda>U. (\<phi>' U \<circ> \<phi> U \<down> \<FF> U))"
proof (intro morphism_presheaves_of_rings.intro morphism_presheaves_of_rings_axioms.intro)
  show "ring_homomorphism (\<phi>' U \<circ> \<phi> U \<down> \<FF> U) (\<FF> U) (add_str U) (mult_str U) (zero_str U) (one_str U) (\<FF>'' U) (add_str'' U) (mult_str'' U) (zero_str'' U) (one_str'' U)"
    if "is_open U"
    for U :: "'a set"
    using that
    by (metis assms comp_ring_morphisms morphism_presheaves_of_rings.is_ring_morphism)
next
  show "\<rho>'' U V \<circ> \<phi>' U \<circ> \<phi> U \<down> \<FF> U \<down> \<FF> U = (\<phi>' V \<circ> \<phi> V \<down> \<FF> V) \<circ> \<rho> U V \<down> \<FF> U"
    if "is_open U" "is_open V" "V \<subseteq> U" for U V
    using that 
    using morphism_presheaves_of_rings.comm_diagrams [OF 1]
    using morphism_presheaves_of_rings.comm_diagrams [OF 2]
    using presheaf_of_rings.is_map_from_is_homomorphism [OF morphism_presheaves_of_rings.axioms(1) [OF 1]]
    apply (auto simp add: fun_eq_iff compose_def)
    apply (metis map.map_closed morphism_presheaves_of_rings.fam_morphisms_are_maps [OF 1])
    by (meson map.map_closed)
qed (use assms in \<open>auto simp: morphism_presheaves_of_rings_def\<close>)

locale iso_presheaves_of_rings =
f: morphism_presheaves_of_rings X is_open \<FF> \<rho> b add_str mult_str zero_str one_str \<FF>' \<rho>' b' add_str' mult_str' zero_str' one_str' \<phi>  
for X is_open \<FF> \<rho> b add_str mult_str zero_str one_str \<FF>' \<rho>' b' add_str' mult_str' zero_str' one_str' \<phi>
+ assumes is_inv: "\<exists>\<psi>. morphism_presheaves_of_rings X is_open \<FF>' \<rho>' b' add_str' mult_str' zero_str' one_str' \<FF> \<rho> b add_str mult_str zero_str one_str \<psi> 
\<and> (\<forall>U. is_open U \<longrightarrow> \<phi> U \<circ> \<psi> U = id \<and> \<psi> U \<circ> \<phi> U = id)"
begin

lemma 
  fixes \<psi>:: "'a set \<Rightarrow> 'c \<Rightarrow> 'b"
  assumes "\<phi> U \<circ> \<psi> U = id" and "\<psi> U \<circ> \<phi> U = id"
  shows "\<phi> U \<circ> \<psi> U \<down> (\<FF>' U) = identity (\<FF>' U)" and "\<psi> U \<circ> \<phi> U \<down> (\<FF> U) = identity (\<FF> U)"
  apply (metis assms(1) comp_apply compose_def eq_id_iff)
  by (metis assms(2) comp_apply compose_def eq_id_iff) 
 
end (* iso_presheaves_of_rings*)


subsection \<open>Sheaves of Rings\<close>

(* def 0.19 *)
locale sheaf_of_rings = presheaf_of_rings X is_open \<FF> \<rho> b add_str mult_str zero_str one_str 
  for X and is_open and \<FF> and \<rho> and b and add_str and mult_str and zero_str ("\<zero>\<^bsub>_\<^esub>") and one_str + 
  assumes locality: "\<And>U I V s. open_cover_of_open_subset X is_open U I V \<Longrightarrow> (\<And>i. i\<in>I \<Longrightarrow> V i \<subseteq> U) \<Longrightarrow> 
s \<in> \<FF> U \<Longrightarrow> (\<And>i. i\<in>I \<Longrightarrow> \<rho> U (V i) s = \<zero>\<^bsub>(V i)\<^esub>) \<Longrightarrow> s = \<zero>\<^bsub>U\<^esub>" and
glueing: "\<And>U I V s. open_cover_of_open_subset X is_open U I V \<Longrightarrow> (\<forall>i. i\<in>I \<longrightarrow> V i \<subseteq> U \<and> s i \<in> \<FF> (V i)) \<Longrightarrow> 
(\<And>i j. i\<in>I \<Longrightarrow> j\<in>I \<Longrightarrow> \<rho> (V i) (V i \<inter> V j) (s i) = \<rho> (V j) (V i \<inter> V j) (s j)) \<Longrightarrow> 
(\<exists>t. t \<in> \<FF> U \<and> (\<forall>i. i\<in>I \<longrightarrow> \<rho> U (V i) t = s i))"

(* def. 0.20 *)
locale morphism_sheaves_of_rings = morphism_presheaves_of_rings

locale iso_sheaves_of_rings = iso_presheaves_of_rings 

(* ex. 0.21 *)
locale cxt_ind_sheaf = sheaf_of_rings X is_open \<FF> \<rho> b add_str mult_str zero_str one_str + 
ind_topology X is_open U
for X and is_open and \<FF> and \<rho> and b and add_str ("+\<^bsub>_\<^esub>") and mult_str ("\<cdot>\<^bsub>_\<^esub>") 
and zero_str ("\<zero>\<^bsub>_\<^esub>") and one_str ("\<one>\<^bsub>_\<^esub>") and U +
  assumes is_open_subset: "is_open U"
begin

definition ind_sheaf:: "'a set \<Rightarrow> 'b set"
  where "ind_sheaf V \<equiv> \<FF> (U \<inter> V)"

definition ind_ring_morphisms:: "'a set \<Rightarrow> 'a set \<Rightarrow> ('b \<Rightarrow> 'b)"
  where "ind_ring_morphisms V W \<equiv> \<rho> (U \<inter> V) (U \<inter> W)"

definition ind_add_str:: "'a set \<Rightarrow> ('b \<Rightarrow> 'b \<Rightarrow> 'b)"
  where "ind_add_str V \<equiv> \<lambda>x y. +\<^bsub>(U \<inter> V)\<^esub> x y"

definition ind_mult_str:: "'a set \<Rightarrow> ('b \<Rightarrow> 'b \<Rightarrow> 'b)"
  where "ind_mult_str V \<equiv> \<lambda>x y. \<cdot>\<^bsub>(U \<inter> V)\<^esub> x y"

definition ind_zero_str:: "'a set \<Rightarrow> 'b"
  where "ind_zero_str V \<equiv> \<zero>\<^bsub>(U\<inter>V)\<^esub>"

definition ind_one_str:: "'a set \<Rightarrow> 'b"
  where "ind_one_str V \<equiv> \<one>\<^bsub>(U\<inter>V)\<^esub>"

lemma ind_is_open_imp_ring: 
  "\<And>U. ind_is_open U
   \<Longrightarrow> ring (ind_sheaf U) (ind_add_str U) (ind_mult_str U) (ind_zero_str U) (ind_one_str U)"
    using ind_add_str_def ind_is_open_def ind_mult_str_def ind_one_str_def ind_sheaf_def ind_zero_str_def is_open_subset is_ring_from_is_homomorphism is_subset open_inter by force

lemma ind_sheaf_is_presheaf:
  shows "presheaf_of_rings U (ind_is_open) ind_sheaf ind_ring_morphisms b
ind_add_str ind_mult_str ind_zero_str ind_one_str"
proof-
  have "topological_space U ind_is_open" by (simp add: ind_space_is_top_space)
  moreover have "\<And>U V. ind_is_open U \<Longrightarrow> ind_is_open V \<Longrightarrow> V \<subseteq> U \<Longrightarrow> ring_homomorphism (ind_ring_morphisms U V) 
                     (ind_sheaf U) (ind_add_str U) (ind_mult_str U) (ind_zero_str U) (ind_one_str U) 
                     (ind_sheaf V) (ind_add_str V) (ind_mult_str V) (ind_zero_str V) (ind_one_str V)"
  proof (intro ring_homomorphism.intro ind_is_open_imp_ring)
    fix W V
    assume \<section>: "ind_is_open W" "ind_is_open V" "V \<subseteq> W"
    then show "Set_Theory.map (ind_ring_morphisms W V) (ind_sheaf W) (ind_sheaf V)"
      by (metis ind_is_open_def ind_ring_morphisms_def ind_sheaf_def inf.left_idem is_open_subset is_ring_morphism is_subset open_inter ring_homomorphism_def)
    obtain o: "is_open (U \<inter> V)" "is_open (U \<inter> W)" "U \<inter> V \<subseteq> U \<inter> W"
      by (metis (no_types) "\<section>" ind_is_open_def inf.absorb_iff2 is_open_subset is_subset open_inter)
    then show "group_homomorphism (ind_ring_morphisms W V) (ind_sheaf W) (ind_add_str W) (ind_zero_str W) (ind_sheaf V) (ind_add_str V) (ind_zero_str V)"
      by (metis cxt_ind_sheaf.ind_add_str_def cxt_ind_sheaf_axioms ind_ring_morphisms_def ind_sheaf_def ind_zero_str_def is_ring_morphism ring_homomorphism.axioms(4))
    show "monoid_homomorphism (ind_ring_morphisms W V) (ind_sheaf W) (ind_mult_str W) (ind_one_str W) (ind_sheaf V) (ind_mult_str V) (ind_one_str V)"
      using o by (metis ind_mult_str_def ind_one_str_def ind_ring_morphisms_def ind_sheaf_def is_ring_morphism ring_homomorphism_def) 
  qed
  moreover have "ind_sheaf {} = {b}"
    by (simp add: ind_sheaf_def)     
  moreover have "\<And>U. ind_is_open U \<Longrightarrow> ind_ring_morphisms U U = id"
    using identity_map ind_is_open_def ind_ring_morphisms_def is_open_subset is_subset open_inter by auto
  moreover have "\<And>U V W. ind_is_open U \<Longrightarrow> ind_is_open V \<Longrightarrow> ind_is_open W \<Longrightarrow> V \<subseteq> U \<Longrightarrow> W \<subseteq> V 
             \<Longrightarrow> ind_ring_morphisms U W = ind_ring_morphisms V W \<circ> ind_ring_morphisms U V"
    using assoc_comp ind_is_open_def ind_ring_morphisms_def is_open_subset is_subset open_inter by force
  ultimately show ?thesis 
    unfolding presheaf_of_rings_def presheaf_of_rings_axioms_def by blast
qed

lemma ind_sheaf_is_sheaf:
  shows "sheaf_of_rings U ind_is_open ind_sheaf ind_ring_morphisms b ind_add_str ind_mult_str ind_zero_str ind_one_str"
proof (intro sheaf_of_rings.intro sheaf_of_rings_axioms.intro)
  show "presheaf_of_rings U ind_is_open ind_sheaf ind_ring_morphisms b ind_add_str ind_mult_str ind_zero_str ind_one_str"
    using ind_sheaf_is_presheaf by blast
next
  fix V I W s
  assume oc: "open_cover_of_open_subset U ind_is_open V I W"
    and WV: "\<And>i. i \<in> I \<Longrightarrow> W i \<subseteq> V"
    and s: "s \<in> ind_sheaf V"
    and eq: "\<And>i. i \<in> I \<Longrightarrow> ind_ring_morphisms V (W i) s = ind_zero_str (W i)"
  have "ind_is_open V"
    using oc open_cover_of_open_subset.is_open_subset by blast
  then have "s \<in> \<FF> V"
    by (metis cxt_ind_sheaf.ind_sheaf_def cxt_ind_sheaf_axioms ind_is_open_def inf.absorb2 s)
  then have "s = \<zero>\<^bsub>V\<^esub>"
    by (metis Int_absorb1 Int_subset_iff WV cxt_ind_sheaf.ind_zero_str_def cxt_ind_sheaf_axioms eq ind_is_open_def ind_ring_morphisms_def is_open_subset locality oc open_cover_from_ind_open_cover open_cover_of_open_subset.is_open_subset) 
  then show "s = ind_zero_str V"
    by (metis Int_absorb1 ind_is_open_def ind_zero_str_def oc open_cover_of_open_subset.is_open_subset)
next
  fix V I W s
  assume oc: "open_cover_of_open_subset U ind_is_open V I W"
    and WV: "\<forall>i. i \<in> I \<longrightarrow> W i \<subseteq> V \<and> s i \<in> ind_sheaf (W i)"
    and eq: "\<And>i j. \<lbrakk>i \<in> I; j \<in> I\<rbrakk> \<Longrightarrow> ind_ring_morphisms (W i) (W i \<inter> W j) (s i) = ind_ring_morphisms (W j) (W i \<inter> W j) (s j)"
  have "is_open V" 
    using is_open_from_ind_is_open is_open_subset oc open_cover_of_open_subset.is_open_subset by blast
  moreover have "open_cover_of_open_subset X is_open V I W" 
    using open_cover_from_ind_open_cover oc ind_topology.intro ind_topology_axioms_def is_open_subset is_subset topological_space_axioms by blast
  moreover have "\<rho> (W i) (W i \<inter> W j) (s i) = \<rho> (W j) (W i \<inter> W j) (s j)"
    if "i\<in>I" "j\<in>I" for i j
  proof -
    have "U \<inter> W i = W i" and "U \<inter> W j = W j"
      by (metis Int_absorb1 WV ind_is_open_def oc open_cover_of_open_subset.is_open_subset 
            subset_trans that)+
    then show ?thesis 
      using eq[unfolded ind_ring_morphisms_def,OF that] by (metis inf_sup_aci(2)) 
  qed
  moreover have "\<forall>i. i\<in>I \<longrightarrow> W i \<subseteq> V \<and> s i \<in> \<FF> (W i)"
    by (metis WV ind_is_open_def ind_sheaf_def inf.orderE inf_idem inf_aci(3) oc open_cover_of_open_subset.is_open_subset)
  ultimately 
  obtain t where "t \<in> (\<FF> V) \<and> (\<forall>i. i\<in>I \<longrightarrow> \<rho> V (W i) t = s i)" 
    using glueing by blast
  then have "t \<in> ind_sheaf V" 
    unfolding ind_sheaf_def using oc
    by (metis Int_absorb1 cover_of_subset_def open_cover_of_open_subset_def open_cover_of_subset_def)
  moreover have "\<forall>i. i\<in>I \<longrightarrow> ind_ring_morphisms V (W i) t = s i" 
    unfolding ind_ring_morphisms_def
    by (metis oc Int_absorb1 \<open>t \<in> \<FF> V \<and> (\<forall>i. i \<in> I \<longrightarrow> \<rho> V (W i) t = s i)\<close> cover_of_subset_def open_cover_of_open_subset_def open_cover_of_subset_def)
  ultimately show "\<exists>t. t \<in> (ind_sheaf V) \<and> (\<forall>i. i\<in>I \<longrightarrow> ind_ring_morphisms V (W i) t = s i)" by blast
qed

end (* cxt_ind_sheaf*)

(* context for construction 0.22 *)
locale cxt_direct_im_sheaf = continuous_map X is_open X' is_open' f + 
sheaf_of_rings X is_open \<FF> \<rho> b add_str mult_str zero_str one_str
for X and is_open and X' and is_open' and f and \<FF> and \<rho> and b and add_str ("+\<^bsub>_\<^esub>") and 
mult_str ("\<cdot>\<^bsub>_\<^esub>") and zero_str ("\<zero>\<^bsub>_\<^esub>") and one_str ("\<one>\<^bsub>_\<^esub>")
begin

(* def 0.24 *)
definition direct_im_sheaf:: "'b set => 'c set"
  where "direct_im_sheaf V \<equiv> \<FF> (f\<^sup>\<inverse> V)"

definition direct_im_sheaf_ring_morphisms:: "'b set \<Rightarrow> 'b set \<Rightarrow> ('c \<Rightarrow> 'c)"
  where "direct_im_sheaf_ring_morphisms U V \<equiv> \<rho> (f\<^sup>\<inverse> U) (f\<^sup>\<inverse> V)"

lemma direct_im_sheaf_is_presheaf:
"presheaf_of_rings X' (is_open') direct_im_sheaf direct_im_sheaf_ring_morphisms b
(\<lambda>V x y. +\<^bsub>(f\<^sup>\<inverse> V)\<^esub> x y) (\<lambda>V x y. \<cdot>\<^bsub>(f\<^sup>\<inverse> V)\<^esub> x y) (\<lambda>V. \<zero>\<^bsub>(f\<^sup>\<inverse> V)\<^esub>) (\<lambda>V. \<one>\<^bsub>(f\<^sup>\<inverse> V)\<^esub>)"
proof-
  have "topological_space X' is_open'"
    by (simp add: target.topological_space_axioms)
  moreover have "\<And>U V. is_open' U \<Longrightarrow> is_open' V \<Longrightarrow> V \<subseteq> U \<Longrightarrow> 
ring_homomorphism (direct_im_sheaf_ring_morphisms U V) 
(direct_im_sheaf U) (+\<^bsub>(f\<^sup>\<inverse> U)\<^esub>) (\<cdot>\<^bsub>(f\<^sup>\<inverse> U)\<^esub>) (\<zero>\<^bsub>(f\<^sup>\<inverse> U)\<^esub>) (\<one>\<^bsub>(f\<^sup>\<inverse> U)\<^esub>) 
(direct_im_sheaf V) (+\<^bsub>(f\<^sup>\<inverse> V)\<^esub>) (\<cdot>\<^bsub>(f\<^sup>\<inverse> V)\<^esub>) (\<zero>\<^bsub>(f\<^sup>\<inverse> V)\<^esub>) (\<one>\<^bsub>(f\<^sup>\<inverse> V)\<^esub>)"
    by (metis direct_im_sheaf_def direct_im_sheaf_ring_morphisms_def is_continuous is_ring_morphism vimage_def vimage_mono)
  moreover have "direct_im_sheaf {} = {b}" using direct_im_sheaf_def by simp
  moreover have "\<And>U. is_open' U \<Longrightarrow> direct_im_sheaf_ring_morphisms U U = id" 
    using direct_im_sheaf_ring_morphisms_def by (simp add: is_continuous vimage_def)
  moreover have "\<And>U V W. is_open' U \<Longrightarrow> is_open' V \<Longrightarrow> is_open' W \<Longrightarrow> V \<subseteq> U \<Longrightarrow> W \<subseteq> V \<Longrightarrow> 
direct_im_sheaf_ring_morphisms U W = direct_im_sheaf_ring_morphisms V W \<circ> direct_im_sheaf_ring_morphisms U V"
    by (metis (full_types) assoc_comp continuous_map.is_continuous continuous_map_axioms direct_im_sheaf_ring_morphisms_def vimage_def vimage_mono)
  ultimately show ?thesis unfolding presheaf_of_rings_def presheaf_of_rings_axioms_def by blast
qed

(* ex 0.23 *)
lemma direct_im_sheaf_is_sheaf:
  shows "sheaf_of_rings X' (is_open') direct_im_sheaf direct_im_sheaf_ring_morphisms b
(\<lambda>V x y. +\<^bsub>(f\<^sup>\<inverse> V)\<^esub> x y) (\<lambda>V x y. \<cdot>\<^bsub>(f\<^sup>\<inverse> V)\<^esub> x y) (\<lambda>V. \<zero>\<^bsub>(f\<^sup>\<inverse> V)\<^esub>) (\<lambda>V. \<one>\<^bsub>(f\<^sup>\<inverse> V)\<^esub>)"
proof (intro sheaf_of_rings.intro sheaf_of_rings_axioms.intro)
  show "presheaf_of_rings X' is_open' direct_im_sheaf direct_im_sheaf_ring_morphisms b (\<lambda>V. +\<^bsub>f \<^sup>\<inverse> V\<^esub>) (\<lambda>V. \<cdot>\<^bsub>f \<^sup>\<inverse> V\<^esub>) (\<lambda>V. \<zero>\<^bsub>f \<^sup>\<inverse> V\<^esub>) (\<lambda>V. \<one>\<^bsub>f \<^sup>\<inverse> V\<^esub>)"
    using direct_im_sheaf_is_presheaf by force
next
  fix U I V s
  assume oc: "open_cover_of_open_subset X' is_open' U I V"
    and VU: "\<And>i. i \<in> I \<Longrightarrow> V i \<subseteq> U"
    and s: "s \<in> direct_im_sheaf U"
    and eq0: "\<And>i. (i::real) \<in> I \<Longrightarrow> direct_im_sheaf_ring_morphisms U (V i) s = \<zero>\<^bsub>f \<^sup>\<inverse> V i\<^esub>"
  have "open_cover_of_open_subset X is_open (f\<^sup>\<inverse> U) I (\<lambda>i. f\<^sup>\<inverse> (V i))"
    by (simp add: oc open_cover_of_open_subset_from_target_to_source) 
  then show "s = \<zero>\<^bsub>f \<^sup>\<inverse> U\<^esub>"
    by (metis (mono_tags, lifting) VU direct_im_sheaf_def direct_im_sheaf_ring_morphisms_def eq0 locality s vimage_mono) 
next
  fix U I V s
  assume oc: "open_cover_of_open_subset X' is_open' U I V"
    and VU: "\<forall>i. i \<in> I \<longrightarrow> V i \<subseteq> U \<and> s i \<in> direct_im_sheaf (V i)"
    and eq: "\<And>i j. \<lbrakk>i \<in> I; j \<in> I\<rbrakk> \<Longrightarrow> direct_im_sheaf_ring_morphisms (V i) (V i \<inter> V j) (s i) = direct_im_sheaf_ring_morphisms (V j) (V i \<inter> V j) (s j)"
  have "\<exists>t. t \<in> \<FF> (f  \<^sup>\<inverse> U) \<and> (\<forall>i. i \<in> I \<longrightarrow> \<rho> (f  \<^sup>\<inverse> U) (f  \<^sup>\<inverse> V i) t = s i)"
  proof (rule glueing)
    show "open_cover_of_open_subset X is_open (f \<^sup>\<inverse> U) I (\<lambda>i. f \<^sup>\<inverse> V i)"
      using oc open_cover_of_open_subset_from_target_to_source by presburger
    show "\<forall>i. i \<in> I \<longrightarrow> f \<^sup>\<inverse> V i \<subseteq> f \<^sup>\<inverse> U \<and> s i \<in> \<FF> (f \<^sup>\<inverse> V i)"
      using VU direct_im_sheaf_def by blast
    show "\<rho> (f \<^sup>\<inverse> V i) (f \<^sup>\<inverse> V i \<inter> f \<^sup>\<inverse> V j) (s i) = \<rho> (f \<^sup>\<inverse> V j) (f \<^sup>\<inverse> V i \<inter> f \<^sup>\<inverse> V j) (s j)"
      if "i \<in> I" "j \<in> I" for i j
      using direct_im_sheaf_ring_morphisms_def eq that by auto
  qed
  then obtain t where "t \<in> \<FF> (f\<^sup>\<inverse> U) \<and> (\<forall>i. i\<in>I \<longrightarrow> \<rho> (f\<^sup>\<inverse> U) (f\<^sup>\<inverse> (V i)) t = s i)" ..
  then show "\<exists>t. t \<in> direct_im_sheaf U \<and> (\<forall>i. i \<in> I \<longrightarrow> direct_im_sheaf_ring_morphisms U (V i) t = s i)"
    using direct_im_sheaf_def direct_im_sheaf_ring_morphisms_def by auto
qed

end (* cxt_direct_im_sheaf *)


subsection \<open>Quotient Ring\<close>

locale cxt_quotient_ring = comm_ring R "(+)" "(\<cdot>)" "\<zero>" "\<one>" + submonoid S R "(\<cdot>)" "\<one>" 
  for S and R and addition (infixl "+" 65) and multiplication (infixl "\<cdot>" 70) and zero ("\<zero>") and 
unit ("\<one>")
begin

definition rel:: "('a \<times> 'a) \<Rightarrow> ('a \<times> 'a) \<Rightarrow> bool" (infix "\<sim>" 80)
  where "x \<sim> y \<equiv> \<exists>s1. s1 \<in> S \<and> s1 \<cdot> (snd y \<cdot> fst x - snd x \<cdot> fst y) = \<zero>"

lemma rel_is_equivalence:
  shows "equivalence (R \<times> S) {(x,y) \<in> (R\<times>S)\<times>(R\<times>S). x \<sim> y}"
proof-
  have 0: "\<And>r s r1 s2 s1.
       \<lbrakk>r \<in> R; s \<in> S; r1 \<in> R; s2 \<in> S; s1 \<in> S; s1 \<cdot> (s2 \<cdot> r - s \<cdot> r1) = \<zero>\<rbrakk> \<Longrightarrow> s1 \<cdot> (s \<cdot> r1 - s2 \<cdot> r) = \<zero>"
    by (smt additive.composition_closed additive.inverse_composition_commute additive.inverse_unit 
        additive.invertible additive.monoid_axioms local.right_minus monoid.invertible_inverse_closed 
        monoid.invertible_inverse_inverse multiplicative.composition_closed sub)  
  have "{(x,y)\<in>(R\<times>S)\<times>(R\<times>S). x \<sim> y} \<subseteq> (R \<times> S) \<times> (R \<times> S)" by auto
  moreover have 1: "\<And>x. x \<in> R \<times> S \<Longrightarrow> x \<sim> x"
    by (auto simp: rel_def)
  moreover have 2: "\<And>x y. x \<in> R \<times> S \<and> y \<in> R \<times> S \<and> x \<sim> y \<Longrightarrow> y \<sim> x"
    by (metis 0 SigmaE prod.sel rel_def)
  moreover have 3: "x \<sim> z"
    if "x \<in> R \<times> S" "y \<in> R \<times> S" "x \<sim> y" "z \<in> R \<times> S" "y \<sim> z" for x y z
  proof -
    obtain s1 where "s1 \<in> S" and xy0: "s1 \<cdot> (snd y \<cdot> fst x - snd x \<cdot> fst y) = \<zero>"
      using \<open>x \<sim> y\<close> unfolding rel_def by auto
    obtain s2 where "s2 \<in> S" and yz0:"s2 \<cdot> (snd z \<cdot> fst y - snd y \<cdot> fst z) = \<zero>"
      using \<open>y \<sim> z\<close> unfolding rel_def by auto
    have [simp]:
      "s1 \<in> R" "s2 \<in> R" "fst x \<in> R" "snd x\<in>R" "fst y\<in>R" "snd y\<in>R" "fst z\<in>R" "snd z\<in>R"
      using that \<open>s1\<in>S\<close> \<open>s2\<in>S\<close> by auto

    define s3 where "s3=s1 \<cdot> s2 \<cdot> snd y"
    have "s3\<in>S" and [simp]:"s3\<in>R"
    proof -
      show "s3\<in>S" unfolding s3_def using \<open>s1 \<in> S\<close> \<open>s2 \<in> S\<close> that(2) by auto
      then show "s3\<in>R" by simp
    qed
    have "s3 \<cdot> snd z \<cdot> fst x - s1 \<cdot> s2 \<cdot> snd x \<cdot> fst y \<cdot> snd z = \<zero>"
    proof -
      have "snd z \<cdot> s2 \<cdot> s1 \<cdot> (snd y \<cdot> fst x - snd x \<cdot> fst y) = \<zero>"
        using xy0 by (simp add: multiplicative.associative)
      then show ?thesis
        unfolding s3_def 
        using commutative_mult multiplicative.associative distributive right_minus
        by auto
    qed
    moreover have "s1 \<cdot> s2 \<cdot> snd x \<cdot> fst y \<cdot> snd z - s3 \<cdot> snd x \<cdot> fst z = \<zero>"
    proof -
      have "snd x \<cdot> s1 \<cdot> s2 \<cdot> (snd z \<cdot> fst y - snd y \<cdot> fst z) = \<zero>"
        using yz0 by (simp add: multiplicative.associative)
      then show ?thesis 
        unfolding s3_def 
        using commutative_mult multiplicative.associative distributive right_minus
        by auto
    qed
    ultimately have "s3 \<cdot> snd z \<cdot> fst x - s3 \<cdot> snd x \<cdot> fst z = \<zero>" 
      by (simp add: additive.commutative additive.monoid_axioms monoid.inverse_equality s3_def)
    then have "s3 \<cdot> (snd z \<cdot> fst x - snd x \<cdot> fst z) = \<zero>"
      using distributive right_minus multiplicative.associative by auto
    with \<open>s3\<in>S\<close> show ?thesis
      unfolding rel_def by auto
  qed
  show ?thesis 
    by (simp add: equivalence_def) (blast intro: 1 2 3)
qed

notation equivalence.Partition (infixl "'/" 75)

definition frac:: "'a \<Rightarrow> 'a \<Rightarrow> ('a \<times> 'a) set" (infixl "'/" 75)
  where "r / s \<equiv> equivalence.Class (R \<times> S) {(x,y)\<in>(R\<times>S)\<times>(R\<times>S). x \<sim> y} (r, s)"

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
  where "carrier_quotient_ring \<equiv> equivalence.Partition (R \<times> S) {(x,y)\<in>(R\<times>S)\<times>(R\<times>S). x \<sim> y}"

(* ex. 0.26 *)
lemma
  shows "ring carrier_quotient_ring add_rel mult_rel (\<zero> / \<one>) (\<one> / \<one>)"
  sorry

end (* cxt_quotient_ring *)

notation cxt_quotient_ring.carrier_quotient_ring ("_ \<^sup>\<inverse> _\<^bsub>_ _ _\<^esub>")


subsection \<open>Local Rings at Prime Ideals\<close>

context prime_ideal 
begin

lemma submonoid_prime_ideal:
  shows "submonoid (R \<setminus> I) R (\<cdot>) \<one>"
proof
  show "a \<cdot> b \<in> R\<setminus>I" if "a \<in> R\<setminus>I" "b \<in> R\<setminus>I" for a b
    using that by (metis Diff_iff absorbent multiplicative.composition_closed)
  show "\<one> \<in> R\<setminus>I"
    using ideal.ideal(2) ideal_axioms prime_ideal.carrier_neq prime_ideal_axioms by fastforce
qed auto

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
context comm_ring
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

lemma
  fixes s:: "'a set \<Rightarrow> ('a \<times> 'a) set"
  shows "is_regular s {}"
  by (simp add: is_regular_def)

definition sheaf_on_spec:: "('a set) set \<Rightarrow> ('a set \<Rightarrow> ('a \<times> 'a) set) set"
  where "sheaf_on_spec U \<equiv> {s. (Set_Theory.map s U (\<Union>\<pp>\<in>U. (R\<^bsub>\<pp> (+) (\<cdot>) \<zero>\<^esub>))) 
                  \<and> is_regular s U}"

definition add_sheaf_on_spec:: "('a set) set \<Rightarrow> ('a set \<Rightarrow> ('a \<times> 'a) set) \<Rightarrow> ('a set \<Rightarrow> ('a \<times> 'a) set) \<Rightarrow> ('a set \<Rightarrow> ('a \<times> 'a) set)"
  where "add_sheaf_on_spec U s s' \<equiv> \<lambda>\<pp>\<in>U. cxt_quotient_ring.add_rel (R \<setminus> \<pp>) R (+) (\<cdot>) \<zero> (s \<pp>) (s' \<pp>)"

lemma
  assumes "is_zariski_open U" and "is_regular s U" and "is_regular s' U" 
  shows "is_regular (add_sheaf_on_spec U s s') U"
  sorry

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
  shows "sheaf_of_rings Spec is_zariski_open sheaf_on_spec sheaf_on_spec_ring_morphisms (\<lambda>\<pp>. {(\<zero>,\<zero>)})
(\<lambda>U. add_sheaf_on_spec U) (\<lambda>U. mult_sheaf_on_spec U) (\<lambda>U. zero_sheaf_on_spec U) (\<lambda>U. one_sheaf_on_spec U)"
  sorry

end (* comm_ring *)


section \<open>Schemes\<close>

subsection \<open>Ringed Spaces\<close>

(* definition 0.32 *)
locale ringed_space = topological_space X is_open + sheaf_of_rings X is_open \<O> \<rho> b add_str mult_str zero_str one_str
  for X and is_open and \<O> and \<rho> and b and add_str and mult_str and zero_str and one_str

context comm_ring
begin

lemma 
  shows "ringed_space Spec is_zariski_open sheaf_on_spec sheaf_on_spec_ring_morphisms (\<lambda>\<pp>. {(a,a)})
(\<lambda>U. add_sheaf_on_spec U) (\<lambda>U. mult_sheaf_on_spec U) (\<lambda>U. zero_sheaf_on_spec U) (\<lambda>U. one_sheaf_on_spec U)"
  sorry

end (* comm_ring *)

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
locale cxt_direct_lim = sheaf_of_rings X is_open \<FF> \<rho> b add_str mult_str zero_str one_str 
  for X and is_open and \<FF> and \<rho> and b and add_str ("+\<^bsub>_\<^esub>") and mult_str ("\<cdot>\<^bsub>_\<^esub>") and 
zero_str ("\<zero>\<^bsub>_\<^esub>") and one_str ("\<one>\<^bsub>_\<^esub>") + 
  fixes I:: "'a set set"
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

subsubsection \<open>Stalks of a Presheaf\<close>

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

subsubsection \<open>Maximal Ideals\<close>

(* definition 0.38 *)
locale max_ideal = comm_ring R "(+)" "(\<cdot>)" "\<zero>" "\<one>" + ideal I  R "(+)" "(\<cdot>)" "\<zero>" "\<one>" 
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

subsubsection \<open>Local Rings\<close>

(* definition 0.39 *)
locale local_ring = comm_ring +
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

subsubsection \<open>Locally Ringed Spaces\<close>

(* def. 0.42 *)
locale locally_ringed_space = ringed_space +
  assumes is_local_ring: "\<And>x U. x \<in> U \<Longrightarrow> is_open U \<Longrightarrow>
local_ring (stalk_at x) (add_stalk_at x) (mult_stalk_at x) (zero_stalk_at x U) (one_stalk_at x U)"
context entire_ring
begin

(* ex. 0.43 *)
lemma
  shows "locally_ringed_space Spec is_zariski_open sheaf_on_spec sheaf_on_spec_ring_morphisms (\<lambda>\<pp>. {(\<zero>,\<zero>)})
(\<lambda>U. add_sheaf_on_spec U) (\<lambda>U. mult_sheaf_on_spec U) (\<lambda>U. zero_sheaf_on_spec U) (\<lambda>U. one_sheaf_on_spec U)"
  sorry

end (* comm_ring *)

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
locale affine_scheme = locally_ringed_space + comm_ring +
  assumes is_iso_to_spec: "\<exists>f \<phi>\<^sub>f. iso_locally_ringed_spaces X is_open \<O> \<rho> b add_str mult_str zero_str one_str
Spec is_zariski_open sheaf_on_spec sheaf_on_spec_ring_morphisms (\<lambda>\<pp>. {(\<zero>,\<zero>)}) (\<lambda>U. add_sheaf_on_spec U)
(\<lambda>U. mult_sheaf_on_spec U) (\<lambda>U. zero_sheaf_on_spec U) (\<lambda>U. one_sheaf_on_spec U) f \<phi>\<^sub>f"


subsection \<open>Schemes\<close>

(* def. 0.47 *)
locale scheme = locally_ringed_space + comm_ring +
  assumes are_affine_schemes: "\<forall>x. x \<in> X \<longrightarrow> (\<exists>U. is_open U \<and> x \<in> U \<and> 
affine_scheme U (ind_topology.ind_is_open X is_open U) (cxt_ind_sheaf.ind_sheaf \<O> U) 
(cxt_ind_sheaf.ind_ring_morphisms \<rho> U) b (cxt_ind_sheaf.ind_add_str add_str U)
(cxt_ind_sheaf.ind_mult_str mult_str U) (cxt_ind_sheaf.ind_zero_str zero_str U)
(cxt_ind_sheaf.ind_one_str one_str U) R (+) (\<cdot>) \<zero> \<one>
)"

context affine_scheme
begin

lemma affine_scheme_is_scheme:
  shows "scheme X is_open \<O> \<rho> b add_str mult_str zero_str one_str R (+) (\<cdot>) \<zero> \<one>"
  sorry

end (* affine_scheme*)

lemma empty_scheme_is_affine_scheme:
  shows "affine_scheme {} (\<lambda>U. True) (\<lambda>U. {0::nat}) (\<lambda>U V. id) 0 (\<lambda>U x y. 0) (\<lambda>U x y. 0) (\<lambda>U. 0) (\<lambda>U. 0)
{0} (\<lambda>x y. 0) (\<lambda>x y. 0) 0 0"
  sorry


end