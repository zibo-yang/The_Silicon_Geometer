theory Group_Further_Theory
  imports Main 
          (*"HOL-Algebra.FiniteProduct"*)
          "Jacobson_Basic_Algebra.Group_Theory"

begin

section \<open>Monoids\<close>

subsection \<open>Finite Products\<close>

context monoid
begin

(* The following 4 definitions are taken from HOL-Algebra.FiniteProduct. I could simply import
"HOL-Algebra.FiniteProduct" but then it creates ambiguities in our other theories that made me 
mad. If you know a simple way to remove these ambiguities, then delete the following 3 definitions
and simply import HOL-Algebra.FiniteProduct. Note however that finprod needs to be redefined, since 
in HOL-Algebra it uses a monoid-record which simply does not exist in the Ballarin's new formalism. 
*)
inductive_set
  foldSetD :: "['a set, 'b \<Rightarrow> 'a \<Rightarrow> 'a, 'a] \<Rightarrow> ('b set * 'a) set"
  for D :: "'a set" and f :: "'b \<Rightarrow> 'a \<Rightarrow> 'a" and e :: 'a
  where
    emptyI [intro]: "e \<in> D \<Longrightarrow> ({}, e) \<in> foldSetD D f e"
  | insertI [intro]: "\<lbrakk>x \<notin> A; f x y \<in> D; (A, y) \<in> foldSetD D f e\<rbrakk> \<Longrightarrow>
                      (insert x A, f x y) \<in> foldSetD D f e"

inductive_cases empty_foldSetDE [elim!]: "({}, x) \<in> foldSetD D f e"

definition
  foldD :: "['a set, 'b \<Rightarrow> 'a \<Rightarrow> 'a, 'a, 'b set] \<Rightarrow> 'a"
  where "foldD D f e A = (THE x. (A, x) \<in> foldSetD D f e)"

definition finprod:: "'b set => ('b => 'a) \<Rightarrow> 'a"
  where "finprod I f \<equiv> if finite I then foldD M (composition \<circ> f) \<one> I else \<one>"

end (* monoid *)

section \<open>Subgroup Generated by a Subset\<close>

context group 
begin

inductive_set generate :: "'a set \<Rightarrow> 'a set"
  for H where
    unit:  "\<one> \<in> generate H"
  | incl: "a \<in> H \<Longrightarrow> a \<in> generate H"
  | inv:  "a \<in> H \<Longrightarrow> inverse a \<in> generate H"
  | mult:  "a \<in> generate H \<Longrightarrow> b \<in> generate H \<Longrightarrow> a \<cdot> b \<in> generate H"

lemma generate_into_G: "a \<in> generate (G \<inter> H) \<Longrightarrow> a \<in> G"
  by (induction rule: generate.induct) auto


definition subgroup_generated :: "'a set \<Rightarrow> 'a set"
  where "subgroup_generated S = generate (G \<inter> S)"

lemma inverse_in_subgroup_generated: "a \<in> subgroup_generated H \<Longrightarrow> inverse a \<in> subgroup_generated H"
  unfolding subgroup_generated_def
proof (induction rule: generate.induct)
  case (mult a b)
  then show ?case
    by (simp add: generate.mult generate_into_G inverse_composition_commute)
qed (auto simp add: generate.unit generate.incl generate.inv)

lemma subgroup_generated_is_monoid:
  fixes H                 
  shows "Group_Theory.monoid (subgroup_generated H) (\<cdot>) \<one>"
  unfolding subgroup_generated_def
proof qed (auto simp: generate.unit generate.mult associative generate_into_G)

lemma subgroup_generated_is_subset:
  fixes H                 
  shows "subgroup_generated H \<subseteq> G"
    using generate_into_G subgroup_generated_def by blast

lemma subgroup_generated_is_subgroup:
  fixes H                 
  shows "subgroup (subgroup_generated H) G (\<cdot>) \<one>"
proof
  show "subgroup_generated H \<subseteq> G"
    by (simp add: subgroup_generated_is_subset)
  show "a \<cdot> b \<in> subgroup_generated H"
    if "a \<in> subgroup_generated H" "b \<in> subgroup_generated H" for a b
    using that by (meson monoid.composition_closed subgroup_generated_is_monoid)         
  show "a \<cdot> b \<cdot> c = a \<cdot> (b \<cdot> c)"
    if "a \<in> subgroup_generated H" "b \<in> subgroup_generated H" "c \<in> subgroup_generated H"
    for a b c
    using that by (meson monoid.associative subgroup_generated_is_monoid)
  show "monoid.invertible (subgroup_generated H) (\<cdot>) \<one> u"
    if "u \<in> subgroup_generated H" for u
  proof (rule monoid.invertibleI )
    show "Group_Theory.monoid (subgroup_generated H) (\<cdot>) \<one>"
      by (simp add: subgroup_generated_is_monoid)
    show "u \<cdot> local.inverse u = \<one>" "local.inverse u \<cdot> u = \<one>" "u \<in> subgroup_generated H"
      using \<open>subgroup_generated H \<subseteq> G\<close> that by auto
    show "local.inverse u \<in> subgroup_generated H"
      using inverse_in_subgroup_generated that by blast
  qed 
qed (auto simp: generate_into_G generate.unit subgroup_generated_def)


end (* group *)

end