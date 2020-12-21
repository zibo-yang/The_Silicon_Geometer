theory Topological_Space_Theory
  imports Main
          HOL.Real
          "Jacobson_Basic_Algebra.Set_Theory"
          Set_Further_Theory

begin

section \<open>Topological Spaces\<close>

locale topological_space = fixes S :: "'a set" and is_open :: "'a set \<Rightarrow> bool"
  assumes open_space [simp, intro]: "is_open S" and open_empty [simp, intro]: "is_open {}" and
open_inter [intro]: "\<lbrakk>U \<subseteq> S; V \<subseteq> S\<rbrakk> \<Longrightarrow> is_open U \<Longrightarrow> is_open V \<Longrightarrow> is_open (U \<inter> V)" and
open_union [intro]: "\<forall>F::('a set) set. (\<forall>x\<in>F. x \<subseteq> S \<and> is_open x) \<Longrightarrow> is_open (\<Union>x\<in>F. x)"

begin

definition is_closed :: "'a set \<Rightarrow> bool"
  where "is_closed U \<equiv> U \<subseteq> S \<and> is_open (S - U)"

end (* topological_space *)

subsection \<open>Topological Basis\<close>

inductive generated_topology :: "'a set set \<Rightarrow> 'a set \<Rightarrow> bool" for B :: "'a set set"
  where
    UNIV: "generated_topology B S"
  | Int: "generated_topology B (U \<inter> V)" if "generated_topology B U" and "generated_topology B V"
  | UN: "generated_topology B (\<Union>K)" if "(\<And>U. U \<in> K \<Longrightarrow> generated_topology B U)"
  | Basis: "generated_topology B b" if "b \<in> B \<and> b \<subseteq> S"

subsection \<open>Covers\<close>

locale cover_of_subset =
  fixes X:: "'a set" and U:: "'a set" and index:: "real set" and cover:: "real \<Rightarrow> 'a set"
(* We use real instead of index::"'b set" otherwise we get some troubles with locale sheaf_of_rings
in Comm_Ring_Theory.thy *)
  assumes is_subset: "U \<subseteq> X" and are_subsets: "\<And>i. i \<in> index \<Longrightarrow> cover i \<subseteq> X"
and covering: "U \<subseteq> (\<Union>i\<in>index. cover i)"

locale open_cover_of_subset = topological_space X is_open + cover_of_subset X U I C 
  for X and is_open and U and I and C +
  assumes are_open_subspaces: "\<And>i. i\<in>I \<Longrightarrow> is_open (C i)"

locale open_cover_of_open_subset = open_cover_of_subset X is_open U I C 
  for X and is_open and U and I and C +
  assumes is_open_subset: "is_open U"

subsection \<open>Induced Topology\<close>

locale ind_topology = topological_space X is_open for X and is_open +
  fixes S:: "'a set"
  assumes is_subset: "S \<subseteq> X"
begin

definition ind_is_open:: "'a set \<Rightarrow> bool"
  where "ind_is_open U \<equiv> U \<subseteq> S \<and> (\<exists>V. is_open V \<and> U = S \<inter> V)"

lemma 
  shows "topological_space S (ind_is_open)" sorry

end (* induced topology *)


subsection \<open>Continuous Maps\<close>

locale continuous_map = source: topological_space X is_open + target: topological_space X' is_open' 
+ map f X X'
  for X and is_open and X' and is_open' and f +
  assumes is_continuous: "\<And>U. is_open' U \<Longrightarrow> is_open {x. f x \<in> U}"


subsection \<open>Homeomorphisms\<close>

text \<open>The topological isomorphisms between topological spaces are called homeomorphisms.\<close>

locale homeomorphism = 
continuous_map + bijective_map f X X' + 
continuous_map X' is_open' X is_open "f\<^sup>\<inverse> X X'"

end