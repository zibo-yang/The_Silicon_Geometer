theory Topological_Space_Theory
imports Main

begin

section \<open>Topological Spaces\<close>

locale topological_space = fixes S :: "'a set" and is_open :: "'a set \<Rightarrow> bool"
  assumes open_space [simp, intro]: "is_open S" and 
open_inter [intro]: "\<lbrakk>U \<subseteq> S; V \<subseteq> S\<rbrakk> \<Longrightarrow> is_open U \<Longrightarrow> is_open V \<Longrightarrow> is_open (U \<inter> V)" and
open_union [intro]: "\<forall>F::('a set) set. (\<forall>x\<in>F. x \<subseteq> S \<and> is_open x) \<Longrightarrow> is_open (\<Union>x\<in>F. x)"

begin

definition is_closed :: "'a set \<Rightarrow> bool"
  where "is_closed U \<equiv> U \<subseteq> S \<and> is_open (S - U)"

subsection \<open>Topological Basis\<close>

inductive generated_topology :: "'a set set \<Rightarrow> 'a set \<Rightarrow> bool" for B :: "'a set set"
  where
    UNIV: "generated_topology B S"
  | Int: "generated_topology B (U \<inter> V)" if "generated_topology B U" and "generated_topology B V"
  | UN: "generated_topology B (\<Union>K)" if "(\<And>U. U \<in> K \<Longrightarrow> generated_topology B U)"
  | Basis: "generated_topology B b" if "b \<in> B \<and> b \<subseteq> S"

end (* topological_space *)

end