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
open_union [intro]: "\<And>F::('a set) set. (\<And>x. x \<in> F \<and> x \<subseteq> S \<and> is_open x) \<Longrightarrow> is_open (\<Union>x\<in>F. x)"

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
  where "ind_is_open U \<equiv> U \<subseteq> S \<and> (\<exists>V. V \<subseteq> X \<and> is_open V \<and> U = S \<inter> V)"

lemma ind_space_is_top_space:
  shows "topological_space S (ind_is_open)"
proof-
  have "ind_is_open S" using ind_is_open_def is_subset (* take V = X *) by auto
  moreover have "ind_is_open {}" using ind_is_open_def (* take V = {} *) by auto
  moreover have "\<And>U V. U \<subseteq> S \<Longrightarrow> V \<subseteq> S \<Longrightarrow> ind_is_open U \<Longrightarrow> ind_is_open V \<Longrightarrow> ind_is_open (U \<inter> V)"
  proof-
    fix U assume "U \<subseteq> S" and "ind_is_open U" obtain V1 where H1:"V1 \<subseteq> X \<and> is_open V1 \<and> U = S \<inter> V1"
      using \<open>ind_is_open U\<close> ind_is_open_def by auto
    fix V assume "V \<subseteq> S" and "ind_is_open V" obtain V2 where H2:"V2 \<subseteq> X \<and> is_open V2 \<and> V = S \<inter> V2"
      using \<open>ind_is_open V\<close> ind_is_open_def by auto
    have "is_open (V1 \<inter> V2) \<and> (U \<inter> V = S \<inter> (V1 \<inter> V2))" using H1 H2 open_inter by auto
    then show "ind_is_open (U \<inter> V)"
      using ind_is_open_def by (metis H1 inf.cobounded1 subset_trans)
  qed
  moreover have "\<And>F::('a set) set. (\<And>x. x \<in> F \<and> x \<subseteq> S \<and> ind_is_open x) \<Longrightarrow> ind_is_open (\<Union>x\<in>F. x)"
  proof-
    fix F assume "\<And>x. x \<in> F \<and> x \<subseteq> S \<and> ind_is_open x" obtain F' where "\<And>x. x \<in> F \<and> x \<subseteq> S \<and> ind_is_open x \<Longrightarrow> (F' x) \<subseteq> X \<and> is_open (F' x) \<and> x = S \<inter> (F' x)"
      using ind_is_open_def by meson
    then have "is_open (\<Union>x\<in>F. F' x) \<and> ((\<Union>x\<in>F. x) = S \<inter> (\<Union>x\<in>F. F' x))" 
      using open_union
      by (metis SUP_upper2 \<open>\<And>x. x \<in> F \<and> x \<subseteq> S \<and> ind_is_open x\<close> inf_left_idem set_eq_subset)
    then show "ind_is_open (\<Union>x\<in>F. x)" by (simp add: \<open>\<And>x. x \<in> F \<and> x \<subseteq> S \<and> ind_is_open x\<close>)
  qed
  thus ?thesis
    by (simp add: calculation(1-3) topological_space_def)
qed

lemma is_open_from_ind_is_open:
  assumes "is_open S" and "ind_is_open U"
  shows "is_open U"
  using assms open_inter ind_is_open_def is_subset by auto

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