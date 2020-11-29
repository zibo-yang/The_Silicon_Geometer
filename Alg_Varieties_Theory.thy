theory Alg_Varieties_Theory
  imports Field_Theory 


begin

(* We formalize below our blueprint, first with n=1, but this should be generalized. 
If n=1 then the affine space is just carrier k. *)

context field
begin

(* def. 0.0.3 *)
definition zero_set :: "('a upoly) set \<Rightarrow> 'a set"
  where "zero_set T \<equiv> {p \<in> R. \<forall>f\<in>T. eval_poly f p = \<zero>}"

(* def 0.0.4 *)
definition algebraic :: "'a set \<Rightarrow> bool"
  where "algebraic Y \<equiv> (\<exists>T. Y = zero_set T)"

(* exercise 0.0.5 *)
lemma empty_set_is_algebraic:
  shows "algebraic empty" sorry

lemma whole_space_is_algebraic:
  shows "algebraic R" sorry

(* exercise 0.0.6 *)
lemma inter_of_alg_family_is_algebraic:
  fixes f :: "'a set set"
  assumes "Y \<in> f \<Longrightarrow> algebraic Y"
  shows "algebraic (\<Inter>f)" sorry

(* exercise 0.0.7 *)
lemma union_of_two_algebraic_is_algebraic:
  assumes "algebraic Y" and "algebraic Z"
  shows "algebraic (Y \<union> Z)" sorry

(* def. 0.0.8 *)
definition zariski_open :: "'a set \<Rightarrow> bool"
  where "zariski_open S = (\<exists>Y. algebraic Y \<and> S = R - Y)"

(* exercise 0.0.9 *)
lemma zariski_topology_is_topology:
  shows "istopology zariski_open" sorry

definition  zariski_closed :: "'a set \<Rightarrow> bool"
  where "zariski_closed S \<equiv> zariski_open (R - S)"

(* def. 0.0.10 *)
definition irreducible :: "'a set \<Rightarrow> bool"
  where "irreducible S \<equiv> S \<subseteq> R \<and> S \<noteq> empty \<and> \<not>(\<exists>U V. S = U \<union> V \<and> zariski_closed U \<and> 
zariski_closed V \<and> U \<subset> R \<and> V \<subset> R)"

(* def 0.0.11 *)
definition aff_alg_variety :: "'a set \<Rightarrow> bool"
  where "aff_alg_variety S \<equiv> irreducible S \<and> zariski_closed S"

(* def 0.0.12 *)
definition quasi_aff_variety :: "'a set \<Rightarrow> bool"
  where "quasi_aff_variety U \<equiv> \<exists>S Y. aff_alg_variety S \<and> zariski_open Y \<and> U = S \<inter> Y"
 
end

end