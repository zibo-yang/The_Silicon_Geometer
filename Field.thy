theory Field (* Can't use the plural Fields because HOL.Fields *)
  imports "Jacobson_Basic_Algebra.Ring_Theory"
          (* "Polynomials.MPoly_PM" *)
          "HOL-Computational_Algebra.Polynomial"
          "HOL.Topological_Spaces"

begin

no_notation plus (infixl "+" 65)
(* no_notation map_scale (infixl "\<cdot>" 71) *)

section \<open>Fields\<close>

locale field = ring R "(+)" "(\<cdot>)" "\<zero>" "\<one>" 
  for R and addition (infixl "+" 65) and multiplication (infixl "\<cdot>" 70) and zero ("\<zero>") and unit ("\<one>") +
  assumes commutative_mult: "\<lbrakk> a \<in> R; b \<in> R \<rbrakk> \<Longrightarrow> a \<cdot> b = b \<cdot> a" and nonzero: "\<zero> \<noteq> \<one>" and 
invertible_mult: "a \<in> R \<Longrightarrow> a \<noteq> \<zero> \<Longrightarrow> \<exists>b\<in>R. a \<cdot> b = \<one>"
begin

lemma left_inv_mult_is_right_inv:
  assumes "a \<in> R" and "b \<in> R" and "a \<cdot> b = \<one>"
  shows "b \<cdot> a = \<one>"
  using assms commutative_mult by simp

lemma uniqueness_of_inv: 
  assumes "a \<in> R" and "a \<noteq> \<zero>" and "b \<in> R" and "c \<in> R" and "a \<cdot> b = \<one>" and "a \<cdot> c = \<one>"
  shows "b = c" sorry

end

locale subfield = subring S R "(+)" "(\<cdot>)" "\<zero>" "\<one>" 
  for S and R and addition (infix "+" 65) and multiplication (infix "\<cdot>" 70) and zero ("\<zero>") and unit ("\<one>") +
  assumes stable_under_inv: "\<lbrakk>a \<in> S; b \<in> R\<rbrakk> \<Longrightarrow> a \<noteq> \<zero> \<Longrightarrow> a \<cdot> b = \<one> \<Longrightarrow> b \<in> S" 


section \<open>Algebraically Closed Fields\<close>

locale alg_closed_field = field k "(+)" "(\<cdot>)" "\<zero>" "\<one>"
  for k::"'a::comm_semiring_0 set" and addition (infix "+" 65) and multiplication (infix "\<cdot>" 70) and zero ("\<zero>") and unit ("\<one>") +
  assumes alg_closed: "\<forall>(f::'a poly). Polynomial.degree f > 0 \<longrightarrow> (\<exists>p. poly f p = 0)" 
(* 
The assumption alg_closed above should probably be expressed using univariate polynomials seen as 
a special case of multivariate polynomials as defined in the archive "Executable Multivariate Polynomials" 
*)

begin

(* Possibly some equivalent formulations of the property of being algebraically closed *)
(* If n=1 in the blueprint then the affine space is just carrier k. *)

(* def. 0.0.3 *)
definition zero_set:: "'a poly set \<Rightarrow> 'a set"
  where "zero_set T \<equiv> {p \<in> k. \<forall>f\<in>T. poly f p = 0}"

(* def 0.0.4 *)
definition algebraic:: "'a set \<Rightarrow> bool"
  where "algebraic Y \<equiv> Y \<subseteq> k \<and> (\<exists>(T::'a poly set). Y = zero_set T)"

(* exercise 0.0.5 *)
lemma empty_set_is_algebraic:
  shows "algebraic empty" sorry

lemma whole_space_is_algebraic:
  shows "algebraic k" sorry

(* exercise 0.0.6 *)
lemma inter_of_alg_family_is_algebraic:
  fixes f::"'a set set"
  assumes "Y \<in> f \<Longrightarrow> algebraic Y"
  shows "algebraic (\<Inter>f)" sorry

(* exercise 0.0.7 *)
lemma union_of_two_algebraic_is_algebraic:
  assumes "algebraic Y" and "algebraic Z"
  shows "algebraic (Y \<union> Z)" sorry

(* def. 0.0.8 *)
definition zariski_open:: "'a set \<Rightarrow> bool"
  where "zariski_open S \<equiv> \<exists>Y. algebraic Y \<and> S = k - Y"

(* exercise 0.0.9 *)
lemma zariski_topology_is_topology:
  shows "topology zariski_open" sorry

definition  zariski_closed:: "'a set \<Rightarrow> bool"
  where "zariski_closed S \<equiv> zariski_open (k - S)"

(* def. 0.0.10 *)
definition irreducible:: "'a set \<Rightarrow> bool"
  where "irreducible S \<equiv> S \<subseteq> k \<and> S \<noteq> empty \<and> \<not>(\<exists>U V. S = U \<union> V \<and> zariski_closed U \<and> 
zariski_closed V \<and> U \<subset> k \<and> V \<subset> k)"

(* def 0.0.11 *)
definition aff_alg_variety:: "'a set \<Rightarrow> bool"
  where "aff_alg_variety S \<equiv> irreducible S \<and> zariski_closed S"

(* def 0.0.12 *)
definition quasi_aff_variety:: "'a set \<Rightarrow> bool"
  where "quasi_aff_variety U \<equiv> \<exists>S Y. aff_alg_variety S \<and> zariski_open Y \<and> U = S \<inter> Y"
 
end

end