theory Field (* Can't use the plural Fields because HOL.Fields *)
  imports "Jacobson_Basic_Algebra.Ring_Theory"
          (* "Polynomials.MPoly_PM" *)
          "HOL-Computational_Algebra.Polynomial"

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
definition is_alg:: "'a set \<Rightarrow> bool"
  where "is_alg Y \<equiv> Y \<subseteq> k \<and> (\<exists>(T::'a poly set). Y = zero_set T)"

(* exercise 0.0.5 *)
lemma empty_set_is_alg:
  shows "is_alg empty" sorry

lemma whole_space_is_alg:
  shows "is_alg k" sorry

(* exercise 0.0.6 *)
lemma inter_of_alg_family_is_alg:
  fixes f::"'a set set"
  assumes "Y \<in> f \<Longrightarrow> is_alg Y"
  shows "is_alg (\<Inter>f)" sorry

(* exercise 0.0.7 *)
lemma union_of_two_alg_is_alg:
  assumes "is_alg Y" and "is_alg Z"
  shows "is_alg (Y \<union> Z)" sorry
 
end

end