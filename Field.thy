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

locale alg_closed_field = field F "(+)" "(\<cdot>)" "\<zero>" "\<one>"
  for F and addition (infix "+" 65) and multiplication (infix "\<cdot>" 70) and zero ("\<zero>") and unit ("\<one>") +
  assumes alg_closed: "\<forall>(p::'a poly). Polynomial.degree p > 0 \<longrightarrow> (\<exists>r. poly p r = 0)" 
(* 
The assumption alg_closed above should probably be expressed using univariate polynomials seen as 
a special case of multivariate polynomials as defined in the archive "Executable Multivariate Polynomials" 
*)

(*
begin

Possibly some equivalent formulations of the property of being algebraically closed
 
end
*)
end