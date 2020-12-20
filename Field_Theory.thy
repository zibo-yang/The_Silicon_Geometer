theory Field_Theory
  imports "Comm_Ring_Theory"
          (* "Polynomials.MPoly_PM" *)
          (* "HOL-Computational_Algebra.Polynomial" *)
          "HOL.Topological_Spaces"

begin


section \<open>Fields\<close>

no_notation plus (infixl "+" 65)

locale field = comm_ring R "(+)" "(\<cdot>)" "\<zero>" "\<one>" 
  for R and addition (infixl "+" 65) and multiplication (infixl "\<cdot>" 70) and zero ("\<zero>") and unit ("\<one>") +
  assumes nonzero: "\<zero> \<noteq> \<one>" and invertible_mult: "a \<in> R \<Longrightarrow> a \<noteq> \<zero> \<Longrightarrow> \<exists>b\<in>R. a \<cdot> b = \<one>"

begin

declare nonzero [simp]
lemma nonzero' [simp]: "\<one> \<noteq> \<zero>"
  using nonzero by blast 

lemma left_inv_mult_is_right_inv:
  assumes "a \<in> R" and "b \<in> R" and "a \<cdot> b = \<one>"
  shows "b \<cdot> a = \<one>"
  using assms commutative_mult by simp

lemma uniqueness_of_inv: 
  assumes "a \<cdot> b = \<one>" "a \<cdot> c = \<one>" "a \<in> R" "b \<in> R" "c \<in> R"
  shows "b = c"
  using assms commutative_mult multiplicative.inverse_unique by presburger

end

locale subfield = subring S R "(+)" "(\<cdot>)" "\<zero>" "\<one>" 
  for S and R and addition (infix "+" 65) and multiplication (infix "\<cdot>" 70) and zero ("\<zero>") and unit ("\<one>") +
  assumes stable_under_inv: "\<lbrakk>a \<in> S; b \<in> R\<rbrakk> \<Longrightarrow> a \<noteq> \<zero> \<Longrightarrow> a \<cdot> b = \<one> \<Longrightarrow> b \<in> S" 


section \<open>Univariate Polynomials\<close>

type_synonym 'a upoly = "nat \<Rightarrow> 'a"

context ring  
begin

definition degree :: "'a upoly \<Rightarrow> nat"
  where "degree p = (LEAST n. \<forall>i>n. p i = \<zero>)"

definition zero_poly :: "'a upoly"
  where "zero_poly \<equiv> \<lambda>_. \<zero>"

definition coeffs :: "'a upoly \<Rightarrow> 'a list"
  where "coeffs p = (if p = zero_poly then [] else map (\<lambda>i. p i) [0 ..< Suc (degree p)])"

definition fold_coeffs :: "('a \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'a upoly \<Rightarrow> 'b \<Rightarrow> 'b"
  where "fold_coeffs f p = foldr f (coeffs p)"

definition eval_poly :: "'a upoly \<Rightarrow> 'a \<Rightarrow> 'a"
  where "eval_poly p = fold_coeffs (\<lambda>a f x. a + x \<cdot> f x) p (\<lambda>x. \<zero>)" \<comment> \<open>The Horner Schema\<close>

definition is_upoly :: "'a set \<Rightarrow> 'a upoly \<Rightarrow> bool" 
  where "is_upoly carrier f \<equiv>  ((\<forall>\<^sub>\<infinity> n. f n = \<zero>) \<and> (\<forall>n. f n \<in> carrier))"

definition upoly_with_coeff_in :: "'a set \<Rightarrow> ('a upoly) set" 
  where "upoly_with_coeff_in carrier = {f. is_upoly carrier f}"

end


section \<open>Algebraically Closed Fields\<close>

locale alg_closed_field = field +
  assumes alg_closed: "\<forall>f \<in> upoly_with_coeff_in R. degree f > 0 \<longrightarrow> (\<exists>r\<in>R. eval_poly f r = \<zero>)" 

(* Possibly some equivalent formulations of the property of being algebraically closed *)


end