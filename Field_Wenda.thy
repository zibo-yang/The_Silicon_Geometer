theory Field_Wenda (* Can't use the plural Fields because HOL.Fields *)
  imports "Jacobson_Basic_Algebra.Ring_Theory"
          (* "Polynomials.MPoly_PM"*)
          (*"HOL-Computational_Algebra.Polynomial" *)
          "HOL.Topological_Spaces"
          "HOL-Analysis.Analysis"
begin

no_notation plus (infixl "+" 65)

(* We formalize below our blueprint, first with n=1 *)

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


section \<open>Univariate Polynomials\<close>

type_synonym 'a upoly = "nat \<Rightarrow> 'a"

context ring  
begin

definition degree :: "'a upoly \<Rightarrow> nat"
  where "degree p = (LEAST n. \<forall>i>n. p i = \<zero>)"

definition zero_poly :: "'a upoly"
  where "zero_poly \<equiv> \<lambda>_. \<zero>"

primrec foldr :: "('a \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'a list \<Rightarrow> 'b \<Rightarrow> 'b" where
foldr_Nil:  "foldr f [] = id" |
foldr_Cons: "foldr f (x # xs) = f x \<circ> foldr f xs"

definition coeffs :: "'a upoly \<Rightarrow> 'a list"
  where "coeffs p = (if p = zero_poly then [] else map (\<lambda>i. p i) [0 ..< Suc (degree p)])"

definition fold_coeffs :: "('a \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'a upoly \<Rightarrow> 'b \<Rightarrow> 'b"
  where "fold_coeffs f p = foldr f (coeffs p)"

definition eval_poly :: "'a upoly \<Rightarrow> 'a \<Rightarrow> 'a"
  where "eval_poly p = fold_coeffs (\<lambda>a f x. a + x \<cdot> f x) p (\<lambda>x. \<zero>)" \<comment> \<open>The Horner Schema\<close>

definition is_upoly :: "'a set \<Rightarrow> 'a upoly \<Rightarrow> bool" where
  "is_upoly carrier f \<equiv>  ((\<forall>\<^sub>\<infinity> n. f n = \<zero>) \<and> (\<forall>n. f n \<in> carrier))"

definition from_carrier_set :: "'a set \<Rightarrow> ('a upoly) set" where
  "from_carrier_set carrier = {f. is_upoly carrier f}"

end

section \<open>Algebraically Closed Fields\<close>

locale alg_closed_field = field +
     (*I don't think 'degree f > 0' is really necessary here*)
  assumes alg_closed: "\<forall>f \<in> from_carrier_set R. degree f > 0 \<longrightarrow> (\<exists>r\<in>R. eval_poly f r = \<zero>)" 
   

context field (*These definition may not need an algebraic closed field*)
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