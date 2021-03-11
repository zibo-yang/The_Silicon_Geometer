theory Euclidean_Space_Theory
  imports Group_Further_Theory
          Complex_Main

begin


section \<open>Real Vector Spaces\<close>

locale real_vector_space = abelian_group V add zero 
  for V and add (infixl "+" 70) and zero ("\<zero>") + 
  fixes scale:: "real \<Rightarrow> 'a \<Rightarrow> 'a" (infixr "\<cdot>\<^sub>R" 75)
  assumes scale_add: "r \<cdot>\<^sub>R (x + y) = r \<cdot>\<^sub>R x + r \<cdot>\<^sub>R y"
  and add_scale: "(r + s) \<cdot>\<^sub>R x = r \<cdot>\<^sub>R x + s \<cdot>\<^sub>R x"
  and scale_scale: "r \<cdot>\<^sub>R s \<cdot>\<^sub>R x = (r * s) \<cdot>\<^sub>R x"
  and one_scale: "1 \<cdot>\<^sub>R x = x"
begin

abbreviation divide:: "'a \<Rightarrow> real \<Rightarrow> 'a"  (infixl "'/\<^sub>R" 70)
  where "x /\<^sub>R r \<equiv> Fields.inverse r \<cdot>\<^sub>R x"

end (* real_vector_space *)


section \<open>Inner Product Spaces\<close>

locale inner_product_space = real_vector_space +
  fixes inner_prod:: "'a \<Rightarrow> 'a \<Rightarrow> real" ("\<langle>_,_\<rangle>")
  assumes scale_is_linear: "\<langle>r \<cdot>\<^sub>R x, y\<rangle> = r * \<langle>x, y\<rangle>"
and add_is_linear: "\<langle>x + y, z\<rangle> = \<langle>x,z\<rangle> + \<langle>y,z\<rangle>"
and is_symmetric: "\<langle>x,y\<rangle> = \<langle>y,x\<rangle>"
and is_positive_definite: "x \<noteq> \<zero> \<Longrightarrow> \<langle>x,x\<rangle> > 0"
begin

lemma inner_prod_of_zero:
  shows "\<langle>\<zero>,\<zero>\<rangle> = 0" sorry

lemma is_positive_semi_definite:
  shows "\<langle>x,x\<rangle> \<ge> 0" sorry

lemma is_definite:
  shows "\<langle>x,x\<rangle> = 0 \<Longrightarrow> x = \<zero>" sorry

end (* inner_product_space *)


section \<open>Euclidean Vector Spaces\<close>

locale euclidean_vector_space = inner_product_space +
  fixes n:: nat and Basis:: "'a set" 
  assumes is_nonempty [simp]: "n \<ge> 1"
and dim [simp]: "card Basis = n"
and inner_basis: "\<lbrakk>u \<in> Basis; v \<in> Basis\<rbrakk> \<Longrightarrow> \<langle>u,v\<rangle> = (if u = v then 1 else 0)"
and euclidean_all_zero_iff: "(\<forall>u\<in>Basis. \<langle>x,u\<rangle> = 0) \<longleftrightarrow> (x = \<zero>)"
(* the two last axioms should be deduced from two axioms asserting that Basis is free and spans V *)
begin

definition dist:: "'a \<Rightarrow> 'a \<Rightarrow> real" ("\<d>'(_,_')")
  where "\<d>(u,v) \<equiv> sqrt (\<langle>minus u v , minus u v\<rangle>)"
(* Why the notation for minus from Group_Further_Theory.thy does not work here ? *)

end (* euclidean_vector_space *)

end