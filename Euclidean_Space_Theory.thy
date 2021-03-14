theory Euclidean_Space_Theory
  imports Group_Further_Theory
          Complex_Main

begin


section \<open>Real Vector Spaces\<close>

locale real_vector_space = abelian_group V add zero 
  for V and add (infixl "+" 70) and zero ("\<zero>") + 
  fixes scale:: "real \<Rightarrow> 'a \<Rightarrow> 'a" (infixr "\<cdot>\<^sub>\<real>" 75)
  assumes scale_add: "\<lbrakk>x \<in> V; y \<in> V\<rbrakk> \<Longrightarrow> r \<cdot>\<^sub>\<real> (x + y) = r \<cdot>\<^sub>\<real> x + r \<cdot>\<^sub>\<real> y"
  and add_scale: "x \<in> V \<Longrightarrow> (r + s) \<cdot>\<^sub>\<real> x = r \<cdot>\<^sub>\<real> x + s \<cdot>\<^sub>\<real> x"
  and scale_scale: "x \<in> V \<Longrightarrow> r \<cdot>\<^sub>\<real> s \<cdot>\<^sub>\<real> x = (r * s) \<cdot>\<^sub>\<real> x"
  and one_scale: "x \<in> V \<Longrightarrow> 1 \<cdot>\<^sub>\<real> x = x"
begin

abbreviation divide:: "'a \<Rightarrow> real \<Rightarrow> 'a"  (infixl "'/\<^sub>\<real>" 70)
  where "x /\<^sub>\<real> r \<equiv> Fields.inverse r \<cdot>\<^sub>\<real> x"

end (* real_vector_space *)


section \<open>Real Normed Vector Spaces\<close>

locale real_normed_vector_space = real_vector_space +
  fixes norm:: "'a \<Rightarrow> real" ("\<parallel>_\<parallel>")
  assumes is_nonneg: "x \<in> V \<Longrightarrow> \<parallel>x\<parallel> \<ge> 0"
and is_pos_on_nonzero: "x \<in> V \<Longrightarrow> (\<parallel>x\<parallel> = 0 \<longleftrightarrow> x = \<zero>)"
and is_linear_with_abs: "x \<in> V \<Longrightarrow> \<parallel>r \<cdot>\<^sub>\<real> x\<parallel> = \<bar>r\<bar> * \<parallel>x\<parallel>"
and triangle_eq_holds: "\<lbrakk>x \<in> V; y \<in> V\<rbrakk> \<Longrightarrow> \<parallel>x + y\<parallel> \<le> \<parallel>x\<parallel> + \<parallel>y\<parallel>"


section \<open>Inner Product Spaces\<close>

locale inner_product_space = real_vector_space +
  fixes inner_prod:: "'a \<Rightarrow> 'a \<Rightarrow> real" ("\<langle>_,_\<rangle>")
  assumes scale_is_linear: "\<lbrakk>x \<in> V; y \<in> V\<rbrakk> \<Longrightarrow> \<langle>r \<cdot>\<^sub>\<real> x, y\<rangle> = r * \<langle>x, y\<rangle>"
and add_is_linear: "\<lbrakk>x \<in> V; y \<in> V; z \<in> V\<rbrakk> \<Longrightarrow> \<langle>x + y, z\<rangle> = \<langle>x,z\<rangle> + \<langle>y,z\<rangle>"
and is_symmetric: "\<lbrakk>x \<in> V; y \<in> V\<rbrakk> \<Longrightarrow> \<langle>x,y\<rangle> = \<langle>y,x\<rangle>"
and is_pos_definite: "x \<in> V \<Longrightarrow> x \<noteq> \<zero> \<Longrightarrow> \<langle>x,x\<rangle> > 0"
begin

lemma inner_prod_of_zero:
  shows "\<langle>\<zero>,\<zero>\<rangle> = 0" sorry

lemma is_positive_semi_definite:
  assumes "x \<in> V"
  shows "\<langle>x,x\<rangle> \<ge> 0" sorry

lemma is_definite:
  assumes "x \<in> V"
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

(* prove that dist is a metric, hence prove that an euclidean space is a topological space *)

definition norm:: "'a \<Rightarrow> real" ("\<parallel>_\<parallel>")
  where "norm u \<equiv> sqrt (\<langle>u,u\<rangle>)"

(* prove that norm is a norm *)

end (* euclidean_vector_space *)

sublocale euclidean_vector_space \<subseteq> topological_space sorry

sublocale euclidean_vector_space \<subseteq> real_normed_vector_space sorry

end