theory Euclidean_Space_Theory
  imports Complex_Main 
          Group_Further_Theory
          HOL.Filter

begin

no_notation Groups.plus_class.plus (infixl "+" 70)

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

locale linear_map = 
dom: real_vector_space V "(+)" \<zero> scale + codom: real_vector_space V' "(+')" "\<zero>'" scale' + map f V V'
for V and add (infixl "+" 70) and zero ("\<zero>") and scale (infixr "\<cdot>\<^sub>\<real>" 75) and V' and 
add' (infixl "+''" 70) and zero' ("\<zero>''") and scale' (infixr "\<cdot>\<^sub>\<real>''" 75) and f +
assumes additivity: "\<lbrakk>x \<in> V; y \<in> V\<rbrakk> \<Longrightarrow> f (x + y) = f x +' f y"
and homogeneity: "x \<in> V \<Longrightarrow> f (r \<cdot>\<^sub>\<real> x) = r \<cdot>\<^sub>\<real>' f x"


section \<open>Real Normed Vector Spaces\<close>

locale real_normed_vector_space = real_vector_space +
  fixes norm:: "'a \<Rightarrow> real" ("\<parallel>_\<parallel>")
  assumes is_nonneg: "x \<in> V \<Longrightarrow> \<parallel>x\<parallel> \<ge> 0"
and is_pos_on_nonzero: "x \<in> V \<Longrightarrow> (\<parallel>x\<parallel> = 0 \<longleftrightarrow> x = \<zero>)"
and is_linear_with_abs: "x \<in> V \<Longrightarrow> \<parallel>r \<cdot>\<^sub>\<real> x\<parallel> = \<bar>r\<bar> * \<parallel>x\<parallel>"
and triangle_eq_holds: "\<lbrakk>x \<in> V; y \<in> V\<rbrakk> \<Longrightarrow> \<parallel>x + y\<parallel> \<le> \<parallel>x\<parallel> + \<parallel>y\<parallel>"
begin

definition dist:: "'a \<Rightarrow> 'a \<Rightarrow> real"
  where "dist x y \<equiv> \<parallel>minus y x\<parallel>" 
(* Why the notation for minus from Group_Further_Theory.thy does not work here ? *)

(* prove that dist is a metric, hence prove that an euclidean space is a topological space *)

end (* real_normed_vector_space *)

sublocale real_normed_vector_space \<subseteq> topological_space sorry

locale bounded_linear_map = 
dom: real_normed_vector_space V add zero scale norm + 
codom: real_normed_vector_space V' add' zero' scale' norm' +
linear_map V add zero scale V' add' zero' scale' f
for V add zero scale norm V' add' zero' scale' norm' f +
assumes bounded: "\<exists>K. \<forall>x. norm' (f x) \<le> norm x * K"


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

definition distance:: "'a \<Rightarrow> 'a \<Rightarrow> real" ("\<d>'(_,_')")
  where "\<d>(u,v) \<equiv> sqrt (\<langle>minus u v , minus u v\<rangle>)"
(* Why the notation for minus from Group_Further_Theory.thy does not work here ? *)

(* prove that dist is a metric, hence prove that an euclidean space is a topological space *)

definition norm:: "'a \<Rightarrow> real" ("\<parallel>_\<parallel>")
  where "norm u \<equiv> sqrt (\<langle>u,u\<rangle>)"

(* prove that norm is a norm *)

end (* euclidean_vector_space *)

sublocale euclidean_vector_space \<subseteq> topological_space sorry

sublocale euclidean_vector_space \<subseteq> real_normed_vector_space sorry

(*
definition has_derivative :: "('a::real_normed_vector \<Rightarrow> 'b::real_normed_vector) \<Rightarrow>
    ('a \<Rightarrow> 'b) \<Rightarrow> 'a filter \<Rightarrow> bool"  (infix "(has'_derivative)" 50)
  where "(f has_derivative f') F \<longleftrightarrow>
    bounded_linear f' \<and>
    ((\<lambda>y. ((f y - f (Lim F (\<lambda>x. x))) - f' (y - Lim F (\<lambda>x. x))) /\<^sub>R norm (y - Lim F (\<lambda>x. x))) \<longlongrightarrow> 0) F"
*)

locale has_derivative = 
dom: real_normed_vector_space V add zero scale norm +
codom: real_normed_vector_space V' add' zero' scale' norm' +
map f V V' + map f' V V'
for V add zero scale norm V' add' zero' scale' norm' f f' +
fixes F:: "'a filter"
assumes is_bounded_linear: "bounded_linear_map V add zero scale norm V' add' zero' scale' norm' f'"
(* unfinished *)

(* To introduce abbreviation (f has_derivative f') F *)

text \<open>
  Usually the filter \<^term>\<open>F\<close> is \<^term>\<open>at x within s\<close>.  \<^term>\<open>(f has_derivative D)
  (at x within s)\<close> means: \<^term>\<open>D\<close> is the derivative of function \<^term>\<open>f\<close> at point \<^term>\<open>x\<close>
  within the set \<^term>\<open>s\<close>. Where \<^term>\<open>s\<close> is used to express left or right sided derivatives. In
  most cases \<^term>\<open>s\<close> is either a variable or \<^term>\<open>UNIV\<close>.
\<close>


term "is_filter"
term "bounded_linear"
term "Vector_Spaces.linear"
term "module_hom"
term "Lim"
term "filterlim"
term "filtermap"
term "Abs_filter"
term "eventually"
term "nhds"
term "principal"
print_locale "t2_space"

end