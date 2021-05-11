theory Euclidean_Space_Theory
  imports Complex_Main 
          Group_Extras
          HOL.Filter
          Topological_Space
          
begin

no_notation Groups.plus_class.plus (infixl "+" 70)
(*notation Group_Further_Theory.abelian_group.minus (infixl "-" 65)*)


section \<open>Real Vector Spaces\<close>

locale real_vector_space = abelian_group V add zero 
  for V and add (infixl "+" 70) and zero ("\<zero>") + 
  fixes scale:: "real \<Rightarrow> 'a \<Rightarrow> 'a" (infixr "\<cdot>\<^sub>\<real>" 75)
  assumes scale_add: "\<lbrakk>x \<in> V; y \<in> V\<rbrakk> \<Longrightarrow> r \<cdot>\<^sub>\<real> (x + y) = r \<cdot>\<^sub>\<real> x + r \<cdot>\<^sub>\<real> y"
  and add_scale: "x \<in> V \<Longrightarrow> (r + s) \<cdot>\<^sub>\<real> x = r \<cdot>\<^sub>\<real> x + s \<cdot>\<^sub>\<real> x"
  and scale_scale: "x \<in> V \<Longrightarrow> r \<cdot>\<^sub>\<real> s \<cdot>\<^sub>\<real> x = (r * s) \<cdot>\<^sub>\<real> x"
  and one_scale: "x \<in> V \<Longrightarrow> 1 \<cdot>\<^sub>\<real> x = x"
  and scale_closed: "x \<in> V \<Longrightarrow> r \<cdot>\<^sub>\<real> x \<in> V"
begin

abbreviation divide:: "'a \<Rightarrow> real \<Rightarrow> 'a"  (infixl "'/\<^sub>\<real>" 70)
  where "x /\<^sub>\<real> r \<equiv> Fields.inverse r \<cdot>\<^sub>\<real> x"

end (* real_vector_space *)

locale linear_map = 
dom: real_vector_space V "(+)" \<zero> scale + codom: real_vector_space V' "(+')" "\<zero>'" scale' + map f V V'
for V and add (infixl "+" 70) and zero ("\<zero>") and scale (infixr "\<cdot>\<^sub>\<real>" 75) and V' and 
add' (infixl "+''" 70) and zero' ("\<zero>''") and scale' (infixr "\<cdot>\<^sub>\<real>''" 75) and f 
 +
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
lemma dist_nonneg:
  assumes "x \<in> V" and "y \<in> V"
  shows"dist x y \<ge> 0"
proof-
  from assms have "minus y x \<in> V" 
    by (auto simp: minus_def)
  thus "dist x y \<ge> 0" 
    by (auto simp add:is_nonneg dist_def)
qed
lemma dist_nonzero:
  assumes "x \<in> V" and "y \<in> V"
  shows" dist x y = 0 \<longleftrightarrow> x = y"
proof
  from assms have "inverse x \<in> V" 
    unfolding invertible invertible_inverse_closed 
    by auto
  with assms have "minus y x \<in> V" 
    by (auto simp add: minus_def)
  hence "minus y x = \<zero>" if "dist x y = 0"
    using dist_def  is_pos_on_nonzero that
    by auto
  with assms show "x = y" if "dist x y = 0"
    using minus_def invertible_inverse_inverse that
    by (metis \<open>local.inverse x \<in> V\<close> 
              invertible invertible_left_inverse 
              local.inverse_unique)
next
  from assms have "y = inverse (inverse x)" if "x = y"
    using invertible that  
    by auto
  with assms have "minus y x = \<zero>" if "x = y"
    unfolding minus_def
    using invertible invertible_right_inverse that 
    by auto
  thus  "dist x y = 0"if "x = y" 
    unfolding dist_def 
    using is_pos_on_nonzero that 
    by auto
qed

lemma dist_triangle:
  assumes"x \<in> V" " y \<in> V" "z \<in> V"
  shows"dist x y + dist y z \<ge> dist x z"
proof-
  from assms have interm: "(minus y x) + (minus z y) = minus z x" 
    unfolding minus_def
    by (smt (verit) 
        associative 
        commutative 
        composition_closed 
        invertible 
        invertible_inverse_closed 
        monoid.invertible_right_inverse2 
        monoid_axioms)
  with assms show "dist x y + dist y z \<ge> dist x z" 
    unfolding dist_def
    using triangle_eq_holds[of "minus y x" "minus z y"]
          minus_def 
    by auto 
qed

lemma dist_is_symmetric:
  assumes "x \<in> V""y \<in> V"
  shows"dist x y = dist y x"
proof-
  from assms have xy:"minus x y \<in> V"and yx:"minus y x \<in> V"
  proof -
    show "local.minus x y \<in> V"
      by (simp add: assms(1) assms(2) minus_def)
    next
    show "local.minus y x \<in> V"
      by (simp add: assms(1) assms(2) minus_def)
  qed
  with assms have "minus x y + minus y x = \<zero>"
    by (simp add: associative invertible_left_inverse2 minus_def)
  with xy yx have "minus y x + (-1) \<cdot>\<^sub>\<real> (minus y x) = \<zero>"
    by (smt (z3) associative left_unit one_scale real_vector_space.add_scale real_vector_space_axioms scale_closed)
  thus ?thesis
    by (smt (z3) \<open>local.minus x y + local.minus y x = \<zero>\<close> commutative dist_def is_linear_with_abs monoid.inverse_equality monoid_axioms one_scale scale_closed xy yx)
qed

   
(* prove that dist is a metric, hence prove that an euclidean space is a topological space *)
definition is_open_space::"'a set \<Rightarrow> bool" where 
"is_open_space K \<equiv> (K \<subseteq> V) \<and> 
(\<forall>k. k \<in> K \<longrightarrow> (\<exists>r::real . r > 0 \<longrightarrow>(\<forall>z. z \<in> V \<longrightarrow> dist z k \<le> r \<longrightarrow> z \<in> K)))"

(*new*)
definition disk::"'a \<Rightarrow> real \<Rightarrow> 'a set " ("D'(_,_')") where
"D(x,r) \<equiv> {y. y \<in> V \<and> (dist y x < r)}"

(*new*)
lemma disk_contains_center:
  assumes "r > 0""x \<in> V"
  shows"x \<in> D(x,r)"
    unfolding disk_def
    using dist_nonzero assms
    by fastforce

(*new*)
lemma disk_is_open:
  assumes "x \<in> V"
  shows "is_open_space D(x, r)"
    unfolding is_open_space_def
    using disk_def assms
    by auto 

(*new*)
(*important conclusion for lemma is_hausdorff_rnvs*)
lemma empty_intersection:
  assumes "x \<in> V" "y \<in> V" "x \<noteq> y""r1 + r2 \<le> dist x y "
  shows "D(x,r1) \<inter> D(y,r2) = {}"
proof-
  from assms have "D(x,r1) \<inter> D(y,r2) = {a. a \<in> V \<and> dist a x < r1 \<and> dist a y < r2 }"
    unfolding disk_def Int_def
    by blast
  moreover have "\<not> (\<exists>a. a \<in> V \<and> dist a x < r1 \<and> dist a y < r2 )
   \<Longrightarrow> {a. a \<in> V \<and> dist a x < r1 \<and> dist a y < r2} = {}"
    by blast
  moreover have "\<And>a. a \<in> V \<Longrightarrow> dist a x < r1 \<Longrightarrow> dist a y > dist x y - r1 "
    by (smt (verit) assms(1) assms(2) dist_is_symmetric local.dist_triangle)
  ultimately show "D(x,r1) \<inter> D(y,r2) = {}"
    using assms(4) 
    by force
qed

(*new*)
(*the key conclusion to prove sublocales real_normed_vector_space \<subseteq> t2_space*)
lemma is_hausdorff_rnvs:
"\<And>x y. x \<in> V \<and> y \<in> V \<and> x \<noteq> y
 \<Longrightarrow> \<exists>u v::'a set. is_open_space u \<and> is_open_space v \<and> x \<in> u \<and> y \<in> v \<and> u \<inter> v = {}"
proof-
  fix x y
  assume xv:"x \<in> V \<and> y \<in> V \<and> x \<noteq> y"
  then obtain r1 and r2 where x1:"r1 = dist x y / 2" and y1:"r2 = dist x y / 2"
    by blast
  then obtain u and v where "u = D(x, r1)" and "v = D(y, r2)"
    by blast
  with xv have dx:"is_open_space u \<and> x \<in> u"
    using disk_is_open[of x r1] disk_contains_center[of r1 x] dist_nonzero[of x y]
          dist_nonneg x1 
    by force
  with xv have dy:"is_open_space v \<and> y \<in> v"
    using disk_is_open[of y r2] disk_contains_center[of r2 y] dist_nonzero[of x y]
          dist_nonneg x1
          \<open>u = D(x,r1)\<close> \<open>v = D(y,r2)\<close> y1 
    by fastforce 
  from xv have em:"u \<inter> v = {}"
    using empty_intersection[of x y r1 r2]
    by (simp add: \<open>u = D(x,r1)\<close> \<open>v = D(y,r2)\<close> x1 y1)
  thus "\<exists>u v::'a set. is_open_space u \<and> is_open_space v \<and> x \<in> u \<and> y \<in> v \<and> u \<inter> v = {}"
    using dx dy 
    by blast
qed

    


end (* real_normed_vector_space *)

sublocale real_normed_vector_space \<subseteq> sub: topological_space V "is_open_space"
proof(unfold_locales)
  show"is_open_space V" 
    unfolding is_open_space_def 
    by blast
  show"is_open_space {}" 
    unfolding is_open_space_def 
    by blast
  show"\<And>U. is_open_space U \<Longrightarrow> U \<subseteq> V"
    unfolding is_open_space_def 
    by auto
  show"\<And>S T. is_open_space S \<Longrightarrow> is_open_space T \<Longrightarrow> is_open_space (S \<inter> T)"
    unfolding is_open_space_def 
    by blast
  show"\<And>F. (\<And>x. x \<in> F \<Longrightarrow> is_open_space x) \<Longrightarrow> is_open_space (\<Union>x\<in>F. x) "
    unfolding is_open_space_def 
    by blast
qed

(*new*)
(*we need this sublocale to use dom.Lim and codom.Lim in locale has_derivative*)
sublocale real_normed_vector_space \<subseteq> t2_space V is_open_space
proof(unfold_locales)
  show"sub.is_hausdorff"
    using sub.is_hausdorff_def sub.neighborhoods_def
    by (metis (no_types, lifting) mem_Collect_eq is_hausdorff_rnvs)
qed

      



  
    
 


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
  shows "\<langle>\<zero>,\<zero>\<rangle> = 0" 
proof-
  have "\<langle>\<zero>,\<zero>\<rangle> + \<langle>\<zero>,\<zero>\<rangle> = \<langle>\<zero>,\<zero>\<rangle>" 
    using add_is_linear[of \<zero> \<zero> \<zero>] 
    by auto
  then show"\<langle>\<zero>,\<zero>\<rangle> = 0" 
    by auto
qed

lemma is_positive_semi_definite:
  assumes "x \<in> V"
  shows "\<langle>x,x\<rangle> \<ge> 0"
proof cases
  assume "x = \<zero>"
  with assms show "\<langle>x,x\<rangle> \<ge> 0" 
    using inner_prod_of_zero 
    by auto
next
  assume "x \<noteq> \<zero>"
  with assms show "\<langle>x,x\<rangle> \<ge> 0" 
    using is_pos_definite[of x]  
    by auto
qed

lemma is_definite:
  assumes "x \<in> V"
  shows "\<langle>x,x\<rangle> = 0 \<Longrightarrow> x = \<zero>" 
proof-
  assume "\<langle>x,x\<rangle> = 0"
  then have "x \<noteq> \<zero> \<Longrightarrow> False" 
    using is_pos_definite[of x] assms 
    by auto
  then show "x = \<zero>" 
    by auto
qed


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

definition norm:: "'a \<Rightarrow> real" ("\<parallel>_\<parallel>")
  where "norm u \<equiv> sqrt (\<langle>u,u\<rangle>)"

(* prove that norm is a norm *)
lemma norm_is_nonneg_evs:
  assumes "x \<in> V"
  shows"\<parallel>x\<parallel> \<ge> 0"
proof-
  from assms have "\<langle>x,x\<rangle> \<ge> 0" 
    using is_positive_semi_definite 
    by auto
  thus "\<parallel>x\<parallel> \<ge> 0" 
    using norm_def 
    by auto
qed


lemma norm_is_pos_on_nonzero_evs: (*"x \<in> V \<Longrightarrow> (\<parallel>x\<parallel> = 0 \<longleftrightarrow> x = \<zero>)"*)
  assumes "x \<in> V"
  shows"\<parallel>x\<parallel> = 0 \<longleftrightarrow> x = \<zero>"
proof
  from assms have "\<langle>x,x\<rangle> = 0" if "\<parallel>x\<parallel> = 0" 
    using norm_def that
    by auto
  with assms show "x = \<zero>" if "\<parallel>x\<parallel> = 0" 
    using is_definite[of x] that
    by auto
next
  from assms have "\<langle>x,x\<rangle> = 0" if "x = \<zero>"
    using inner_prod_of_zero that 
    by auto
  thus "\<parallel>x\<parallel> = 0" if "x = \<zero>"
    unfolding norm_def that
    by auto
qed

lemma norm_is_linear_with_abs_evs:(*" x \<in> V \<Longrightarrow> \<parallel>r \<cdot>\<^sub>\<real> x\<parallel> = \<bar>r\<bar> * \<parallel>x\<parallel>"*)
  assumes "x \<in> V"
  shows"\<parallel>r \<cdot>\<^sub>\<real> x\<parallel> = \<bar>r\<bar> * \<parallel>x\<parallel>"
proof-
  from assms have "\<langle>r \<cdot>\<^sub>\<real> x,r \<cdot>\<^sub>\<real> x\<rangle> = r^2 * \<langle>x,x\<rangle>"
    using scale_is_linear is_symmetric scale_closed
    by (auto simp:power2_eq_square)
  thus "\<parallel>r \<cdot>\<^sub>\<real> x\<parallel> = \<bar>r\<bar> * \<parallel>x\<parallel>" 
    unfolding norm_def 
    using assms is_positive_semi_definite 
          scale_closed 
          NthRoot.real_sqrt_abs2 
          NthRoot.real_sqrt_mult 
    by auto
qed

(*lemma delta is important for lemma triangle_mul which plays the key role in 
lemma norm_triangle_eq_holds_evs *)
lemma delta:
  fixes a b c ::real
  assumes"\<And>t . a * t^2 + b * t + c \<ge> 0" and"a \<ge> 0"
  shows"b^2 \<le> 4 * a * c"
proof (cases "a = 0")
  case True
  with assms have lin_nonneg:
  "\<And>t . b * t + c \<ge> 0" 
    by auto
  have "b \<noteq> 0 \<Longrightarrow> \<exists>t . b * t + c < 0"
    by (metis eq_diff_eq 
              le_add_same_cancel2 
              mult.commute 
              nonzero_eq_divide_eq 
              not_le not_one_le_zero)
  with lin_nonneg have "b = 0"
    by (smt (z3))
  with True show "b^2 \<le> 4 * a * c"
    by auto
next
  case False
  with assms(2) have inter1:
    "\<And>t::real. a * (t + b / (2 * a))^2 = a * t^2 + b * t + b^2 / (4 * a)"
    unfolding Power.comm_semiring_1_class.power2_sum 
    using power2_eq_square[of a]
    by (auto simp:field_simps)
  from assms have inter2:
    "\<And>t::real. a * t^2 + b*t + b^2/(4*a) \<ge> b^2 / (4 * a) - c" 
    by (simp add: algebra_simps)
  with inter1 have 
    "\<And>t::real. a * (t + (b::real) / (2 * a))^2 \<ge> b^2 / (4 * a) - c"
    by auto
  hence "b^2 / (4 * a) - c \<le> 0"
    by (metis diff_add_cancel mult_zero_right zero_eq_power2)
  with assms(2) show  "b^2 \<le> 4 * a * c" 
    by (smt (verit, best) 
        False 
        divide_cancel_right 
        divide_right_mono 
        nonzero_mult_div_cancel_left)
qed

    
(*lemma triangle_mul plays the key role in lemma norm_triangle_eq_holds_evs *)
lemma triangle_mul:
  assumes "x \<in> V"" y \<in> V"
  shows "\<langle>x,y\<rangle>^2 \<le>  \<langle>x,x\<rangle> * \<langle>y,y\<rangle>"
proof-
  from assms have "\<And>r::real. \<langle>x + r \<cdot>\<^sub>\<real> y ,x + r \<cdot>\<^sub>\<real> y \<rangle> \<ge> 0"
    using is_positive_semi_definite scale_closed
    by auto
  with assms have 
   "\<And>r::real. 0 \<le> \<langle>y,y\<rangle> * r^2 + 2 * \<langle>x,y\<rangle>*r + \<langle>x,x\<rangle>"
    using scale_is_linear
      and add_is_linear
      and is_symmetric
          scale_closed
          composition_closed
    by (simp add: power2_eq_square field_simps)
  with assms show ?thesis
    using delta[of "\<langle>y,y\<rangle>" "2*\<langle>x,y\<rangle>" "\<langle>x,x\<rangle>"]
          is_positive_semi_definite[of y]
    by (auto simp add: field_simps)
qed

lemma norm_triangle_eq_holds_evs:
  assumes"x \<in> V""y \<in> V"
  shows"\<parallel>x + y\<parallel> \<le> \<parallel>x\<parallel> + \<parallel>y\<parallel>"
proof-
  from assms have "\<langle>x,y\<rangle>^2 \<le>  \<langle>x,x\<rangle> * \<langle>y,y\<rangle>" 
    by (simp add: triangle_mul)
  hence ineq:"\<langle>x,y\<rangle> \<le>  sqrt(\<langle>x,x\<rangle>) * sqrt(\<langle>y,y\<rangle>)" 
    by (metis real_le_rsqrt real_sqrt_mult) 
  from assms have lhs:"\<langle>x + y,x + y\<rangle> = \<langle>x,x\<rangle> + \<langle>y,y\<rangle> + 2 * \<langle>x,y\<rangle>"
    using add_is_linear is_symmetric 
    by auto
  from assms have nonnegx: "\<langle>x,x\<rangle> \<ge> 0"and nonnegy:"\<langle>y,y\<rangle> \<ge> 0"
    using is_positive_semi_definite 
    by auto
  hence nonneg_sqrt:"sqrt \<langle>x,x\<rangle> + sqrt \<langle>y,y\<rangle> \<ge> 0" 
    using Groups.ordered_comm_monoid_add_class.add_nonneg_nonneg
          NthRoot.real_sqrt_ge_0_iff
    by auto
  from nonnegx nonnegy have rhs:"(sqrt \<langle>x,x\<rangle> + sqrt \<langle>y,y\<rangle>)^2 = \<langle>x,x\<rangle> + \<langle>y,y\<rangle> + 2 * sqrt \<langle>x,x\<rangle> * sqrt \<langle>y,y\<rangle>"
    using NthRoot.real_sqrt_pow2_iff
    by (auto simp:Power.comm_semiring_1_class.power2_sum)
  from lhs rhs ineq have "\<langle>x + y,x + y\<rangle> \<le> (sqrt \<langle>x,x\<rangle> + sqrt \<langle>y,y\<rangle>)^2"
    by auto
  with nonneg_sqrt assms show "\<parallel>x + y\<parallel> \<le> \<parallel>x\<parallel> + \<parallel>y\<parallel>"
    unfolding norm_def
    using Power.linordered_semidom_class.power2_le_imp_le[of "sqrt \<langle>x + y,x + y\<rangle>" "sqrt \<langle>x,x\<rangle> +
       sqrt \<langle>y,y\<rangle>"]
          NthRoot.real_sqrt_pow2_iff[of "\<langle>x + y,x + y\<rangle>"]
          is_positive_semi_definite[of "x + y"]
          composition_closed[of x y]
    by auto
qed


definition distance:: "'a \<Rightarrow> 'a \<Rightarrow> real" ("\<d>'(_,_')")
  where "\<d>(u,v) \<equiv> sqrt (\<langle>minus u v , minus u v\<rangle>)"
(* Why the notation for minus from Group_Further_Theory.thy does not work here ? *)
(* prove that dist is a metric, hence prove that an euclidean space is a topological space *)
lemma distance_nonneg_evs:
  assumes "x \<in> V" and "y \<in> V"
  shows"\<d>(x,y) \<ge> 0"
  by (unfold distance_def minus_def,
      simp add:assms is_positive_semi_definite)
  
lemma distance_nonzero_evs:
  assumes "x \<in> V" and "y \<in> V"
  shows" \<d>(x,y) = 0 \<longleftrightarrow> x = y"
proof
  have "minus x y = \<zero>" if "x = y"
    by (simp add: assms(2) minus_def that)
  thus "\<d>(x,y) = 0" if "x = y"
    by (simp add: distance_def inner_prod_of_zero that)
next
  have "minus x y = \<zero>" if "\<d>(x,y) = 0"
    using assms(1) assms(2) distance_def is_definite that
    by (auto simp: composition_closed 
                   invertible 
                   invertible_inverse_closed 
                   norm_is_pos_on_nonzero_evs 
                   minus_def 
                   norm_def) 
   
  thus "x = y" if "\<d>(x,y) = 0"
    by (metis assms 
              inverse_equality  
              invertible 
              invertibleE 
              invertible_right_cancel 
              minus_def 
              that)
    
qed

lemma distance_triangle_evs:
  assumes"x \<in> V" " y \<in> V" "z \<in> V"
  shows"\<d>(x,y) + \<d>(y,z) \<ge> \<d>(x,z)"
proof-
  from assms have "minus x y + minus y z = minus x z"
    by (simp add: associative invertible_left_inverse2 minus_def)
  thus "\<d>(x,y) + \<d>(y,z) \<ge> \<d>(x,z)"
    unfolding distance_def
    using norm_triangle_eq_holds_evs[of "minus x y" "minus y z"]
    by (simp add: assms minus_def norm_def)
qed
  


definition is_open_evs::"'a set \<Rightarrow> bool" where 
"is_open_evs K \<equiv> (K \<subseteq> V) \<and> 
(\<forall>k. k \<in> K \<longrightarrow> (\<exists>r::real . r > 0 \<longrightarrow>(\<forall>z. z \<in> V \<longrightarrow> \<d>(z,k) \<le> r \<longrightarrow> z \<in> K)))"

end (* euclidean_vector_space *)

sublocale euclidean_vector_space \<subseteq> topological_space V "is_open_evs"
proof(unfold_locales)
  show"is_open_evs V" unfolding is_open_evs_def 
    by blast
  show"is_open_evs {}" unfolding is_open_evs_def 
    by blast
  show"\<And>U. is_open_evs U \<Longrightarrow> U \<subseteq> V"
    unfolding is_open_evs_def 
    by auto
  show"\<And>S T. is_open_evs S \<Longrightarrow> is_open_evs T \<Longrightarrow> is_open_evs (S \<inter> T)"
    unfolding is_open_evs_def 
    by blast
  show"\<And>F. (\<And>x. x \<in> F \<Longrightarrow> is_open_evs x) \<Longrightarrow> is_open_evs (\<Union>x\<in>F. x) "
    unfolding is_open_evs_def 
    by blast
qed

sublocale euclidean_vector_space \<subseteq> real_normed_vector_space V "(+)" "\<zero>" "(\<cdot>\<^sub>\<real>)" "norm"
proof(unfold_locales)
  show "\<And>x. x \<in> V \<Longrightarrow> 0 \<le> \<parallel>x\<parallel>"
    by (simp add:is_positive_semi_definite norm_def)
  show"\<And>x. x \<in> V \<Longrightarrow> (\<parallel>x\<parallel> = 0) = (x = \<zero>)"
    by (simp add:norm_is_pos_on_nonzero_evs)
  show"\<And>x r. x \<in> V \<Longrightarrow> \<parallel>r \<cdot>\<^sub>\<real> x\<parallel> =\<bar>r\<bar> * \<parallel>x\<parallel>"
    by (simp add:norm_is_linear_with_abs_evs)
  show"\<And>x y. x \<in> V \<Longrightarrow> y \<in> V \<Longrightarrow> \<parallel>x + y\<parallel> \<le> \<parallel>x\<parallel> + \<parallel>y\<parallel>"
    by (simp add:norm_triangle_eq_holds_evs)
qed

(*new*)
locale has_derivative = 

dom: real_normed_vector_space V add zero scale norm +

codom: real_normed_vector_space V' add' zero' scale' norm' +

map f V V' + map f' V V'

for V and add(infixl "+" 70)and  zero("\<zero>") and scale(infixr "\<cdot>\<^sub>\<real>" 75) and norm("\<parallel>_\<parallel>") 
and V' and add'(infixl "+''" 70)and zero'("\<zero>''") and scale'(infixr "\<cdot>\<^sub>\<real>''" 75) and norm'("\<parallel>_\<parallel>''") 
and f and f'+

fixes F:: "'a filter" 

and codom_divide:: "'b \<Rightarrow> real \<Rightarrow> 'b"  (infixl "'/\<^sub>R" 75)

and dom_minus::"'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "-" 70)

and codom_minus::"'b \<Rightarrow> 'b \<Rightarrow> 'b" (infixl "-''" 70)

and dom_lim::"'a filter \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> 'a"("Lim\<^sub>d")

and codom_lim::"'a filter \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'b"("Lim\<^sub>c")

assumes is_bounded_linear: "bounded_linear_map V add zero scale norm V' add' zero' scale' norm' f'"

and dom_minus_def:"x - y \<equiv> dom.minus x y"

and codom_minus_def:"a -' b \<equiv> codom.minus a b"

and codom_divide_def:"a /\<^sub>R r \<equiv> codom.divide a r"

(*In order to introduce the notation in the statement of this locale, the author uses the trick here
to combine "dom_minus" and "dom_minus_def" so that any notations in the formula like "-" will not 
cause the type errors when compiling*)

and has_derivative_hd:

"let k = Lim\<^sub>d F (\<lambda>x\<in>V. x) in

Lim\<^sub>c F (\<lambda>y\<in>V. (f y -' f k -' f'(y - k)) /\<^sub>R  \<parallel>y - k\<parallel>) = zero'"

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

