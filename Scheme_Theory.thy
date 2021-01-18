theory Scheme_Theory
imports "Comm_Ring_Theory"

begin

section \<open>Affine Schemes\<close>

text \<open>Computational affine schemes take the isomorphism with Spec as part of their data,
while in the locale for affine schemes we merely assert the existence of such an isomorphism.\<close> 

locale comp_affine_scheme = comm_ring +
iso_locally_ringed_spaces X is_open \<O>\<^sub>X \<rho> b add_str mult_str zero_str one_str
"Spec" is_zariski_open sheaf_spec sheaf_spec_morphisms \<O>b "\<lambda>U. add_sheaf_spec U"
"\<lambda>U. mult_sheaf_spec U" "\<lambda>U. zero_sheaf_spec U" "\<lambda>U. one_sheaf_spec U" f \<phi>\<^sub>f
for X is_open \<O>\<^sub>X \<rho> b add_str mult_str zero_str one_str f \<phi>\<^sub>f

(* definition 0.46 *)
locale affine_scheme = locally_ringed_space + comm_ring +
  assumes is_iso_to_spec: "\<exists>f \<phi>\<^sub>f. iso_locally_ringed_spaces X is_open \<O>\<^sub>X \<rho> b add_str mult_str zero_str one_str
Spec is_zariski_open sheaf_spec sheaf_spec_morphisms \<O>b (\<lambda>U. add_sheaf_spec U)
(\<lambda>U. mult_sheaf_spec U) (\<lambda>U. zero_sheaf_spec U) (\<lambda>U. one_sheaf_spec U) f \<phi>\<^sub>f"

sublocale comp_affine_scheme \<subseteq> affine_scheme sorry

section \<open>Schemes\<close>

(* def. 0.47 *)
locale scheme = locally_ringed_space + comm_ring +
  assumes are_affine_schemes: "\<And>x. x \<in> X \<Longrightarrow> (\<exists>U. x\<in>U \<and> is_open U \<and> 
affine_scheme U (ind_topology.ind_is_open X is_open U) (cxt_ind_sheaf.ind_sheaf \<O>\<^sub>X U) 
(cxt_ind_sheaf.ind_ring_morphisms \<rho> U) b (cxt_ind_sheaf.ind_add_str add_str U)
(cxt_ind_sheaf.ind_mult_str mult_str U) (cxt_ind_sheaf.ind_zero_str zero_str U)
(cxt_ind_sheaf.ind_one_str one_str U) R (+) (\<cdot>) \<zero> \<one>)"

context comp_affine_scheme
begin

interpretation pr: presheaf_of_rings X is_open \<O>\<^sub>X \<rho> b add_str mult_str zero_str one_str
  by (simp add: dom.presheaf_of_rings_axioms)

interpretation cis:cxt_ind_sheaf X is_open "\<O>\<^sub>X" \<rho> b add_str mult_str zero_str one_str X
  by (simp add: cxt_ind_sheaf_axioms_def cxt_ind_sheaf_def dom.sheaf_of_rings_axioms)

interpretation it: ind_topology X is_open X by simp

interpretation pr': presheaf_of_rings X it.ind_is_open cis.ind_sheaf cis.ind_ring_morphisms b 
cis.ind_add_str cis.ind_mult_str cis.ind_zero_str cis.ind_one_str
  using cis.ind_sheaf_is_presheaf by simp

interpretation sh: sheaf_of_rings X is_open \<O>\<^sub>X \<rho> b add_str mult_str zero_str one_str
  by (simp add: dom.sheaf_of_rings_axioms)

interpretation sh': sheaf_of_rings X it.ind_is_open cis.ind_sheaf cis.ind_ring_morphisms b 
cis.ind_add_str cis.ind_mult_str cis.ind_zero_str cis.ind_one_str
  using cis.ind_sheaf_is_sheaf by blast

interpretation rs': ringed_space X it.ind_is_open cis.ind_sheaf cis.ind_ring_morphisms b 
cis.ind_add_str cis.ind_mult_str cis.ind_zero_str cis.ind_one_str
  by (simp add: pr'.topological_space_axioms ringed_space.intro sh'.sheaf_of_rings_axioms)

interpretation dims: cxt_direct_im_sheaf X is_open Spec is_zariski_open f \<O>\<^sub>X \<rho> b add_str mult_str zero_str one_str
  by (simp add: cxt_direct_im_sheaf_def dom.sheaf_of_rings_axioms is_continuous)

interpretation dims': cxt_direct_im_sheaf X it.ind_is_open Spec is_zariski_open f cis.ind_sheaf 
cis.ind_ring_morphisms b cis.ind_add_str cis.ind_mult_str cis.ind_zero_str cis.ind_one_str
  by (simp add: continuous_map_axioms_def continuous_map_def cxt_direct_im_sheaf.intro dims.is_continuous dims.map_axioms dom.ind_is_open_iff_open pr'.topological_space_axioms sh'.sheaf_of_rings_axioms)

lemma eq_ind_is_open:
  shows "\<And>U. is_open U = it.ind_is_open U"
  using dom.ind_is_open_iff_open dom.open_imp_subset by auto

lemma eq_ind_sheaf:
  shows "\<And>V. V \<subseteq> X \<Longrightarrow> \<O>\<^sub>X V = cis.ind_sheaf V" 
  using cxt_ind_sheaf.ind_sheaf_def
  by (simp add: Int_absorb1 cis.ind_sheaf_def)

lemma eq_ind_ring_morphisms:
  shows "\<And>V W. V \<subseteq> X \<Longrightarrow> W \<subseteq> X \<Longrightarrow> \<rho> V W = cis.ind_ring_morphisms V W"
  by (simp add: Int_absorb1 cis.ind_ring_morphisms_def)

lemma eq_ind_add_str:
  shows "\<And>V. V \<subseteq> X \<Longrightarrow> add_str V = cis.ind_add_str V" 
  using cis.ind_add_str_def by (simp add: inf.absorb_iff2)

lemma eq_ind_mult_str:
  shows "\<And>V. V \<subseteq> X \<Longrightarrow> mult_str V = cis.ind_mult_str V" 
  using cis.ind_mult_str_def by (simp add: inf.absorb_iff2)

lemma eq_ind_zero_str:
  shows "\<And>V. V \<subseteq> X \<Longrightarrow> zero_str V = cis.ind_zero_str V" 
  using cis.ind_zero_str_def by (simp add: inf.absorb_iff2)

lemma eq_ind_one_str:
  shows "\<And>V. V \<subseteq> X \<Longrightarrow> one_str V = cis.ind_one_str V" 
  using cis.ind_one_str_def by (simp add: inf.absorb_iff2)

lemma eq_neighborhoods:
  shows "\<And>x U. (U \<in> {U. is_open U \<and> x \<in> U}) = (U \<in> pr'.neighborhoods x)" 
  using eq_ind_is_open pr'.neighborhoods_def by simp

lemma eq_stalk:
  assumes "x \<in> X"
  shows "stalk_at x = pr'.stalk_at x"
  sorry

lemma eq_add_stalk:
  assumes "x \<in> X"
  shows "add_stalk_at x = pr'.add_stalk_at x"
  sorry

lemma eq_mult_stalk:
  assumes "x \<in> X"
  shows "mult_stalk_at x = pr'.mult_stalk_at x"
  sorry

lemma eq_zero_stalk:
  assumes "it.ind_is_open V" and "x \<in> V"
  shows "zero_stalk_at x V = pr'.zero_stalk_at x V"
  sorry

lemma eq_one_stalk:
  assumes "it.ind_is_open V" and "x \<in> V"
  shows "one_stalk_at x V = pr'.one_stalk_at x V"
  sorry

lemma eq_direct_im_sheaf:
  shows "\<And>V. \<O>\<^sub>X(f\<^sup>\<inverse> X V) = cis.ind_sheaf (f\<^sup>\<inverse> X V)"
  sorry

lemma eq_direct_im_sheaf_morphisms:
  shows "\<And>U V. \<rho> (f\<^sup>\<inverse> X U) (f\<^sup>\<inverse> X V) = cis.ind_ring_morphisms (f\<^sup>\<inverse> X U) (f\<^sup>\<inverse> X V)"
  sorry

lemma eq_direct_im_add_str:
  shows "\<And>V x y. add_str (f\<^sup>\<inverse> X V) x y = cis.ind_add_str (f\<^sup>\<inverse> X V) x y"
  sorry

lemma eq_direct_im_mult_str:
  shows "\<And>V x y. mult_str (f\<^sup>\<inverse> X V) x y = cis.ind_mult_str (f\<^sup>\<inverse> X V) x y"
  sorry

lemma eq_direct_im_zero_str:
  shows "\<And>V. zero_str (f\<^sup>\<inverse> X V) = cis.ind_zero_str (f\<^sup>\<inverse> X V)"
  sorry

lemma eq_direct_im_one_str:
  shows "\<And>V. one_str (f\<^sup>\<inverse> X V) = cis.ind_one_str (f\<^sup>\<inverse> X V)"
  sorry

lemma eq_im_sheaf:
  shows "\<And>U. is_zariski_open U \<Longrightarrow> 
dims.direct_im_sheaf U = dims'.direct_im_sheaf U"
  sorry

lemma affine_scheme_lrs_axioms:
  shows "locally_ringed_space_axioms it.ind_is_open cis.ind_sheaf cis.ind_ring_morphisms
     cis.ind_add_str cis.ind_mult_str cis.ind_zero_str cis.ind_one_str"
  by (smt comp_affine_scheme.eq_zero_stalk comp_affine_scheme_axioms dom.open_space eq_mult_stalk eq_stalk in_mono is_local_ring it.is_open_from_ind_is_open locally_ringed_space_axioms_def pr'.open_imp_subset)

interpretation lrs': locally_ringed_space X it.ind_is_open cis.ind_sheaf cis.ind_ring_morphisms b 
cis.ind_add_str cis.ind_mult_str cis.ind_zero_str cis.ind_one_str
  by (simp add: affine_scheme_lrs_axioms locally_ringed_space.intro rs'.ringed_space_axioms)

lemma affine_scheme_as_axioms:
  shows "affine_scheme_axioms X it.ind_is_open cis.ind_sheaf cis.ind_ring_morphisms b cis.ind_add_str
     cis.ind_mult_str cis.ind_zero_str cis.ind_one_str R (+) (\<cdot>) \<zero> \<one>"
proof-
  have "iso_locally_ringed_spaces X it.ind_is_open cis.ind_sheaf cis.ind_ring_morphisms b
        cis.ind_add_str cis.ind_mult_str cis.ind_zero_str cis.ind_one_str Spec is_zariski_open
        sheaf_spec sheaf_spec_morphisms \<O>b add_sheaf_spec mult_sheaf_spec zero_sheaf_spec
        one_sheaf_spec f \<phi>\<^sub>f"
  proof(intro_locales)
    show "morphism_ringed_spaces_axioms X it.ind_is_open cis.ind_sheaf cis.ind_ring_morphisms b
     cis.ind_add_str cis.ind_mult_str cis.ind_zero_str cis.ind_one_str Spec is_zariski_open
     sheaf_spec sheaf_spec_morphisms \<O>b add_sheaf_spec mult_sheaf_spec zero_sheaf_spec
     one_sheaf_spec f \<phi>\<^sub>f"
    proof (intro morphism_ringed_spaces_axioms.intro)
      show "continuous_map X it.ind_is_open Spec is_zariski_open f"
        by (simp add: dims'.continuous_map_axioms)
    next
      show "morphism_sheaves_of_rings Spec is_zariski_open sheaf_spec sheaf_spec_morphisms \<O>b
     add_sheaf_spec mult_sheaf_spec zero_sheaf_spec one_sheaf_spec
     (cxt_direct_im_sheaf.direct_im_sheaf X f cis.ind_sheaf)
     (cxt_direct_im_sheaf.direct_im_sheaf_morphisms X f cis.ind_ring_morphisms) b
     (\<lambda>V. cis.ind_add_str (f \<^sup>\<inverse> X V)) (\<lambda>V. cis.ind_mult_str (f \<^sup>\<inverse> X V))
     (\<lambda>V. cis.ind_zero_str (f \<^sup>\<inverse> X V)) (\<lambda>V. cis.ind_one_str (f \<^sup>\<inverse> X V)) \<phi>\<^sub>f"
      proof(intro_locales)
        show "presheaf_of_rings_axioms is_zariski_open dims'.direct_im_sheaf dims'.direct_im_sheaf_morphisms
     b (\<lambda>V. cis.ind_add_str (f \<^sup>\<inverse> X V)) (\<lambda>V. cis.ind_mult_str (f \<^sup>\<inverse> X V))
     (\<lambda>V. cis.ind_zero_str (f \<^sup>\<inverse> X V)) (\<lambda>V. cis.ind_one_str (f \<^sup>\<inverse> X V))"
          using dims'.direct_im_sheaf_is_presheaf presheaf_of_rings_def by fastforce
      next
        show "morphism_presheaves_of_rings_axioms is_zariski_open sheaf_spec sheaf_spec_morphisms
     add_sheaf_spec mult_sheaf_spec zero_sheaf_spec one_sheaf_spec dims'.direct_im_sheaf
     dims'.direct_im_sheaf_morphisms (\<lambda>V. cis.ind_add_str (f \<^sup>\<inverse> X V))
     (\<lambda>V. cis.ind_mult_str (f \<^sup>\<inverse> X V)) (\<lambda>V. cis.ind_zero_str (f \<^sup>\<inverse> X V))
     (\<lambda>V. cis.ind_one_str (f \<^sup>\<inverse> X V)) \<phi>\<^sub>f"
        proof-
        have "morphism_presheaves_of_rings_axioms is_zariski_open sheaf_spec sheaf_spec_morphisms
     add_sheaf_spec mult_sheaf_spec zero_sheaf_spec one_sheaf_spec
     dims.direct_im_sheaf dims.direct_im_sheaf_morphisms (\<lambda>V. add_str (f \<^sup>\<inverse> X V)) (\<lambda>V. mult_str (f \<^sup>\<inverse> X V))
     (\<lambda>V. zero_str (f \<^sup>\<inverse> X V)) (\<lambda>V. one_str (f \<^sup>\<inverse> X V)) \<phi>\<^sub>f"
          using is_morphism_of_sheaves morphism_presheaves_of_rings_def morphism_sheaves_of_rings_def by fastforce
        thus ?thesis
          by (simp add: dims'.direct_im_sheaf_def dims'.direct_im_sheaf_morphisms_def dims.direct_im_sheaf_def dims.direct_im_sheaf_morphisms_def eq_direct_im_one_str eq_direct_im_sheaf eq_direct_im_sheaf_morphisms eq_direct_im_zero_str eq_ind_add_str eq_ind_mult_str morphism_presheaves_of_rings_axioms_def)
      qed
    qed
  qed
next
  show "morphism_locally_ringed_spaces_axioms X it.ind_is_open cis.ind_sheaf cis.ind_ring_morphisms
     cis.ind_add_str cis.ind_mult_str cis.ind_zero_str cis.ind_one_str is_zariski_open sheaf_spec
     sheaf_spec_morphisms add_sheaf_spec mult_sheaf_spec zero_sheaf_spec one_sheaf_spec f \<phi>\<^sub>f"
    sorry
next
  show "iso_locally_ringed_spaces_axioms X it.ind_is_open cis.ind_sheaf cis.ind_ring_morphisms b
     cis.ind_add_str cis.ind_mult_str cis.ind_zero_str cis.ind_one_str Spec is_zariski_open
     sheaf_spec sheaf_spec_morphisms \<O>b add_sheaf_spec mult_sheaf_spec zero_sheaf_spec
     one_sheaf_spec f \<phi>\<^sub>f"
    sorry
qed
  thus ?thesis by (meson affine_scheme_axioms_def)
qed
      
lemma comp_affine_scheme_is_scheme:
  shows "scheme X is_open \<O>\<^sub>X \<rho> b add_str mult_str zero_str one_str R (+) (\<cdot>) \<zero> \<one>"
proof (intro scheme.intro scheme_axioms.intro)
  show "locally_ringed_space X is_open \<O>\<^sub>X \<rho> b add_str mult_str zero_str one_str" by (simp add: locally_ringed_space_axioms)
next
  show "comm_ring R (+) (\<cdot>) \<zero> \<one>" by (simp add: local.comm_ring_axioms)
next
  show "\<And>x. x \<in> X \<Longrightarrow>
         \<exists>U. x \<in> U \<and> is_open U \<and>
             affine_scheme U (ind_topology.ind_is_open X is_open U)
              (cxt_ind_sheaf.ind_sheaf \<O>\<^sub>X U) (cxt_ind_sheaf.ind_ring_morphisms \<rho> U) b
              (cxt_ind_sheaf.ind_add_str add_str U) (cxt_ind_sheaf.ind_mult_str mult_str U)
              (cxt_ind_sheaf.ind_zero_str zero_str U) (cxt_ind_sheaf.ind_one_str one_str U) R (+)
              (\<cdot>) \<zero> \<one>"
    by (meson affine_scheme_as_axioms affine_scheme_def dom.open_space local.comm_ring_axioms lrs'.locally_ringed_space_axioms)
qed

end (* comp_affine_scheme *)

lemma (in affine_scheme) affine_scheme_is_scheme:
  shows "scheme X is_open \<O>\<^sub>X \<rho> b add_str mult_str zero_str one_str R (+) (\<cdot>) \<zero> \<one>"
proof-
  obtain f \<phi>\<^sub>f where "iso_locally_ringed_spaces X is_open \<O>\<^sub>X \<rho> b add_str mult_str zero_str one_str
Spec is_zariski_open sheaf_spec sheaf_spec_morphisms \<O>b (\<lambda>U. add_sheaf_spec U)
(\<lambda>U. mult_sheaf_spec U) (\<lambda>U. zero_sheaf_spec U) (\<lambda>U. one_sheaf_spec U) f \<phi>\<^sub>f"
    using is_iso_to_spec by auto
  hence "comp_affine_scheme R (+) (\<cdot>) \<zero> \<one> X is_open \<O>\<^sub>X \<rho> b add_str mult_str zero_str one_str f \<phi>\<^sub>f"
    by (simp add: comp_affine_scheme_def local.comm_ring_axioms)
  thus ?thesis using comp_affine_scheme.comp_affine_scheme_is_scheme by fastforce
qed


lemma (in comm_ring) spec_is_comp_affine_scheme:
  shows "comp_affine_scheme R (+) (\<cdot>) \<zero> \<one> Spec is_zariski_open sheaf_spec sheaf_spec_morphisms \<O>b
(\<lambda>U. add_sheaf_spec U) (\<lambda>U. mult_sheaf_spec U) (\<lambda>U. zero_sheaf_spec U) (\<lambda>U. one_sheaf_spec U)
(identity Spec) (\<lambda>U. identity (\<O> U))"
proof (intro comp_affine_scheme.intro)
  show "comm_ring R (+) (\<cdot>) \<zero> \<one>" by (simp add: local.comm_ring_axioms)
next
  show "iso_locally_ringed_spaces Spec is_zariski_open sheaf_spec sheaf_spec_morphisms \<O>b
     add_sheaf_spec mult_sheaf_spec zero_sheaf_spec one_sheaf_spec Spec is_zariski_open sheaf_spec
     sheaf_spec_morphisms \<O>b add_sheaf_spec mult_sheaf_spec zero_sheaf_spec one_sheaf_spec
     (identity Spec) (\<lambda>U. identity (\<O> U))"
  proof-
    have "homeomorphism Spec is_zariski_open Spec is_zariski_open (identity Spec)" sorry
    moreover have "iso_sheaves_of_rings
Spec is_zariski_open sheaf_spec sheaf_spec_morphisms \<O>b add_sheaf_spec mult_sheaf_spec zero_sheaf_spec one_sheaf_spec
(cxt_direct_im_sheaf.direct_im_sheaf Spec (identity Spec) sheaf_spec)
(cxt_direct_im_sheaf.direct_im_sheaf_morphisms Spec (identity Spec) sheaf_spec_morphisms)
\<O>b
(\<lambda>V x y. add_sheaf_spec ((identity Spec)\<^sup>\<inverse> Spec V) x y) 
(\<lambda>V x y. mult_sheaf_spec ((identity Spec)\<^sup>\<inverse> Spec V) x y) 
(\<lambda>V. zero_sheaf_spec ((identity Spec)\<^sup>\<inverse> Spec V)) 
(\<lambda>V. one_sheaf_spec ((identity Spec)\<^sup>\<inverse> Spec V))
(\<lambda>U. identity (\<O> U))"
      sorry
    moreover have "morphism_locally_ringed_spaces
Spec is_zariski_open sheaf_spec sheaf_spec_morphisms \<O>b add_sheaf_spec mult_sheaf_spec zero_sheaf_spec one_sheaf_spec
Spec is_zariski_open sheaf_spec sheaf_spec_morphisms \<O>b add_sheaf_spec mult_sheaf_spec zero_sheaf_spec one_sheaf_spec
(identity Spec)
(\<lambda>U. identity (\<O> U))" sorry
    ultimately show ?thesis using iso_locally_ringed_spaces_def sorry
  qed
qed

lemma (in comm_ring) spec_is_scheme:
  shows "scheme Spec is_zariski_open sheaf_spec sheaf_spec_morphisms \<O>b
(\<lambda>U. add_sheaf_spec U) (\<lambda>U. mult_sheaf_spec U) (\<lambda>U. zero_sheaf_spec U) (\<lambda>U. one_sheaf_spec U)
R (+) (\<cdot>) \<zero> \<one>"
  using spec_is_comp_affine_scheme affine_scheme.affine_scheme_is_scheme sorry

lemma empty_scheme_is_comp_affine_scheme:
  shows "comp_affine_scheme {0::nat} (\<lambda>x y. 0) (\<lambda>x y. 0) 0 0 
{} (\<lambda>U. True) (\<lambda>U. {0}) (\<lambda>U V. id) 0 (\<lambda>U x y. 0) (\<lambda>U x y. 0) (\<lambda>U. 0) (\<lambda>U. 0)
(\<lambda>\<pp>\<in>Spec. undefined) (\<lambda>U.\<lambda>s\<in>(\<O> U). 0)"
  sorry

lemma empty_scheme_is_scheme:
  shows "scheme {} (\<lambda>U. True) (\<lambda>U. {0}) (\<lambda>U V. id) 0 (\<lambda>U x y. 0) (\<lambda>U x y. 0) (\<lambda>U. 0) (\<lambda>U. 0)
{0::nat} (\<lambda>x y. 0) (\<lambda>x y. 0) 0 0"
  using affine_scheme.affine_scheme_is_scheme empty_scheme_is_comp_affine_scheme sorry

end