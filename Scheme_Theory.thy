theory Scheme_Theory
imports "Comm_Ring_Theory"

begin


section \<open>Affine Schemes\<close>

text \<open>Computational affine schemes take the isomorphism with Spec as part of their data,
while in the locale for affine schemes we merely assert the existence of such an isomorphism.\<close> 

locale comp_affine_scheme = comm_ring +
locally_ringed_space X is_open \<O>\<^sub>X \<rho> b add_str mult_str zero_str one_str +
iso_locally_ringed_spaces X is_open \<O>\<^sub>X \<rho> b add_str mult_str zero_str one_str
"Spec" is_zariski_open sheaf_spec sheaf_spec_morphisms \<O>b "\<lambda>U. add_sheaf_spec U"
"\<lambda>U. mult_sheaf_spec U" "\<lambda>U. zero_sheaf_spec U" "\<lambda>U. one_sheaf_spec U" f \<phi>\<^sub>f
for X is_open \<O>\<^sub>X \<rho> b add_str mult_str zero_str one_str f \<phi>\<^sub>f

(* definition 0.46 *)
locale affine_scheme = comm_ring + 
locally_ringed_space X is_open \<O>\<^sub>X \<rho> b add_str mult_str zero_str one_str 
for X is_open \<O>\<^sub>X \<rho> b add_str mult_str zero_str one_str +
  assumes is_iso_to_spec: "\<exists>f \<phi>\<^sub>f. iso_locally_ringed_spaces X is_open \<O>\<^sub>X \<rho> b add_str mult_str zero_str one_str
Spec is_zariski_open sheaf_spec sheaf_spec_morphisms \<O>b (\<lambda>U. add_sheaf_spec U)
(\<lambda>U. mult_sheaf_spec U) (\<lambda>U. zero_sheaf_spec U) (\<lambda>U. one_sheaf_spec U) f \<phi>\<^sub>f"

sublocale comp_affine_scheme \<subseteq> affine_scheme
proof
  obtain f \<phi>\<^sub>f where "iso_locally_ringed_spaces X is_open \<O>\<^sub>X \<rho> b add_str mult_str zero_str one_str Spec is_zariski_open sheaf_spec
        sheaf_spec_morphisms \<O>b add_sheaf_spec mult_sheaf_spec zero_sheaf_spec one_sheaf_spec f \<phi>\<^sub>f"
    using iso_locally_ringed_spaces_axioms by auto
  show "\<exists>f \<phi>\<^sub>f.
       iso_locally_ringed_spaces X is_open \<O>\<^sub>X \<rho> b add_str mult_str zero_str one_str Spec is_zariski_open sheaf_spec
        sheaf_spec_morphisms \<O>b add_sheaf_spec mult_sheaf_spec zero_sheaf_spec one_sheaf_spec f \<phi>\<^sub>f"
    using iso_locally_ringed_spaces_axioms by auto
qed


section \<open>Schemes\<close>

(* def. 0.47 *)
locale scheme = comm_ring + 
locally_ringed_space X is_open \<O>\<^sub>X \<rho> b add_str mult_str zero_str one_str 
for X is_open \<O>\<^sub>X \<rho> b add_str mult_str zero_str one_str +
  assumes are_affine_schemes: "\<And>x. x \<in> X \<Longrightarrow> (\<exists>U. x\<in>U \<and> is_open U \<and> 
affine_scheme  R (+) (\<cdot>) \<zero> \<one> U (ind_topology.ind_is_open X is_open U) (ind_sheaf.ind_sheaf \<O>\<^sub>X U) 
(ind_sheaf.ind_ring_morphisms \<rho> U) b (ind_sheaf.ind_add_str add_str U)
(ind_sheaf.ind_mult_str mult_str U) (ind_sheaf.ind_zero_str zero_str U)
(ind_sheaf.ind_one_str one_str U))"

context comp_affine_scheme
begin

(* interpretation pr: presheaf_of_rings X is_open \<O>\<^sub>X \<rho> b add_str mult_str zero_str one_str
  by (simp add: dom.presheaf_of_rings_axioms)

interpretation cis:ind_sheaf X is_open "\<O>\<^sub>X" \<rho> b add_str mult_str zero_str one_str X
  by (simp add: ind_sheaf_axioms_def ind_sheaf_def sheaf_of_rings_axioms)

interpretation it: ind_topology X is_open X by simp

interpretation pr': presheaf_of_rings X it.ind_is_open cis.ind_sheaf cis.ind_ring_morphisms b 
cis.ind_add_str cis.ind_mult_str cis.ind_zero_str cis.ind_one_str
  using cis.ind_sheaf_is_presheaf by simp

interpretation sh: sheaf_of_rings X is_open \<O>\<^sub>X \<rho> b add_str mult_str zero_str one_str
  by (simp add: sheaf_of_rings_axioms)

interpretation sh': sheaf_of_rings X it.ind_is_open cis.ind_sheaf cis.ind_ring_morphisms b 
cis.ind_add_str cis.ind_mult_str cis.ind_zero_str cis.ind_one_str
  using cis.ind_sheaf_is_sheaf by blast

interpretation rsspec: ringed_space Spec is_zariski_open sheaf_spec sheaf_spec_morphisms \<O>b 
add_sheaf_spec mult_sheaf_spec zero_sheaf_spec one_sheaf_spec
  using spec_is_ringed_space by simp

interpretation rs: ringed_space X is_open \<O>\<^sub>X \<rho> b add_str mult_str zero_str one_str
  by (simp add: ringed_space_def sheaf_of_rings_axioms)

interpretation rs': ringed_space X it.ind_is_open cis.ind_sheaf cis.ind_ring_morphisms b 
cis.ind_add_str cis.ind_mult_str cis.ind_zero_str cis.ind_one_str
  by (simp add: pr'.topological_space_axioms ringed_space.intro sh'.sheaf_of_rings_axioms)

interpretation dims: im_sheaf X is_open Spec is_zariski_open f \<O>\<^sub>X \<rho> b add_str mult_str zero_str one_str
  by (simp add: im_sheaf_def dom.sheaf_of_rings_axioms is_continuous)

interpretation dims': im_sheaf X it.ind_is_open Spec is_zariski_open f cis.ind_sheaf 
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
  shows "presheaf_of_rings.stalk_at is_open \<O>\<^sub>X \<rho> x = pr'.stalk_at x"
  sorry

lemma eq_add_stalk:
  assumes "x \<in> X"
  shows "presheaf_of_rings.add_stalk_at is_open \<O>\<^sub>X \<rho> add_str x = pr'.add_stalk_at x"
  sorry

lemma eq_mult_stalk:
  assumes "x \<in> X"
  shows "presheaf_of_rings.mult_stalk_at is_open \<O>\<^sub>X \<rho> mult_str x = pr'.mult_stalk_at x"
  sorry

lemma eq_zero_stalk:
  assumes "it.ind_is_open V" and "x \<in> V"
  shows "presheaf_of_rings.zero_stalk_at is_open \<O>\<^sub>X \<rho> zero_str x V = pr'.zero_stalk_at x V"
  sorry

lemma eq_one_stalk:
  assumes "it.ind_is_open V" and "x \<in> V"
  shows "presheaf_of_rings.one_stalk_at is_open \<O>\<^sub>X \<rho> one_str x V = pr'.one_stalk_at x V"
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

lemma eq_ind_morphism_btw_stalks:
  assumes "x \<in> X" (* may need other assumptions as well *)
  shows "\<phi>\<^bsub>X is_open \<O>\<^sub>X \<rho> f \<phi>\<^sub>f x\<^esub> = \<phi>\<^bsub>X it.ind_is_open cis.ind_sheaf cis.ind_ring_morphisms f \<phi>\<^sub>f x\<^esub>"
  sorry

lemma affine_scheme_lrs_axioms:
  shows "locally_ringed_space_axioms it.ind_is_open cis.ind_sheaf cis.ind_ring_morphisms
     cis.ind_add_str cis.ind_mult_str cis.ind_zero_str cis.ind_one_str"
  by (smt comp_affine_scheme.eq_add_stalk comp_affine_scheme.eq_mult_stalk comp_affine_scheme.eq_stalk comp_affine_scheme_axioms dom.open_space eq_one_stalk eq_zero_stalk in_mono is_local_ring it.is_open_from_ind_is_open locally_ringed_space_axioms_def pr'.open_imp_subset)

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
    show G1:"morphism_ringed_spaces_axioms X it.ind_is_open cis.ind_sheaf cis.ind_ring_morphisms b
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
  show "morphism_locally_ringed_spaces_axioms X it.ind_is_open cis.ind_sheaf cis.ind_ring_morphisms
     cis.ind_add_str cis.ind_mult_str cis.ind_zero_str cis.ind_one_str is_zariski_open sheaf_spec
     sheaf_spec_morphisms add_sheaf_spec mult_sheaf_spec zero_sheaf_spec one_sheaf_spec f \<phi>\<^sub>f"
  proof-
     interpret mrs: morphism_ringed_spaces X it.ind_is_open cis.ind_sheaf cis.ind_ring_morphisms b
     cis.ind_add_str cis.ind_mult_str cis.ind_zero_str cis.ind_one_str Spec is_zariski_open sheaf_spec
     sheaf_spec_morphisms \<O>b add_sheaf_spec mult_sheaf_spec zero_sheaf_spec one_sheaf_spec f \<phi>\<^sub>f
      using G1 by (simp add: morphism_ringed_spaces_def rs'.ringed_space_axioms spec_is_ringed_space)
    show "morphism_locally_ringed_spaces_axioms X it.ind_is_open cis.ind_sheaf cis.ind_ring_morphisms
     cis.ind_add_str cis.ind_mult_str cis.ind_zero_str cis.ind_one_str is_zariski_open sheaf_spec
     sheaf_spec_morphisms add_sheaf_spec mult_sheaf_spec zero_sheaf_spec one_sheaf_spec f \<phi>\<^sub>f"
    proof(intro morphism_locally_ringed_spaces_axioms.intro)
      fix x V assume "x \<in> X" "is_zariski_open V" "f x \<in> V"
      interpret lrg: local_ring "codom.stalk_at (f x)" "codom.add_stalk_at (f x)" "codom.mult_stalk_at (f x)" "codom.zero_stalk_at (f x) V" "codom.one_stalk_at (f x) V"
        using \<open>f x \<in> V\<close> \<open>is_zariski_open V\<close> spec_is_locally_ringed_space
        by (simp add: locally_ringed_space_axioms_def locally_ringed_space_def)
      interpret lrgcodom: local_ring "dom.stalk_at x" "dom.add_stalk_at x" "dom.mult_stalk_at x" "dom.zero_stalk_at x (f\<^sup>\<inverse> X V)" "dom.one_stalk_at x (f\<^sup>\<inverse> X V)"
        by (meson \<open>f x \<in> V\<close> \<open>is_zariski_open V\<close> \<open>x \<in> X\<close> is_local_morphism local_ring_morphism_def)
      have "local_ring_morphism \<phi>\<^bsub>X is_open \<O>\<^sub>X \<rho> f \<phi>\<^sub>f x\<^esub>
            (codom.stalk_at (f x)) (codom.add_stalk_at (f x)) (codom.mult_stalk_at (f x)) (codom.zero_stalk_at (f x) V) (codom.one_stalk_at (f x) V) 
(presheaf_of_rings.stalk_at is_open \<O>\<^sub>X \<rho> x) (presheaf_of_rings.add_stalk_at is_open \<O>\<^sub>X \<rho> add_str x) 
(presheaf_of_rings.mult_stalk_at is_open \<O>\<^sub>X \<rho> mult_str x) (presheaf_of_rings.zero_stalk_at is_open \<O>\<^sub>X \<rho> zero_str x (f \<^sup>\<inverse> X V))
(presheaf_of_rings.one_stalk_at is_open \<O>\<^sub>X \<rho> one_str x (f \<^sup>\<inverse> X V))"
        by (simp add: \<open>f x \<in> V\<close> \<open>is_zariski_open V\<close> \<open>x \<in> X\<close> is_local_morphism)
      thus "local_ring_morphism \<phi>\<^bsub>X it.ind_is_open cis.ind_sheaf cis.ind_ring_morphisms f \<phi>\<^sub>f x\<^esub>
            (codom.stalk_at (f x)) (codom.add_stalk_at (f x)) (codom.mult_stalk_at (f x))
            (codom.zero_stalk_at (f x) V) (codom.one_stalk_at (f x) V) (pr'.stalk_at x)
            (pr'.add_stalk_at x) (pr'.mult_stalk_at x) (pr'.zero_stalk_at x (f \<^sup>\<inverse> X V))
            (pr'.one_stalk_at x (f \<^sup>\<inverse> X V))" using eq_ind_morphism_btw_stalks \<open>f x \<in> V\<close> \<open>is_zariski_open V\<close> \<open>x \<in> X\<close> sorry
    qed
  qed
next
  show "iso_locally_ringed_spaces_axioms X it.ind_is_open cis.ind_sheaf cis.ind_ring_morphisms b
     cis.ind_add_str cis.ind_mult_str cis.ind_zero_str cis.ind_one_str Spec is_zariski_open
     sheaf_spec sheaf_spec_morphisms \<O>b add_sheaf_spec mult_sheaf_spec zero_sheaf_spec
     one_sheaf_spec f \<phi>\<^sub>f"
    sorry
qed
  thus ?thesis by (meson affine_scheme_axioms_def)
qed
*) 

lemma comp_affine_scheme_is_scheme:
  shows "scheme R (+) (\<cdot>) \<zero> \<one> X is_open \<O>\<^sub>X \<rho> b add_str mult_str zero_str one_str"
proof -
  interpret ind_sheaf X is_open \<O>\<^sub>X \<rho> b add_str mult_str zero_str one_str X
    by (metis ind_sheaf_axioms_def ind_sheaf_def open_space ringed_space_axioms ringed_space_def)
  have ind_is_open[simp]: "ind_topology.ind_is_open X is_open X = is_open"
    by (rule ext) (meson ind_is_open_iff_open open_imp_subset)

  interpret sheaf_of_rings X is_open local.ind_sheaf ind_ring_morphisms b ind_add_str 
    ind_mult_str ind_zero_str ind_one_str
    using ind_sheaf_is_sheaf by force

  have "affine_scheme R (+) (\<cdot>) \<zero> \<one> X is_open local.ind_sheaf ind_ring_morphisms b
          ind_add_str ind_mult_str ind_zero_str ind_one_str"
  proof intro_locales
    show "locally_ringed_space_axioms is_open local.ind_sheaf ind_ring_morphisms ind_add_str 
            ind_mult_str ind_zero_str ind_one_str"
    proof -
      have \<section>: "stalk.is_local is_open local.ind_sheaf ind_ring_morphisms ind_add_str
                ind_mult_str ind_zero_str ind_one_str
                (neighborhoods u) u U"
        if "u \<in> U" and opeU: "is_open U" for u U
      proof -
        have UX: "U \<subseteq> X" by (simp add: opeU open_imp_subset)

        interpret stX: stalk X is_open local.ind_sheaf ind_ring_morphisms b ind_add_str 
          ind_mult_str ind_zero_str ind_one_str "neighborhoods u" u
          apply (unfold_locales)
          unfolding neighborhoods_def using \<open>U \<subseteq> X\<close> \<open>u\<in>U\<close> by auto
        interpret stX_r:ring stX.carrier_stalk stX.add_stalk stX.mult_stalk 
          "stX.zero_stalk U" "stX.one_stalk U"
          using that stX.stalk_is_ring by simp_all

        have eq_\<O>\<^sub>X: "local.ind_sheaf U = \<O>\<^sub>X U" if "U \<subseteq> X" for U
          using that by (simp add: Int_absorb2 Int_commute local.ind_sheaf_def)
        have eq_\<rho>: "\<And>U V. U \<subseteq> X \<and> V \<subseteq> X \<Longrightarrow> ind_ring_morphisms U V = \<rho> U V"
          by (simp add: ind_ring_morphisms_def inf.absorb_iff2)
        have eq_add_str: "\<And>U. U \<subseteq> X \<Longrightarrow> ind_add_str U = add_str U"
          by (simp add: ind_add_str_def inf.absorb_iff2)
        have eq_mult_str : "\<And>U. U \<subseteq> X \<Longrightarrow> ind_mult_str U = mult_str U"
          by (simp add: ind_mult_str_def inf.absorb_iff2)
        have eq_zero_str : "\<And>U. U \<subseteq> X \<Longrightarrow> ind_zero_str U = zero_str U"
          by (simp add: Int_absorb2 Int_commute ind_zero_str_def)
        have eq_one_str : "\<And>U. U \<subseteq> X \<Longrightarrow> ind_one_str U = one_str U"
          by (simp add: ind_one_str_def inf.absorb_iff2)

        interpret stalk X is_open \<O>\<^sub>X \<rho> b add_str mult_str zero_str one_str "neighborhoods u" u
          by (meson direct_lim_def ind_sheaf.axioms(1) ind_sheaf_axioms stX.stalk_axioms stalk_def)
        interpret r:ring carrier_stalk add_stalk mult_stalk "zero_stalk U" "one_stalk U"
          using stalk_is_ring that by simp_all
        have "ring stX.carrier_stalk stX.add_stalk stX.mult_stalk (stX.zero_stalk U) (stX.one_stalk U)"
          by (simp add: opeU stX.stalk_is_ring that(1))
        moreover have "local_ring carrier_stalk add_stalk mult_stalk (zero_stalk U) (one_stalk U)"
          using is_local_def opeU stalks_are_local that(1) by blast
        moreover have "ring_isomorphism (restrict id stX.carrier_stalk)
            stX.carrier_stalk stX.add_stalk stX.mult_stalk (stX.zero_stalk U) (stX.one_stalk U)
            carrier_stalk add_stalk mult_stalk (zero_stalk U) (one_stalk U)"
        proof 
          let ?id = "restrict id stX.carrier_stalk"

          let ?A="Sigma (neighborhoods u) local.ind_sheaf"
          let ?B="Sigma (neighborhoods u) \<O>\<^sub>X"
          interpret A:equivalence "Sigma (neighborhoods u) local.ind_sheaf" "{(x, y). stX.rel x y}"
            using stX.rel_is_equivalence by simp
          interpret B:equivalence "Sigma (neighborhoods u) \<O>\<^sub>X" "{(x, y). rel x y}"
            using rel_is_equivalence  by simp

          have stX_carrier:"stX.carrier_stalk = A.Partition"
            unfolding stX.carrier_stalk_def stX.carrier_direct_lim_def by rule

          have S_eq:"?A = ?B" 
            apply (rule Sigma_cong)
            by (simp_all add: eq_\<O>\<^sub>X open_imp_subset subset_of_opens)
          moreover have E_eq:"{(x, y). stX.rel x y} = {(x, y). rel x y}" 
          proof -
            have "stX.rel a1 a2 \<longleftrightarrow> rel a1 a2" if "a1\<in>?A" "a2\<in>?A" for a1 a2 
              unfolding stX.rel_def rel_def by (metis eq_\<O>\<^sub>X eq_\<rho> open_imp_subset subset_of_opens)
            with S_eq show ?thesis 
              by (smt (verit, best) A.left_closed A.right_closed B.left_closed Collect_cong 
                  Pair_inject case_prodE case_prodI2 mem_Collect_eq rel_Class_iff)
          qed
          ultimately have AB:"A.Partition = B.Partition" "A.Class = B.Class"
            by auto
          then have class_of_eq:"stX.class_of = class_of"
            unfolding stX.class_of_def class_of_def by auto 

          show "?id (stX.one_stalk U) = one_stalk U" 
          proof -
            have "stX.one_stalk U \<in> stX.carrier_stalk" by blast
            then have "?id (stX.one_stalk U) = stX.one_stalk U" by auto
            also have "... = one_stalk U"
              unfolding stX.one_stalk_def one_stalk_def 
              unfolding class_of_eq eq_one_str[OF UX] stX_carrier by rule
            finally show ?thesis .
          qed

          show "?id (stX.zero_stalk U) = zero_stalk U" 
          proof -
            have "stX.zero_stalk U \<in> stX.carrier_stalk" by blast
            then have "?id (stX.zero_stalk U) = stX.zero_stalk U" by auto
            also have "... = zero_stalk U"
              unfolding stX.zero_stalk_def zero_stalk_def 
              unfolding class_of_eq eq_zero_str[OF UX] stX_carrier by rule
            finally show ?thesis .
          qed

          show "?id (stX.add_stalk X' Y') = add_stalk (?id X') (?id Y')" 
            "?id (stX.mult_stalk X' Y') = mult_stalk (?id X') (?id Y')" 
            if "X' \<in> stX.carrier_stalk" "Y' \<in> stX.carrier_stalk" for X' Y'
          proof -
            define x where "x=(SOME x. x \<in> X')"
            define y where "y=(SOME y. y \<in> Y')"
            have x:"x\<in>X'" "x\<in>?A" and x_alt:"X' = stX.class_of (fst x) (snd x)"
              using stX.rel_carrier_Eps_in[OF that(1)[unfolded stX.carrier_stalk_def]] 
              unfolding x_def by auto
            have y:"y\<in>Y'" "y\<in>?A" and y_alt:"Y' = stX.class_of (fst y) (snd y)"
              using stX.rel_carrier_Eps_in[OF that(2)[unfolded stX.carrier_stalk_def]] 
              unfolding y_def by auto
            have "fst x \<subseteq> X" "fst y \<subseteq> X" 
              subgoal by (metis SigmaE open_imp_subset prod.sel(1) subset_of_opens x(2))
              by (metis SigmaE open_imp_subset prod.sel(1) subset_of_opens y(2))


            obtain w where w:"w\<in>neighborhoods u" "w \<subseteq> fst x" "w \<subseteq> fst y"
              using stX.has_lower_bound x(2) y(2) by force
            have "w \<subseteq> X" 
              by (simp add: open_imp_subset subset_of_opens w(1))

            have "stX.add_stalk X' Y' = stX.class_of w (ind_add_str w 
                    (ind_ring_morphisms (fst x) w (snd x)) (ind_ring_morphisms (fst y) w (snd y)))"
              unfolding x_alt y_alt stX.add_stalk_def
              apply (subst stX.add_rel_class_of[where W=w])
              using x y w by auto
            also have "... = class_of w (add_str w (\<rho> (fst x) w (snd x)) (\<rho> (fst y) w (snd y)))"
              unfolding class_of_eq  eq_add_str[OF \<open>w \<subseteq> X\<close>]
              using eq_\<rho> \<open>fst x \<subseteq> X\<close> \<open>fst y \<subseteq> X\<close> \<open>w \<subseteq> X\<close> by simp
            also have "... = add_stalk X' Y'"
              unfolding add_stalk_def x_alt y_alt class_of_eq   
              apply (subst add_rel_class_of[where W=w])
              using x y w S_eq by auto
            finally have "stX.add_stalk X' Y' = add_stalk X' Y'" .
            moreover have "stX.add_stalk X' Y' \<in> stX.carrier_stalk"
              unfolding stX.add_stalk_def using that 
              using stX.carrier_stalk_def by blast
            ultimately show "?id (stX.add_stalk X' Y') = add_stalk (?id X') (?id Y')" 
              using that by simp

            have "stX.mult_stalk X' Y' = stX.class_of w (ind_mult_str w 
                    (ind_ring_morphisms (fst x) w (snd x)) (ind_ring_morphisms (fst y) w (snd y)))"
              unfolding x_alt y_alt stX.mult_stalk_def
              apply (subst stX.mult_rel_class_of[where W=w])
              using x y w by auto
            also have "... = class_of w (mult_str w (\<rho> (fst x) w (snd x)) (\<rho> (fst y) w (snd y)))"
              unfolding class_of_eq  eq_mult_str[OF \<open>w \<subseteq> X\<close>]
              using eq_\<rho> \<open>fst x \<subseteq> X\<close> \<open>fst y \<subseteq> X\<close> \<open>w \<subseteq> X\<close> by simp
            also have "... = mult_stalk X' Y'"
              unfolding mult_stalk_def x_alt y_alt class_of_eq   
              apply (subst mult_rel_class_of[where W=w])
              using x y w S_eq by auto
            finally have "stX.mult_stalk X' Y' = mult_stalk X' Y'" .
            moreover have "stX.mult_stalk X' Y' \<in> stX.carrier_stalk"
              unfolding stX.mult_stalk_def using that 
              using stX.carrier_stalk_def by blast
            ultimately show "?id (stX.mult_stalk X' Y') = mult_stalk (?id X') (?id Y')" 
              using that by simp
          qed

          have "stX.carrier_stalk = carrier_stalk"
            unfolding stX_carrier carrier_stalk_def carrier_direct_lim_def
            using AB(1) by simp
          then show "?id \<in> stX.carrier_stalk \<rightarrow>\<^sub>E carrier_stalk"
            "bij_betw ?id stX.carrier_stalk carrier_stalk"
            by auto
        qed 
        ultimately show ?thesis unfolding stX.is_local_def
          by (rule isomorphic_to_local_is_local[of _ _ _ _ _ carrier_stalk add_stalk mult_stalk 
                "zero_stalk U" "one_stalk U"])
      qed
      then show ?thesis using locally_ringed_space_axioms_def by force
    qed
    show "affine_scheme_axioms R (+) (\<cdot>) \<zero> \<one> X is_open local.ind_sheaf ind_ring_morphisms b 
            ind_add_str ind_mult_str ind_zero_str ind_one_str"
      sorry
  qed
  moreover have "is_open X" by simp
  ultimately show ?thesis
    by unfold_locales fastforce
qed

(*
  fix x assume "x \<in> X"
  have "is_open X"
    by simp
  show "\<exists>U. x \<in> U \<and> is_open U \<and>
             affine_scheme R (+) (\<cdot>) \<zero> \<one> U (ind_topology.ind_is_open X is_open U) (ind_sheaf.ind_sheaf \<O>\<^sub>X U)
              (ind_sheaf.ind_ring_morphisms \<rho> U) b (ind_sheaf.ind_add_str add_str U) (ind_sheaf.ind_mult_str mult_str U)
              (ind_sheaf.ind_zero_str zero_str U) (ind_sheaf.ind_one_str one_str U)"
  proof -
    interpret ind_sheaf X is_open \<O>\<^sub>X \<rho> b add_str mult_str zero_str one_str X
      by (simp add: ind_sheaf_axioms_def ind_sheaf_def sheaf_of_rings_axioms)
    have comp1 [simp]: "\<And>U. ind_topology.ind_is_open X is_open X U = is_open U"
      by (meson ind_is_open_iff_open open_imp_subset)
    have comp2 [simp]: "\<And>U. U \<subseteq> X \<Longrightarrow> ind_sheaf.ind_sheaf \<O>\<^sub>X X U =  \<O>\<^sub>X U"
      by (simp add: Int_absorb2 Int_commute local.ind_sheaf_def)
    have comp3 [simp]: "\<And>U V. U \<subseteq> X \<and> V \<subseteq> X \<Longrightarrow> ind_sheaf.ind_ring_morphisms \<rho> X U V = \<rho> U V"
      by (simp add: ind_ring_morphisms_def inf.absorb_iff2)
    have comp4 [simp]: "\<And>U. U \<subseteq> X \<Longrightarrow> ind_sheaf.ind_add_str add_str X U = add_str U"
      by (simp add: ind_add_str_def inf.absorb_iff2)
    have comp5 [simp]: "\<And>U. U \<subseteq> X \<Longrightarrow> ind_sheaf.ind_mult_str mult_str X U = mult_str U"
      by (simp add: ind_mult_str_def inf.absorb_iff2)
    have comp6 [simp]: "\<And>U. U \<subseteq> X \<Longrightarrow> ind_sheaf.ind_zero_str zero_str X U = zero_str U"
      by (simp add: Int_absorb2 Int_commute ind_zero_str_def)
    have comp7 [simp]: "\<And>U. U \<subseteq> X \<Longrightarrow> ind_sheaf.ind_one_str one_str X U = one_str U"
      by (simp add: ind_one_str_def inf.absorb_iff2)
    have \<section>: "stalk.is_local (ind_topology.ind_is_open X is_open X) (ind_sheaf.ind_sheaf \<O>\<^sub>X X) (ind_sheaf.ind_ring_morphisms \<rho> X) (ind_sheaf.ind_add_str add_str X) (ind_sheaf.ind_mult_str mult_str X) (ind_sheaf.ind_zero_str zero_str X) (ind_sheaf.ind_one_str one_str X) (topological_space.neighborhoods (ind_topology.ind_is_open X is_open X) x) x U"
      if "x \<in> U" and opeU: "ind_topology.ind_is_open X is_open X U"
      for x U
    proof -
      have "x \<in> X"
        using opeU ind_is_open_iff_open that(1) by blast
      interpret sheafX: sheaf_of_rings X "ind_topology.ind_is_open X is_open X" "ind_sheaf.ind_sheaf \<O>\<^sub>X X"
        "ind_sheaf.ind_ring_morphisms \<rho> X" b 
        "ind_sheaf.ind_add_str add_str X" "ind_sheaf.ind_mult_str mult_str X" 
        "ind_sheaf.ind_zero_str zero_str X" "ind_sheaf.ind_one_str one_str X"
        using ind_sheaf_is_sheaf by blast
      interpret stX: stalk X "ind_topology.ind_is_open X is_open X" "ind_sheaf.ind_sheaf \<O>\<^sub>X X"
        "ind_sheaf.ind_ring_morphisms \<rho> X" b 
        "ind_sheaf.ind_add_str add_str X" "ind_sheaf.ind_mult_str mult_str X" 
        "ind_sheaf.ind_zero_str zero_str X" "ind_sheaf.ind_one_str one_str X" 
        "topological_space.neighborhoods (ind_topology.ind_is_open X is_open X) x" 
        x
      proof qed (use \<open>x \<in> X\<close> sheafX.neighborhoods_def in auto)
      interpret stalk X is_open \<O>\<^sub>X \<rho> b add_str mult_str zero_str one_str "neighborhoods x" x
      proof qed (auto simp add: \<open>x \<in> X\<close> neighborhoods_def)
      have "local_ring_axioms stX.carrier_stalk stX.add_stalk stX.mult_stalk (stX.zero_stalk U) (stX.one_stalk U)"
      proof
        fix I J
        assume "max_lideal I stX.carrier_stalk stX.add_stalk stX.mult_stalk (stX.zero_stalk U) (stX.one_stalk U)"
          and "max_lideal J stX.carrier_stalk stX.add_stalk stX.mult_stalk (stX.zero_stalk U) (stX.one_stalk U)"
        show "I = J"
          sorry
      next
        show "\<exists>\<ww>. max_lideal \<ww> stX.carrier_stalk stX.add_stalk stX.mult_stalk (stX.zero_stalk U) (stX.one_stalk U)"
          sorry
      qed
      then show ?thesis
        unfolding stX.is_local_def
        by (meson local_ring.intro opeU stX.stalk_is_ring that(1))
    qed
    interpret lrs: locally_ringed_space X "ind_topology.ind_is_open X is_open X"
      local.ind_sheaf ind_ring_morphisms b ind_add_str ind_mult_str ind_zero_str ind_one_str
      by (simp add: "\<section>" ind_sheaf_is_sheaf locally_ringed_space_axioms_def locally_ringed_space_def ringed_space_def)
    interpret cm: continuous_map X "ind_topology.ind_is_open X is_open X" Spec is_zariski_open f
      using comp1 continuous_map_axioms by presburger
    have "affine_scheme_axioms R (+) (\<cdot>) \<zero> \<one> X (ind_topology.ind_is_open X is_open X)
                   local.ind_sheaf ind_ring_morphisms b ind_add_str ind_mult_str ind_zero_str ind_one_str"
      apply unfold_locales
      sorry
    with \<open>x \<in> X\<close> show ?thesis
      by (meson affine_scheme_def local.comm_ring_axioms lrs.locally_ringed_space_axioms open_space)
  qed
qed 
*)

end (* comp_affine_scheme *)

lemma (in affine_scheme) affine_scheme_is_scheme:
  shows "scheme R (+) (\<cdot>) \<zero> \<one> X is_open \<O>\<^sub>X \<rho> b add_str mult_str zero_str one_str" 
  using comp_affine_scheme.comp_affine_scheme_is_scheme comp_affine_scheme_def is_iso_to_spec 
local.comm_ring_axioms locally_ringed_space_axioms by fastforce


lemma (in comm_ring) spec_is_comp_affine_scheme:
  shows "comp_affine_scheme R (+) (\<cdot>) \<zero> \<one> Spec is_zariski_open sheaf_spec sheaf_spec_morphisms \<O>b
(\<lambda>U. add_sheaf_spec U) (\<lambda>U. mult_sheaf_spec U) (\<lambda>U. zero_sheaf_spec U) (\<lambda>U. one_sheaf_spec U)
(identity Spec) (\<lambda>U. identity (\<O> U))"
proof (intro comp_affine_scheme.intro)
  show "comm_ring R (+) (\<cdot>) \<zero> \<one>" by (simp add: local.comm_ring_axioms)
next
  show "locally_ringed_space Spec is_zariski_open sheaf_spec sheaf_spec_morphisms \<O>b add_sheaf_spec mult_sheaf_spec
     zero_sheaf_spec one_sheaf_spec" using spec_is_locally_ringed_space by simp
next
  have [simp]: "\<And>x A. x \<in> A \<Longrightarrow> inv_into A (identity A) x = x"
    by (metis bij_betw_def bij_betw_restrict_eq inj_on_id2 inv_into_f_f restrict_apply')
  interpret zar: topological_space Spec is_zariski_open
    by blast
  interpret im_sheaf Spec is_zariski_open sheaf_spec
    sheaf_spec_morphisms \<O>b add_sheaf_spec mult_sheaf_spec zero_sheaf_spec one_sheaf_spec Spec
    is_zariski_open "identity Spec"
    by (metis homeomorphism_def im_sheaf_def sheaf_spec_is_sheaf zar.id_is_homeomorphism)
  have rh: "\<And>U V. \<lbrakk>is_zariski_open U; is_zariski_open V; V \<subseteq> U\<rbrakk>
             \<Longrightarrow> ring_homomorphism
                  (im_sheaf_morphisms U V)
                  (local.im_sheaf U) (add_sheaf_spec U)
                  (mult_sheaf_spec U) (zero_sheaf_spec U)
                  (one_sheaf_spec U) (local.im_sheaf V)
                  (add_sheaf_spec V) (mult_sheaf_spec V)
                  (zero_sheaf_spec V) (one_sheaf_spec V)"
    using im_sheaf_morphisms_def local.im_sheaf_def sheaf_spec_morphisms_are_ring_morphisms zar.open_preimage_identity by presburger
  interpret F: presheaf_of_rings Spec is_zariski_open 
    "im_sheaf.im_sheaf Spec sheaf_spec (identity Spec)"
    "im_sheaf.im_sheaf_morphisms Spec sheaf_spec_morphisms (identity Spec)" \<O>b 
    "\<lambda>V. add_sheaf_spec (identity Spec \<^sup>\<inverse> Spec V)" "\<lambda>V. mult_sheaf_spec (identity Spec \<^sup>\<inverse> Spec V)" 
    "\<lambda>V. zero_sheaf_spec (identity Spec \<^sup>\<inverse> Spec V)"  "\<lambda>V. one_sheaf_spec (identity Spec \<^sup>\<inverse> Spec V)"
    unfolding presheaf_of_rings_def presheaf_of_rings_axioms_def
  proof (intro conjI strip)
    show "im_sheaf_morphisms U W x = (im_sheaf_morphisms V W \<circ> im_sheaf_morphisms U V) x"
      if "is_zariski_open U" "is_zariski_open V" "is_zariski_open W" "V \<subseteq> U"
        and "W \<subseteq> V" "x \<in> local.im_sheaf U" for U V W x
      using that assoc_comp by blast
  qed (auto simp: rh ring_of_empty)

  show "iso_locally_ringed_spaces Spec is_zariski_open sheaf_spec sheaf_spec_morphisms \<O>b
     add_sheaf_spec mult_sheaf_spec zero_sheaf_spec one_sheaf_spec Spec is_zariski_open sheaf_spec
     sheaf_spec_morphisms \<O>b add_sheaf_spec mult_sheaf_spec zero_sheaf_spec one_sheaf_spec
     (identity Spec) (\<lambda>U. identity (\<O> U))"
  proof -
    have "iso_sheaves_of_rings
            Spec is_zariski_open sheaf_spec sheaf_spec_morphisms \<O>b add_sheaf_spec mult_sheaf_spec zero_sheaf_spec one_sheaf_spec
            (im_sheaf.im_sheaf Spec sheaf_spec (identity Spec))
            (im_sheaf.im_sheaf_morphisms Spec sheaf_spec_morphisms (identity Spec))
            \<O>b
            (\<lambda>V x y. add_sheaf_spec ((identity Spec)\<^sup>\<inverse> Spec V) x y) 
            (\<lambda>V x y. mult_sheaf_spec ((identity Spec)\<^sup>\<inverse> Spec V) x y) 
            (\<lambda>V. zero_sheaf_spec ((identity Spec)\<^sup>\<inverse> Spec V)) 
            (\<lambda>V. one_sheaf_spec ((identity Spec)\<^sup>\<inverse> Spec V))
            (\<lambda>U. identity (\<O> U))"
    proof intro_locales
      show "morphism_presheaves_of_rings_axioms is_zariski_open sheaf_spec sheaf_spec_morphisms add_sheaf_spec mult_sheaf_spec zero_sheaf_spec one_sheaf_spec (im_sheaf.im_sheaf Spec sheaf_spec (identity Spec)) (im_sheaf.im_sheaf_morphisms Spec sheaf_spec_morphisms (identity Spec)) (\<lambda>V. add_sheaf_spec (identity Spec \<^sup>\<inverse> Spec V)) (\<lambda>V. mult_sheaf_spec (identity Spec \<^sup>\<inverse> Spec V)) (\<lambda>V. zero_sheaf_spec (identity Spec \<^sup>\<inverse> Spec V)) (\<lambda>V. one_sheaf_spec (identity Spec \<^sup>\<inverse> Spec V)) (\<lambda>U. identity (\<O> U))"
        using F.id_is_mor_pr_rngs
        by (simp add: local.im_sheaf_def morphism_presheaves_of_rings_def morphism_presheaves_of_rings_axioms_def im_sheaf_morphisms_def)
      then show "iso_presheaves_of_rings_axioms Spec is_zariski_open sheaf_spec sheaf_spec_morphisms \<O>b add_sheaf_spec mult_sheaf_spec zero_sheaf_spec one_sheaf_spec (im_sheaf.im_sheaf Spec sheaf_spec (identity Spec)) (im_sheaf.im_sheaf_morphisms Spec sheaf_spec_morphisms (identity Spec)) \<O>b (\<lambda>V. add_sheaf_spec (identity Spec \<^sup>\<inverse> Spec V)) (\<lambda>V. mult_sheaf_spec (identity Spec \<^sup>\<inverse> Spec V)) (\<lambda>V. zero_sheaf_spec (identity Spec \<^sup>\<inverse> Spec V)) (\<lambda>V. one_sheaf_spec (identity Spec \<^sup>\<inverse> Spec V)) (\<lambda>U. identity (\<O> U))"
        unfolding iso_presheaves_of_rings_axioms_def
        apply (rule_tac x="(\<lambda>U. identity (\<O> U))" in exI)
        using F.presheaf_of_rings_axioms
        by (simp add: im_sheaf_morphisms_def local.im_sheaf_def morphism_presheaves_of_rings.intro morphism_presheaves_of_rings_axioms_def sheaf_spec_is_presheaf)
    qed
    moreover have "morphism_locally_ringed_spaces
                    Spec is_zariski_open sheaf_spec sheaf_spec_morphisms \<O>b add_sheaf_spec mult_sheaf_spec zero_sheaf_spec one_sheaf_spec
                    Spec is_zariski_open sheaf_spec sheaf_spec_morphisms \<O>b add_sheaf_spec mult_sheaf_spec zero_sheaf_spec one_sheaf_spec
                    (identity Spec)
                    (\<lambda>U. identity (\<O> U))"
      by (simp add: locally_ringed_space.id_to_mor_locally_ringed_spaces spec_is_locally_ringed_space) 
    ultimately show ?thesis 
      by (metis locally_ringed_space.id_to_iso_locally_ringed_spaces spec_is_locally_ringed_space)
  qed
qed

lemma (in comm_ring) spec_is_scheme:
  shows "scheme R (+) (\<cdot>) \<zero> \<one> Spec is_zariski_open sheaf_spec sheaf_spec_morphisms \<O>b
(\<lambda>U. add_sheaf_spec U) (\<lambda>U. mult_sheaf_spec U) (\<lambda>U. zero_sheaf_spec U) (\<lambda>U. one_sheaf_spec U)"
  using spec_is_comp_affine_scheme affine_scheme.affine_scheme_is_scheme sorry

lemma empty_scheme_is_comp_affine_scheme:
  shows "comp_affine_scheme {0::nat} (\<lambda>x y. 0) (\<lambda>x y. 0) 0 0 
{} (\<lambda>U. U={}) (\<lambda>U. {0::nat}) (\<lambda>U V. identity{0}) 0 (\<lambda>U x y. 0) (\<lambda>U x y. 0) (\<lambda>U. 0) (\<lambda>U. 0)
(\<lambda>\<pp>\<in>Spec. undefined) (\<lambda>U. \<lambda>s \<in> cring0.sheaf_spec U. 0)"
proof -
  interpret im0: im_sheaf "{}" "\<lambda>U. U = {}" "\<lambda>U. {0}" "\<lambda>U V. identity {0}"
    "0" "\<lambda>U x y. 0" "\<lambda>U x y. 0" "\<lambda>U. 0" "\<lambda>U. 0" "{}" "\<lambda>U. U = {}" "\<lambda>\<pp>\<in>Spec. undefined"
  proof qed (use invertible_0 in auto)
  note im0.target.open_space [simp del] im0.ring_of_empty [simp del] im0.open_space [simp del] 
  have cring0_open [simp]: "\<And>N. cring0.is_zariski_open N \<longleftrightarrow> N = {}"
    by (metis comm_ring.cring0_is_zariski_open cring0.comm_ring_axioms)
  have ring_im: "ring (im0.im_sheaf V) (im0.add_im_sheaf V) (im0.mult_im_sheaf V) (im0.zero_im_sheaf V) (im0.one_im_sheaf V)"
    for V :: "nat set set"
  proof intro_locales
    show "Group_Theory.monoid (im0.im_sheaf V) (im0.add_im_sheaf V) (im0.zero_im_sheaf V)"
      unfolding im0.add_im_sheaf_def im0.im_sheaf_def im0.zero_im_sheaf_def monoid_def
      by force
    then show "Group_Theory.group_axioms (im0.im_sheaf V) (im0.add_im_sheaf V) (im0.zero_im_sheaf V)"
      unfolding Group_Theory.group_axioms_def im0.im_sheaf_def im0.zero_im_sheaf_def im0.add_im_sheaf_def
      by (simp add: invertible_0)
    show "commutative_monoid_axioms (im0.im_sheaf V) (im0.add_im_sheaf V)"
      by (metis im0.add_im_sheaf_def commutative_monoid_axioms.intro)
  qed (auto simp: im0.im_sheaf_def im0.add_im_sheaf_def im0.mult_im_sheaf_def im0.one_im_sheaf_def monoid_def ring_axioms_def)
  have rh0: "ring_homomorphism (cring0.sheaf_spec_morphisms {} {}) {\<lambda>x. undefined}
             (cring0.add_sheaf_spec {}) (cring0.mult_sheaf_spec {}) (cring0.zero_sheaf_spec {}) (cring0.one_sheaf_spec {}) {\<lambda>x. undefined}
             (cring0.add_sheaf_spec {}) (cring0.mult_sheaf_spec {}) (cring0.zero_sheaf_spec {}) (cring0.one_sheaf_spec {})"
    by (metis cring0.cring0_sheaf_spec_empty cring0.is_zariski_open_empty cring0.sheaf_spec_morphisms_are_ring_morphisms im0.target.open_imp_subset)
  show ?thesis
  proof intro_locales
    show "locally_ringed_space_axioms (\<lambda>U. U={}) (\<lambda>U. {0::nat}) (\<lambda>U V. identity{0}) (\<lambda>U x y. 0) (\<lambda>U x y. 0) (\<lambda>U. 0) (\<lambda>U. 0)"
      by (metis (mono_tags, lifting) empty_iff locally_ringed_space_axioms_def)
    show "topological_space cring0.spectrum cring0.is_zariski_open"
      by blast
    show [simp]: "Set_Theory.map (\<lambda>\<pp>\<in>Spec. undefined) {} cring0.spectrum"
      by (metis cring0.cring0_spectrum_eq im0.map_axioms)
    show "continuous_map_axioms {} (\<lambda>U. U={}) cring0.is_zariski_open (\<lambda>\<pp>\<in>Spec. undefined)"
      unfolding continuous_map_axioms_def by fastforce
    show "presheaf_of_rings_axioms cring0.is_zariski_open cring0.sheaf_spec
            cring0.sheaf_spec_morphisms cring0.\<O>b cring0.add_sheaf_spec cring0.mult_sheaf_spec cring0.zero_sheaf_spec cring0.one_sheaf_spec"
      using cring0.\<O>_on_emptyset cring0.sheaf_morphisms_sheaf_spec
      by (metis cring0.sheaf_spec_is_presheaf presheaf_of_rings_def) 
    show "sheaf_of_rings_axioms cring0.spectrum cring0.is_zariski_open cring0.sheaf_spec cring0.sheaf_spec_morphisms cring0.zero_sheaf_spec"
      using cring0.sheaf_spec_is_sheaf sheaf_of_rings_def by metis
    have im_sheaf_0[simp]: "im_sheaf.im_sheaf {} (\<lambda>U. {0}) (\<lambda>\<pp>\<in>Spec. undefined) U = {0}" for U :: "nat set set"
      using im0.im_sheaf_def by blast
    have rh: "ring_homomorphism (im0.im_sheaf_morphisms U V) (im0.im_sheaf U) (im0.add_im_sheaf U)
         (im0.mult_im_sheaf U) (im0.zero_im_sheaf U) (im0.one_im_sheaf U) (im0.im_sheaf V)
         (im0.add_im_sheaf V) (im0.mult_im_sheaf V) (im0.zero_im_sheaf V) (im0.one_im_sheaf V)"
      if "cring0.is_zariski_open U" "cring0.is_zariski_open V" "V \<subseteq> U" for U V
      using that by (metis cring0.cring0_is_zariski_open im0.is_ring_morphism) 
    show "morphism_ringed_spaces_axioms {} (\<lambda>U. {0})
         (\<lambda>U V. identity {0}) 0 (\<lambda>U x y. 0) (\<lambda>U x y. 0)
         (\<lambda>U. 0) (\<lambda>U. 0) cring0.spectrum cring0.is_zariski_open cring0.sheaf_spec
         cring0.sheaf_spec_morphisms cring0.\<O>b cring0.add_sheaf_spec
         cring0.mult_sheaf_spec cring0.zero_sheaf_spec cring0.one_sheaf_spec
         (\<lambda>\<pp>\<in>Spec. undefined) (\<lambda>U. \<lambda>s\<in>cring0.sheaf_spec U. 0)"
      unfolding morphism_ringed_spaces_axioms_def morphism_sheaves_of_rings_def
        morphism_presheaves_of_rings_def 
    proof (intro conjI)
      show "presheaf_of_rings cring0.spectrum cring0.is_zariski_open cring0.sheaf_spec
         cring0.sheaf_spec_morphisms cring0.\<O>b cring0.add_sheaf_spec
         cring0.mult_sheaf_spec cring0.zero_sheaf_spec cring0.one_sheaf_spec"
        using cring0.sheaf_spec_is_presheaf by force
      show "presheaf_of_rings cring0.spectrum cring0.is_zariski_open im0.im_sheaf im0.im_sheaf_morphisms
 0 im0.add_im_sheaf im0.mult_im_sheaf im0.zero_im_sheaf im0.one_im_sheaf"
        by (smt (z3) comm_ring.cring0_is_zariski_open cring0.comm_ring_axioms cring0.cring0_spectrum_eq im0.presheaf_of_rings_axioms)
      show "morphism_presheaves_of_rings_axioms cring0.is_zariski_open cring0.sheaf_spec cring0.sheaf_spec_morphisms 
               cring0.add_sheaf_spec cring0.mult_sheaf_spec cring0.zero_sheaf_spec cring0.one_sheaf_spec 
               im0.im_sheaf im0.im_sheaf_morphisms im0.add_im_sheaf im0.mult_im_sheaf im0.zero_im_sheaf im0.one_im_sheaf (\<lambda>U. \<lambda>s\<in>cring0.sheaf_spec U. 0)"
        unfolding morphism_presheaves_of_rings_axioms_def
      proof (intro conjI strip)
        fix U
        assume "cring0.is_zariski_open U"
        interpret rU: ring "cring0.sheaf_spec U" "cring0.add_sheaf_spec U" "cring0.mult_sheaf_spec U" "cring0.zero_sheaf_spec U" "cring0.one_sheaf_spec U"
          by (metis \<open>cring0.is_zariski_open U\<close> comm_ring.axioms(1) cring0.sheaf_spec_on_open_is_comm_ring)
        interpret rU': ring "im0.im_sheaf U" "im0.add_im_sheaf U" "im0.mult_im_sheaf U" "im0.zero_im_sheaf U" "im0.one_im_sheaf U"
          using ring_im by blast
        show "ring_homomorphism (\<lambda>s\<in>cring0.sheaf_spec U. 0) (cring0.sheaf_spec U) (cring0.add_sheaf_spec U) (cring0.mult_sheaf_spec U) (cring0.zero_sheaf_spec U) (cring0.one_sheaf_spec U) 
                            (im0.im_sheaf U) (im0.add_im_sheaf U) (im0.mult_im_sheaf U) (im0.zero_im_sheaf U) (im0.one_im_sheaf U)"
        proof intro_locales
          show "Set_Theory.map (\<lambda>s\<in>cring0.sheaf_spec U. 0) (cring0.sheaf_spec U) (im0.im_sheaf U)"
            unfolding  Set_Theory.map_def by (metis ext_funcset_to_sing_iff im0.im_sheaf_def singletonI)
          show "monoid_homomorphism_axioms (\<lambda>s\<in>cring0.sheaf_spec U. 0) (cring0.sheaf_spec U) (cring0.add_sheaf_spec U) (cring0.zero_sheaf_spec U) (im0.add_im_sheaf U) (im0.zero_im_sheaf U)"
            unfolding monoid_homomorphism_axioms_def im0.zero_im_sheaf_def im0.add_im_sheaf_def
            by (metis rU.additive.unit_closed rU.additive.composition_closed restrict_apply)
          show "monoid_homomorphism_axioms (\<lambda>s\<in>cring0.sheaf_spec U. 0) (cring0.sheaf_spec U) (cring0.mult_sheaf_spec U) (cring0.one_sheaf_spec U) (im0.mult_im_sheaf U) (im0.one_im_sheaf U)"
            unfolding monoid_homomorphism_axioms_def im0.mult_im_sheaf_def im0.one_im_sheaf_def
            by (metis rU.multiplicative.composition_closed rU.multiplicative.unit_closed restrict_apply)
        qed
        show "(im0.im_sheaf_morphisms U V \<circ> (\<lambda>s\<in>cring0.sheaf_spec U. 0)) x = ((\<lambda>s\<in>cring0.sheaf_spec V. 0) \<circ> cring0.sheaf_spec_morphisms U V) x"
          if "cring0.is_zariski_open U" "cring0.is_zariski_open V" "V \<subseteq> U" "x \<in> cring0.sheaf_spec U"
          for U V x
          using that cring0.sheaf_morphisms_sheaf_spec 
          unfolding im0.im_sheaf_morphisms_def o_def
          by (metis cring0.cring0_is_zariski_open insertI1 restrict_apply')
      qed
    qed
    interpret monoid0: Group_Theory.monoid "{\<lambda>x. undefined}"
      "cring0.add_sheaf_spec {}"
      "(\<lambda>\<pp>\<in>{}. quotient_ring.zero_rel ({0}\<setminus>\<pp>) {0} ring0.subtraction ring0.subtraction 0 0)"
      by (smt (verit, best) Group_Theory.monoid.intro cring0.add_sheaf_spec_extensional extensional_empty restrict_extensional singletonD)

    show "iso_locally_ringed_spaces_axioms {} (\<lambda>U. U = {})
     (\<lambda>U. {0}) (\<lambda>U V. identity {0}) 0 (\<lambda>U x y. 0)
     (\<lambda>U x y. 0) (\<lambda>U. 0) (\<lambda>U. 0) cring0.spectrum
     cring0.is_zariski_open cring0.sheaf_spec
     cring0.sheaf_spec_morphisms cring0.\<O>b
     cring0.add_sheaf_spec cring0.mult_sheaf_spec
     cring0.zero_sheaf_spec cring0.one_sheaf_spec
     (\<lambda>\<pp>\<in>Spec. undefined)
     (\<lambda>U. \<lambda>s\<in>cring0.sheaf_spec U. 0::nat)"
      unfolding iso_locally_ringed_spaces_axioms_def
    proof (intro conjI)
      show "homeomorphism {} (\<lambda>U. U = {}) cring0.spectrum cring0.is_zariski_open (\<lambda>\<pp>\<in>Spec. undefined)"
      proof intro_locales
        show "bijective (\<lambda>\<pp>\<in>Spec. undefined) {} cring0.spectrum"
          unfolding bijective_def bij_betw_def
          using cring0.cring0_spectrum_eq by blast
        show "Set_Theory.map (inverse_map (\<lambda>\<pp>\<in>Spec. undefined) {} cring0.spectrum) cring0.spectrum {}"
          unfolding Set_Theory.map_def inverse_map_def restrict_def
          by (smt (verit, best) PiE_I cring0.cring0_spectrum_eq empty_iff)
      qed (use im0.map_axioms continuous_map_axioms_def in \<open>force+\<close>)
      show "iso_sheaves_of_rings cring0.spectrum cring0.is_zariski_open cring0.sheaf_spec
                 cring0.sheaf_spec_morphisms cring0.\<O>b cring0.add_sheaf_spec cring0.mult_sheaf_spec cring0.zero_sheaf_spec cring0.one_sheaf_spec 
                 im0.im_sheaf im0.im_sheaf_morphisms (0::nat) im0.add_im_sheaf im0.mult_im_sheaf im0.zero_im_sheaf im0.one_im_sheaf (\<lambda>U. \<lambda>s\<in>cring0.sheaf_spec U. 0::nat)"
      proof intro_locales
        show "topological_space cring0.spectrum cring0.is_zariski_open"
          by force
        show "presheaf_of_rings_axioms cring0.is_zariski_open cring0.sheaf_spec cring0.sheaf_spec_morphisms cring0.\<O>b cring0.add_sheaf_spec cring0.mult_sheaf_spec cring0.zero_sheaf_spec cring0.one_sheaf_spec"
          using \<open>presheaf_of_rings_axioms cring0.is_zariski_open cring0.sheaf_spec cring0.sheaf_spec_morphisms cring0.\<O>b cring0.add_sheaf_spec cring0.mult_sheaf_spec cring0.zero_sheaf_spec cring0.one_sheaf_spec\<close> by force
        show "presheaf_of_rings_axioms cring0.is_zariski_open im0.im_sheaf im0.im_sheaf_morphisms (0::nat) im0.add_im_sheaf im0.mult_im_sheaf im0.zero_im_sheaf im0.one_im_sheaf"
          using im0.presheaf_of_rings_axioms presheaf_of_rings_def by force
        show "morphism_presheaves_of_rings_axioms cring0.is_zariski_open cring0.sheaf_spec cring0.sheaf_spec_morphisms cring0.add_sheaf_spec cring0.mult_sheaf_spec cring0.zero_sheaf_spec cring0.one_sheaf_spec im0.im_sheaf im0.im_sheaf_morphisms im0.add_im_sheaf im0.mult_im_sheaf im0.zero_im_sheaf im0.one_im_sheaf (\<lambda>U. \<lambda>s\<in>cring0.sheaf_spec U. 0::nat)"
        proof qed (auto simp: cring0.zero_sheaf_spec_def cring0.one_sheaf_spec_def cring0.add_sheaf_spec_def cring0.mult_sheaf_spec_def 
            im0.zero_im_sheaf_def im0.one_im_sheaf_def im0.add_im_sheaf_def im0.mult_im_sheaf_def
            im0.im_sheaf_morphisms_def cring0.sheaf_morphisms_sheaf_spec monoid0.invertible_def)
      have morph_empty: "morphism_presheaves_of_rings {} (\<lambda>U. U = {})
             im0.im_sheaf im0.im_sheaf_morphisms 0 (\<lambda>V. ring0.subtraction) (\<lambda>V. ring0.subtraction)
             (\<lambda>V. 0) (\<lambda>V. 0) cring0.sheaf_spec cring0.sheaf_spec_morphisms cring0.\<O>b
             cring0.add_sheaf_spec cring0.mult_sheaf_spec cring0.zero_sheaf_spec cring0.one_sheaf_spec
             (\<lambda>S. \<lambda>n\<in>{0}. \<lambda>x. undefined)"
      proof qed (auto simp: im0.im_sheaf_morphisms_def cring0.sheaf_spec_morphisms_def 
            cring0.zero_sheaf_spec_def cring0.one_sheaf_spec_def cring0.add_sheaf_spec_def cring0.mult_sheaf_spec_def 
            cring0.\<O>b_def monoid0.invertible_def)
      then show "iso_presheaves_of_rings_axioms cring0.spectrum cring0.is_zariski_open cring0.sheaf_spec 
                   cring0.sheaf_spec_morphisms cring0.\<O>b cring0.add_sheaf_spec cring0.mult_sheaf_spec cring0.zero_sheaf_spec cring0.one_sheaf_spec 
                   im0.im_sheaf im0.im_sheaf_morphisms (0::nat) im0.add_im_sheaf im0.mult_im_sheaf im0.zero_im_sheaf im0.one_im_sheaf (\<lambda>U. \<lambda>s\<in>cring0.sheaf_spec U. 0)"
        by unfold_locales (auto simp add: im0.zero_im_sheaf_def im0.one_im_sheaf_def im0.add_im_sheaf_def im0.mult_im_sheaf_def)
      qed
    qed
    show "morphism_locally_ringed_spaces_axioms {}
     (\<lambda>U. U = {}) (\<lambda>U. {0}) (\<lambda>U V. identity {0})
     (\<lambda>U x y. 0) (\<lambda>U x y. 0) (\<lambda>U. 0) (\<lambda>U. 0)
     cring0.is_zariski_open cring0.sheaf_spec
     cring0.sheaf_spec_morphisms cring0.add_sheaf_spec
     cring0.mult_sheaf_spec cring0.zero_sheaf_spec
     cring0.one_sheaf_spec (\<lambda>\<pp>\<in>Spec. undefined)
     (\<lambda>U. \<lambda>s\<in>cring0.sheaf_spec U. 0)"
      by (meson equals0D morphism_locally_ringed_spaces_axioms.intro)
  qed 
qed

lemma empty_scheme_is_scheme:
  shows "scheme {0::nat} (\<lambda>x y. 0) (\<lambda>x y. 0) 0 0 {} (\<lambda>U. U={}) (\<lambda>U. {0}) (\<lambda>U V. identity{0::nat}) 0 (\<lambda>U x y. 0) (\<lambda>U x y. 0) (\<lambda>U. 0) (\<lambda>U. 0)"
  by (metis comp_affine_scheme.comp_affine_scheme_is_scheme empty_scheme_is_comp_affine_scheme)

end