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

context affine_scheme
begin

interpretation cis:cxt_ind_sheaf X is_open "\<O>\<^sub>X" \<rho> b add_str mult_str zero_str one_str X
  by (simp add: cxt_ind_sheaf_axioms_def cxt_ind_sheaf_def sheaf_of_rings_axioms)

interpretation it: ind_topology X is_open X by simp

interpretation pr': presheaf_of_rings X it.ind_is_open cis.ind_sheaf cis.ind_ring_morphisms b 
cis.ind_add_str cis.ind_mult_str cis.ind_zero_str cis.ind_one_str
  using cis.ind_sheaf_is_presheaf by simp

lemma eq_ind_is_open:
  shows "\<And>U. is_open U = it.ind_is_open U" 
  using ind_is_open_iff_open open_imp_subset by auto

lemma eq_ind_sheaf:
  shows "\<And>V. V \<subseteq> X \<Longrightarrow> \<O>\<^sub>X V = cis.ind_sheaf V" 
  using cxt_ind_sheaf.ind_sheaf_def
  by (metis cxt_ind_sheaf_axioms_def cxt_ind_sheaf_def inf_absorb2 open_space sheaf_of_rings_axioms)

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
  shows "\<And>x U. (U \<in> neighborhoods x) = (U \<in> pr'.neighborhoods x)" 
  using eq_ind_is_open by (simp add: neighborhoods_def pr'.neighborhoods_def)

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


(*
lemma eq_belongs_stalk_at:
  assumes "x \<in> X"
  shows "\<And>a. (a \<in> stalk_at x) = (a \<in> pr'.stalk_at x)" 
  using assms eq_neighborhoods eq_ind_sheaf eq_ind_ring_morphisms sorry

lemma eq_add_stalk_at:
  assumes "x \<in> X" and "it.ind_is_open U" and "x \<in> U" and "a \<in> pr'.stalk_at x" and 
"c \<in> pr'.stalk_at x" 
shows "(pr'.add_stalk_at x a c \<in> pr'.stalk_at x) = (add_stalk_at x a c \<in> stalk_at x)"
  using assms sorry
*)

lemma affine_scheme_lrs_axioms:
  shows "locally_ringed_space_axioms it.ind_is_open cis.ind_sheaf cis.ind_ring_morphisms
     cis.ind_add_str cis.ind_mult_str cis.ind_zero_str cis.ind_one_str"
proof
  show "\<And>x U a b.
       x \<in> U \<Longrightarrow>
       it.ind_is_open U \<Longrightarrow>
       a \<in> pr'.stalk_at x \<Longrightarrow> b \<in> pr'.stalk_at x \<Longrightarrow> pr'.add_stalk_at x a b \<in> pr'.stalk_at x"
    using pr'.stalk_is_ring unfolding ring_def
    by (meson Group_Theory.group_def abelian_group_def monoid.composition_closed)
next
  show "\<And>x U. x \<in> U \<Longrightarrow> it.ind_is_open U \<Longrightarrow> pr'.zero_stalk_at x U \<in> pr'.stalk_at x"
    using pr'.stalk_is_ring unfolding ring_def
    by (simp add: Group_Theory.group_def Group_Theory.monoid_def abelian_group_def)
next
  show "\<And>x U a b c.
       x \<in> U \<Longrightarrow>
       it.ind_is_open U \<Longrightarrow>
       a \<in> pr'.stalk_at x \<Longrightarrow>
       b \<in> pr'.stalk_at x \<Longrightarrow>
       c \<in> pr'.stalk_at x \<Longrightarrow>
       pr'.add_stalk_at x (pr'.add_stalk_at x a b) c =
       pr'.add_stalk_at x a (pr'.add_stalk_at x b c)" 
    using pr'.stalk_is_ring unfolding ring_def
    by (simp add: Group_Theory.group_def Group_Theory.monoid_def abelian_group_def)
next
  show "\<And>x U a.
       x \<in> U \<Longrightarrow>
       it.ind_is_open U \<Longrightarrow>
       a \<in> pr'.stalk_at x \<Longrightarrow> pr'.add_stalk_at x (pr'.zero_stalk_at x U) a = a"
using pr'.stalk_is_ring unfolding ring_def
  by (meson Group_Theory.group_def abelian_group_def monoid.left_unit)
next
  show "\<And>x U a.
       x \<in> U \<Longrightarrow>
       it.ind_is_open U \<Longrightarrow>
       a \<in> pr'.stalk_at x \<Longrightarrow> pr'.add_stalk_at x a (pr'.zero_stalk_at x U) = a"
using pr'.stalk_is_ring unfolding ring_def
  by (meson Group_Theory.group_def abelian_group_def monoid.right_unit)
next
show "\<And>x U u.
       x \<in> U \<Longrightarrow>
       it.ind_is_open U \<Longrightarrow>
       u \<in> pr'.stalk_at x \<Longrightarrow>
       monoid.invertible (pr'.stalk_at x) (pr'.add_stalk_at x) (pr'.zero_stalk_at x U) u"
  using pr'.stalk_is_ring unfolding ring_def abelian_group_def by (simp add: group.invertible)
next
  show "\<And>x U xa y.
       x \<in> U \<Longrightarrow>
       it.ind_is_open U \<Longrightarrow>
       xa \<in> pr'.stalk_at x \<Longrightarrow>
       y \<in> pr'.stalk_at x \<Longrightarrow> pr'.add_stalk_at x xa y = pr'.add_stalk_at x y xa"
using pr'.stalk_is_ring unfolding ring_def abelian_group_def
  by (meson commutative_monoid.commutative)
next
  show "\<And>x U a b.
       x \<in> U \<Longrightarrow>
       it.ind_is_open U \<Longrightarrow>
       a \<in> pr'.stalk_at x \<Longrightarrow> b \<in> pr'.stalk_at x \<Longrightarrow> pr'.mult_stalk_at x a b \<in> pr'.stalk_at x"
using pr'.stalk_is_ring unfolding ring_def
  by (meson monoid.composition_closed)
next
  show "\<And>x U. x \<in> U \<Longrightarrow> it.ind_is_open U \<Longrightarrow> pr'.one_stalk_at x U \<in> pr'.stalk_at x"
using pr'.stalk_is_ring unfolding ring_def
  by (simp add: Group_Theory.monoid_def)
next
  show "\<And>x U a b c.
       x \<in> U \<Longrightarrow>
       it.ind_is_open U \<Longrightarrow>
       a \<in> pr'.stalk_at x \<Longrightarrow>
       b \<in> pr'.stalk_at x \<Longrightarrow>
       c \<in> pr'.stalk_at x \<Longrightarrow>
       pr'.mult_stalk_at x (pr'.mult_stalk_at x a b) c =
       pr'.mult_stalk_at x a (pr'.mult_stalk_at x b c)"
using pr'.stalk_is_ring unfolding ring_def
  by (meson monoid.associative)
next
  show "\<And>x U a.
       x \<in> U \<Longrightarrow>
       it.ind_is_open U \<Longrightarrow>
       a \<in> pr'.stalk_at x \<Longrightarrow> pr'.mult_stalk_at x (pr'.one_stalk_at x U) a = a"
using pr'.stalk_is_ring unfolding ring_def
  by (meson monoid.left_unit)
next
  show "\<And>x U a.
       x \<in> U \<Longrightarrow>
       it.ind_is_open U \<Longrightarrow>
       a \<in> pr'.stalk_at x \<Longrightarrow> pr'.mult_stalk_at x a (pr'.one_stalk_at x U) = a"
using pr'.stalk_is_ring unfolding ring_def
  by (meson monoid.right_unit)
next
  show "\<And>x U a b c.
       x \<in> U \<Longrightarrow>
       it.ind_is_open U \<Longrightarrow>
       a \<in> pr'.stalk_at x \<Longrightarrow>
       b \<in> pr'.stalk_at x \<Longrightarrow>
       c \<in> pr'.stalk_at x \<Longrightarrow>
       pr'.mult_stalk_at x a (pr'.add_stalk_at x b c) =
       pr'.add_stalk_at x (pr'.mult_stalk_at x a b) (pr'.mult_stalk_at x a c)"
using pr'.stalk_is_ring unfolding ring_def
  by (simp add: ring_axioms_def)
next
  show "\<And>x U a b c.
       x \<in> U \<Longrightarrow>
       it.ind_is_open U \<Longrightarrow>
       a \<in> pr'.stalk_at x \<Longrightarrow>
       b \<in> pr'.stalk_at x \<Longrightarrow>
       c \<in> pr'.stalk_at x \<Longrightarrow>
       pr'.mult_stalk_at x (pr'.add_stalk_at x b c) a =
       pr'.add_stalk_at x (pr'.mult_stalk_at x b a) (pr'.mult_stalk_at x c a)"
using pr'.stalk_is_ring unfolding ring_def
  by (simp add: ring_axioms_def)
next
  show "\<And>x U a b.
       x \<in> U \<Longrightarrow>
       it.ind_is_open U \<Longrightarrow>
       a \<in> pr'.stalk_at x \<Longrightarrow>
       b \<in> pr'.stalk_at x \<Longrightarrow> pr'.mult_stalk_at x a b = pr'.mult_stalk_at x b a"
    using pr'.stalk_is_ring unfolding ring_def sorry
next
  show "\<And>x U I J.
       x \<in> U \<Longrightarrow>
       it.ind_is_open U \<Longrightarrow>
       max_ideal (pr'.stalk_at x) I (pr'.add_stalk_at x) (pr'.mult_stalk_at x)
        (pr'.zero_stalk_at x U) (pr'.one_stalk_at x U) \<Longrightarrow>
       max_ideal (pr'.stalk_at x) J (pr'.add_stalk_at x) (pr'.mult_stalk_at x)
        (pr'.zero_stalk_at x U) (pr'.one_stalk_at x U) \<Longrightarrow>
       I = J"
    using eq_stalk eq_add_stalk eq_mult_stalk eq_zero_stalk eq_one_stalk
    by (smt eq_ind_is_open in_mono is_local_ring local_ring.is_unique open_imp_subset)
next
  show "\<And>x U. x \<in> U \<Longrightarrow>
           it.ind_is_open U \<Longrightarrow>
           \<exists>\<ww>. max_ideal (pr'.stalk_at x) \<ww> (pr'.add_stalk_at x) (pr'.mult_stalk_at x)
                 (pr'.zero_stalk_at x U) (pr'.one_stalk_at x U)" 
    using eq_stalk eq_add_stalk eq_mult_stalk eq_zero_stalk eq_one_stalk
    by (smt eq_ind_is_open in_mono is_local_ring local_ring.has_max_ideal open_imp_subset) 
qed

lemma affine_scheme_as_axioms:
  shows "affine_scheme_axioms X it.ind_is_open cis.ind_sheaf cis.ind_ring_morphisms b cis.ind_add_str
     cis.ind_mult_str cis.ind_zero_str cis.ind_one_str R (+) (\<cdot>) \<zero> \<one>"
  sorry

lemma affine_scheme_is_scheme:
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
  proof-
    fix x assume "x \<in> X"
    have "affine_scheme X it.ind_is_open cis.ind_sheaf cis.ind_ring_morphisms b cis.ind_add_str cis.ind_mult_str
              (cis.ind_zero_str) (cis.ind_one_str) R (+) (\<cdot>) \<zero> \<one>"
    proof (intro_locales)
      show "sheaf_of_rings_axioms X it.ind_is_open cis.ind_sheaf cis.ind_ring_morphisms cis.ind_zero_str"
        by (meson cis.ind_sheaf_is_sheaf sheaf_of_rings_def)
    next
      show "locally_ringed_space_axioms it.ind_is_open cis.ind_sheaf cis.ind_ring_morphisms
     cis.ind_add_str cis.ind_mult_str cis.ind_zero_str cis.ind_one_str"
        using affine_scheme_lrs_axioms by simp
    next
      show "affine_scheme_axioms X it.ind_is_open cis.ind_sheaf cis.ind_ring_morphisms b cis.ind_add_str
     cis.ind_mult_str cis.ind_zero_str cis.ind_one_str R (+) (\<cdot>) \<zero> \<one>"
        using affine_scheme_as_axioms by simp
    qed
    thus "\<exists>U. x \<in> U \<and> is_open U \<and>
             affine_scheme U (ind_topology.ind_is_open X is_open U)
              (cxt_ind_sheaf.ind_sheaf \<O>\<^sub>X U) (cxt_ind_sheaf.ind_ring_morphisms \<rho> U) b
              (cxt_ind_sheaf.ind_add_str add_str U) (cxt_ind_sheaf.ind_mult_str mult_str U)
              (cxt_ind_sheaf.ind_zero_str zero_str U) (cxt_ind_sheaf.ind_one_str one_str U) R (+)
              (\<cdot>) \<zero> \<one>"
      using \<open>x \<in> X\<close> by blast
  qed
qed

end (* affine_scheme *)

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