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
  assumes are_affine_schemes: "\<And>x. x \<in> X \<Longrightarrow> (\<exists>U. x\<in>U \<and> is_open U \<and> U \<subseteq> X \<and> 
affine_scheme U (ind_topology.ind_is_open X is_open U) (cxt_ind_sheaf.ind_sheaf \<O>\<^sub>X U) 
(cxt_ind_sheaf.ind_ring_morphisms \<rho> U) b (cxt_ind_sheaf.ind_add_str add_str U)
(cxt_ind_sheaf.ind_mult_str mult_str U) (cxt_ind_sheaf.ind_zero_str zero_str U)
(cxt_ind_sheaf.ind_one_str one_str U) R (+) (\<cdot>) \<zero> \<one>)"

context affine_scheme
begin

lemma affine_scheme_is_scheme:
  shows "scheme X is_open \<O>\<^sub>X \<rho> b add_str mult_str zero_str one_str R (+) (\<cdot>) \<zero> \<one>"
proof (intro scheme.intro scheme_axioms.intro)
  show "locally_ringed_space X is_open \<O>\<^sub>X \<rho> b add_str mult_str zero_str one_str" by (simp add: locally_ringed_space_axioms)
next
  show "comm_ring R (+) (\<cdot>) \<zero> \<one>" by (simp add: local.comm_ring_axioms)
next
  show "\<And>x. x \<in> X \<Longrightarrow>
         \<exists>U. x \<in> U \<and> is_open U \<and> U \<subseteq> X \<and>
             affine_scheme U (ind_topology.ind_is_open X is_open U)
              (cxt_ind_sheaf.ind_sheaf \<O>\<^sub>X U) (cxt_ind_sheaf.ind_ring_morphisms \<rho> U) b
              (cxt_ind_sheaf.ind_add_str add_str U) (cxt_ind_sheaf.ind_mult_str mult_str U)
              (cxt_ind_sheaf.ind_zero_str zero_str U) (cxt_ind_sheaf.ind_one_str one_str U) R (+)
              (\<cdot>) \<zero> \<one>"
  proof-
    fix x assume "x \<in> X"
    then have "affine_scheme X (ind_topology.ind_is_open X is_open X)
              (cxt_ind_sheaf.ind_sheaf \<O>\<^sub>X X) (cxt_ind_sheaf.ind_ring_morphisms \<rho> X) b
              (cxt_ind_sheaf.ind_add_str add_str X) (cxt_ind_sheaf.ind_mult_str mult_str X)
              (cxt_ind_sheaf.ind_zero_str zero_str X) (cxt_ind_sheaf.ind_one_str one_str X) R (+)
              (\<cdot>) \<zero> \<one>"
      sorry
    thus "\<exists>U. x \<in> U \<and> is_open U \<and> U \<subseteq> X \<and>
             affine_scheme U (ind_topology.ind_is_open X is_open U)
              (cxt_ind_sheaf.ind_sheaf \<O>\<^sub>X U) (cxt_ind_sheaf.ind_ring_morphisms \<rho> U) b
              (cxt_ind_sheaf.ind_add_str add_str U) (cxt_ind_sheaf.ind_mult_str mult_str U)
              (cxt_ind_sheaf.ind_zero_str zero_str U) (cxt_ind_sheaf.ind_one_str one_str U) R (+)
              (\<cdot>) \<zero> \<one>"
      using \<open>x \<in> X\<close> by blast
  qed
qed

end (* affine_scheme*)

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
     (identity Spec) (\<lambda>U. identity \<O> U)"
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