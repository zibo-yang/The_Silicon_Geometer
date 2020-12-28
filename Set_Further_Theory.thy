theory Set_Further_Theory
  imports "Jacobson_Basic_Algebra.Set_Theory"

begin

section \<open>Sets\<close>

abbreviation complement_in_of:: "'a set \<Rightarrow> 'a set \<Rightarrow> 'a set" ("_\<setminus>_" [65,65]65)
  where "A \<setminus> B \<equiv> A-B"

section \<open>Functions\<close>

abbreviation preimage:: "('a \<Rightarrow> 'b) \<Rightarrow> 'b set \<Rightarrow> 'a set" (infixr " \<^sup>\<inverse>" 90)
  where "f\<^sup>\<inverse> V \<equiv> vimage f V"

definition inverse_map:: "('a \<Rightarrow> 'b) \<Rightarrow> 'a set \<Rightarrow> 'b set \<Rightarrow> ('b \<Rightarrow> 'a)" ("_\<^sup>\<inverse>")
  where "f\<^sup>\<inverse> S T \<equiv> restrict (inv_into S f) T"

lemma bijective_map_preimage:
  assumes "bijective_map f S T"
  shows "bijective_map (f\<^sup>\<inverse> S T) T S"
proof
  show "f\<^sup>\<inverse> S T \<in> T \<rightarrow>\<^sub>E S"
    by (simp add: assms bij_betw_imp_funcset bij_betw_inv_into bijective.bijective bijective_map.axioms(2) inverse_map_def)
  show "bij_betw (f\<^sup>\<inverse> S T) T S"
    using assms by (simp add: bij_betw_inv_into bijective_def bijective_map_def inverse_map_def)
qed

lemma comp_maps:
  assumes "Set_Theory.map \<eta> A B" and "Set_Theory.map \<theta> B C"
  shows "Set_Theory.map (\<theta> \<circ> \<eta>) A C"
proof-
  have "\<theta> \<circ> \<eta> \<in> A \<rightarrow>\<^sub>E C"
  proof-
    have "\<theta> \<circ> \<eta> \<in> A \<rightarrow> C" using assms by (metis comp_apply funcsetI map.map_closed)
    moreover have "\<theta> \<circ> \<eta> \<in> extensional A" sorry
    ultimately show ?thesis by (simp add: PiE_def)
  qed
  thus ?thesis by (simp add: Set_Theory.map_def)
qed

end