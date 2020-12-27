theory Set_Further_Theory
  imports "Jacobson_Basic_Algebra.Set_Theory"

begin

section \<open>Sets\<close>

definition complement_in_of:: "'a set \<Rightarrow> 'a set \<Rightarrow> 'a set" ("_\<setminus>_")
  where "A \<setminus> B \<equiv> {x. x \<in> A \<and> x \<notin> B}"

section \<open>Functions\<close>

definition preimage:: "('a \<Rightarrow> 'b) \<Rightarrow> 'b set \<Rightarrow> 'a set" ("_ \<^sup>\<inverse> _")
  where "f\<^sup>\<inverse> V \<equiv> {x. f x \<in> V}"

definition inverse_map:: "('a \<Rightarrow> 'b) \<Rightarrow> 'a set \<Rightarrow> 'b set \<Rightarrow> ('b \<Rightarrow> 'a)" ("_\<^sup>\<inverse> _ _")
  where "f\<^sup>\<inverse> S T \<equiv> restrict (inv_into S f) T"

lemma
  assumes "bijective_map f S T"
  shows "bijective_map (f\<^sup>\<inverse> S T) T S"
  sorry

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