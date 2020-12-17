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

end