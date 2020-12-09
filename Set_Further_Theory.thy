theory Set_Further_Theory
  imports "Jacobson_Basic_Algebra.Set_Theory"

begin

definition complement_in_of:: "'a set \<Rightarrow> 'a set \<Rightarrow> 'a set" ("_\<setminus>_")
  where "A \<setminus> B \<equiv> {x. x \<in> A \<and> x \<notin> B}"

end