theory Comm_Ring_Theory
  imports "Jacobson_Basic_Algebra.Ring_Theory"

begin

section \<open>Commutative Rings\<close>

locale comm_ring = ring R "(+)" "(\<cdot>)" "\<zero>" "\<one>" 
  for R and addition (infixl "+" 65) and multiplication (infixl "\<cdot>" 70) and zero ("\<zero>") and unit ("\<one>") +
  assumes commutative_mult: "\<lbrakk> a \<in> R; b \<in> R \<rbrakk> \<Longrightarrow> a \<cdot> b = b \<cdot> a"


end