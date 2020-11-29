theory Comm_Ring_Theory
  imports "Jacobson_Basic_Algebra.Ring_Theory"

begin

section \<open>Commutative Rings\<close>

locale comm_ring = ring R "(+)" "(\<cdot>)" "\<zero>" "\<one>" 
  for R and addition (infixl "+" 65) and multiplication (infixl "\<cdot>" 70) and zero ("\<zero>") and unit ("\<one>") +
  assumes commutative_mult: "\<lbrakk> a \<in> R; b \<in> R \<rbrakk> \<Longrightarrow> a \<cdot> b = b \<cdot> a"

(* def 0.13 *)
definition (in ring) zero_divisor :: "'a \<Rightarrow> 'a \<Rightarrow> bool" 
  where "zero_divisor x y \<equiv> (x \<noteq> \<zero>) \<and> (y \<noteq> \<zero>) \<and> (x \<cdot> y = \<zero>)"

(* def 0.14 *)
locale entire_ring = comm_ring + assumes units_neq: "\<one> \<noteq> \<zero>" and 
no_zero_divisors: "\<lbrakk> x \<in> R; y \<in> R\<rbrakk> \<Longrightarrow> \<not>(zero_divisor x y)"

begin

(* ex. 0.16 *)
lemma shows "ideal R R (+) (\<cdot>) \<zero> \<one>" sorry 

lemma shows "ideal {\<zero>} R (+) (\<cdot>) \<zero> \<one>" sorry

(* ex. 0.17 *)
lemma 
  assumes "ideal \<aa> R (+) (\<cdot>) \<zero> \<one>" and "ideal \<bb> R (+) (\<cdot>) \<zero> \<one>"
  shows "ideal {x. \<exists>a b. x = a \<cdot> b \<and> a \<in> \<aa> \<and> b \<in> \<bb>} R (+) (\<cdot>) \<zero> \<one>" sorry

end (* entire_ring *)

(* def. 0.18, see remark 0.20 *)
locale prime_ideal = entire_ring R "(+)" "(\<cdot>)" "\<zero>" "\<one>" + ideal I  R "(+)" "(\<cdot>)" "\<zero>" "\<one>" 
  for R and addition (infixl "+" 65) and multiplication (infixl "\<cdot>" 70) and zero ("\<zero>") and unit ("\<one>") 
and I + 
assumes carrier_neq: "I \<noteq> R" and absorbent: "\<lbrakk>x \<in> R; y \<in> R\<rbrakk> \<Longrightarrow> (x \<cdot> y \<in> I) \<Longrightarrow> (x \<in> I \<or> y \<in> I)"

begin

(* remark 0.21 *)
lemma shows "\<one> \<notin> I" sorry

(* no_notation additive.inverse ("- _" [66] 65) *)

(* ex. 0.22 *)
lemma
  assumes "S = {x \<in> R. x \<notin> I}"
  shows "submonoid R S (\<cdot>) \<one>" sorry

end


end