theory CS_Chap3

  imports Main

begin
type_synonym vname = string
datatype aexp = N int | V vname | Plus aexp aexp

type_synonym val = int
type_synonym state = "vname \<Rightarrow> val"

(* 
  Given an expression and a state (variable value) it evaluates the primer
  giving the expression final value
*)
fun aval :: "aexp \<Rightarrow> state \<Rightarrow> val" where
  "aval (N n) s = n" |
  "aval (V x) s = s x" |
  "aval (Plus a1 a2) s = aval a1 s + aval a2 s"

(*
  Performs constant folding, i.e., reduces the expression, resolving
  trivial Plus operations
*)
fun asimp_const :: "aexp \<Rightarrow> aexp" where
  "asimp_const (N n) = N n" |
  "asimp_const (V x) = V x" |
  "asimp_const (Plus a1 a2) =
    (case (asimp_const a1, asimp_const a2) of 
      (N n1, N n2) \<Rightarrow> N (n1 + n2) |
      (b1, b2) \<Rightarrow> Plus b1 b2)"

lemma "aval (asimp_const a) s = aval a s"
  apply (induction a)
  apply (auto split: aexp.split)
  done

(*
  Plus operation optimization, intended to eliminate 0 and
  simplify trivial summations
*)
fun plus :: "aexp \<Rightarrow> aexp \<Rightarrow> aexp" where
  "plus (N i1) (N i2) = N (i1 + i2)" |
  "plus a (N i) = (if i=0 then a else Plus a (N i))" |
  "plus (N i) a = (if i=0 then a else Plus (N i) a)" |
  "plus a1 a2 = Plus a1 a2"

lemma aval_plus [simp] : "aval (plus a1 a2) s = aval a1 s + aval a2 s"
  apply (induction rule: plus.induct)
  apply (auto)
  done

(* Function for simplify expressions using the plus function *)
fun asimp :: "aexp \<Rightarrow> aexp" where
  "asimp (N n) = N n" |
  "asimp (V x) = V x" |
  "asimp (Plus a1 a2) = plus (asimp a1) (asimp a2)"

lemma "aval (asimp a) s = aval a s"
  apply (induction a)
  apply (auto)
  done

(* EXERCISE 3.1 *)
fun optimal :: "aexp \<Rightarrow> bool" where
  "optimal (N n) = True" |
  "optimal (V x) = True" |
  "optimal (Plus (N i) (N j)) = False" |
  "optimal (Plus a1 a2) = ((optimal a1) \<and> (optimal a2))"

theorem "optimal (asimp_const a)"
  apply (induction a)
  apply (auto split: aexp.split)
  done


(* EXERCISE 3.2 *)
(* Return the total summation of all constants in an expression *)
fun sumN :: "aexp \<Rightarrow> int" where
  "sumN (N n) = n" |
  "sumN (V x) = 0" |
  "sumN (Plus a1 a2) = sumN a1 + sumN a2"

value "sumN (Plus (N 1) (Plus (V x) (N 2)))" (* It works! *)

(* Giving an expression, return it with all constants replaced by zero *)
fun zeroN :: "aexp \<Rightarrow> aexp" where
  "zeroN (N n) = (N 0)" |
  "zeroN (V x) = (V x)" |
  "zeroN (Plus a1 a2) = Plus (zeroN a1) (zeroN a2)"

value "zeroN (Plus (N 1) (Plus (V x) (N 2)))" (* It works! *)

(* Transform a given expression in an addition of the sumN and zeroN of that expression*)
fun sepN :: "aexp \<Rightarrow> aexp" where
  "sepN a = Plus (N (sumN a)) (zeroN a)"

value "sepN (Plus (N 1) (Plus (V x) (N 2)))" (* It works! *)

lemma aval_sepN [simp] : "aval (sepN a) s = aval a s"
  apply (induction a)
  apply (auto)
  done

(* 
  Finally, for performing the full_asimp, we just simplify the expression as we can
  and then apply the sepN function, transforming it in an addition of the variable
  and resulting constant.
 *)
fun full_asimp :: "aexp \<Rightarrow> aexp" where
  "full_asimp a = asimp (sepN a)"

value "full_asimp (Plus (N 1) (Plus (V x) (N 2)))" (* It works *)

lemma aval_full_asimp: "aval (full_asimp a) s = aval a s"
  apply (induction a)
  apply (auto)
  done


(* EXERCISE 3.3 *)
fun subst :: "vname \<Rightarrow> aexp \<Rightarrow> aexp \<Rightarrow> aexp" where
  "subst x a (V v) = (if x = v then a else (V v))" |
  "subst x a (N n) = (N n)" |
  "subst x a (Plus a1 a2) = Plus (subst x a a1) (subst x a a2)"

value "subst ''x'' (N 3) (Plus (V ''x'') (V ''y''))" (* It works! *)

lemma substitution_lemma [simp]: "aval (subst x a e) s = aval e (s(x := aval a s))"
  apply (induction e)
  apply (auto)
  done

theorem "aval a1 s = aval a2 s \<Longrightarrow> aval (subst x a1 e) s = aval (subst x a2 e) s"
  apply (induction e)
  apply (auto)
  done


(* EXERCISE 3.4 *)


(* EXERCISE 3.5 *)


(* EXERCISE 3.6 *)


(* EXERCISE 3.7 *)


end