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
(*
  Instead of important and extending the AExp theory, let's just create
  our own types,  adding the letter t, of times, at the end
  of our constructors. Seems more portable.
*)
datatype aexpt = Nt int 
  | Vt vname 
  | Plust aexpt aexpt
  | Times aexpt aexpt

fun avalt :: "aexpt \<Rightarrow> state \<Rightarrow> val" where
  "avalt (Nt n) s = n" |
  "avalt (Vt x) s = s x" |
  "avalt (Plust a1 a2) s = avalt a1 s + avalt a2 s" |
  "avalt (Times a1 a2) s = avalt a1 s * avalt a2 s "

fun plust :: "aexpt \<Rightarrow> aexpt \<Rightarrow> aexpt" where
  "plust (Nt n1) (Nt n2) = Nt (n1 + n2)" |
  "plust (Nt n) a = (if n = 0 then a else Plust (Nt n) a)" |
  "plust a (Nt n) = (if n = 0 then a else Plust a (Nt n))" |
  "plust a1 a2 = Plust a1 a2"

fun times :: "aexpt \<Rightarrow> aexpt \<Rightarrow> aexpt" where
  "times (Nt n1) (Nt n2) = Nt (n1 * n2)" |
  "times (Nt n) a = 
    (if n = 1 then a else
    if n = 0 then (Nt 0) else
    Times (Nt n) a)" |
  "times a (Nt n) =  
    (if n = 0 then (Nt 0) else
    if n = 1 then a else
    Times a (Nt n))" |
  "times a1 a2 = Times a1 a2"

fun asimpt :: "aexpt \<Rightarrow> aexpt" where
  "asimpt (Nt n) = Nt n" |
  "asimpt (Vt v) = Vt v" |
  "asimpt (Plust a1 a2) = plust (asimpt a1) (asimpt a2)" |
  "asimpt (Times a1 a2) = times (asimpt a1) (asimpt a2)"

lemma avalt_plust [simp] : "avalt (plust a1 a2) s = avalt a1 s + avalt a2 s"
  apply (induction rule: plust.induct)
  apply (auto)
  done

lemma avalt_times [simp] : "avalt (times a1 a2) s = avalt a1 s * avalt a2 a"
  apply (induction rule: times.induct)
  apply (auto)
  done

theorem "avalt (asimpt a) s = avalt a s"
  apply (induction a)
  apply (auto)
  done


(* EXERCISE 3.5 *)
datatype aexp2 = N2 int 
  | V2 vname 
  | Plus2 aexp2 aexp2
  | PostPlus vname
  | Times2 aexp2 aexp2
  | Div2 aexp2 aexp2

fun aval2 :: "aexp2 \<Rightarrow> state \<Rightarrow> (val \<times> state)" where
  "aval2 (N2 n) s = (n, s)" |
  "aval2 (V2 x) s = (s x, s)" |
  "aval2 (Plus2 a1 a2) s = (fst (aval2 a1 s) + fst (aval2 a2 s), 
    (\<lambda> x. (snd (aval2 a1 s) x) + (snd (aval2 a2 s) x) - (s x)))" |
  "aval2 (Times2 a1 a2) s = (fst (aval2 a1 s) * fst (aval2 a2 s), 
    (\<lambda> x. (snd (aval2 a1 s) x) * (snd (aval2 a2 s) x) - (s x)))" |
  "aval2 (Div2 a1 a2) s = (fst (aval2 a1 s) div fst (aval2 a2 s), 
    (\<lambda> x. (snd (aval2 a1 s) x) div (snd (aval2 a2 s) x) - (s x)))" |
  "aval2 (PostPlus x) s = (s x, s(x:= 1 + s x))"


(* EXERCISE 3.6 *)


(* EXERCISE 3.7 *)


end