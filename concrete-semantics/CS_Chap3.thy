theory CS_Chap3

imports Main
  "~~/src/HOL/IMP/BExp"

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

(* We have now the Times case. Pretty trivial! *)
fun avalt :: "aexpt \<Rightarrow> state \<Rightarrow> val" where
  "avalt (Nt n) s = n" |
  "avalt (Vt x) s = s x" |
  "avalt (Plust a1 a2) s = avalt a1 s + avalt a2 s" |
  "avalt (Times a1 a2) s = avalt a1 s * avalt a2 s "

(* plust definition follows equal as our previous plus function *)
fun plust :: "aexpt \<Rightarrow> aexpt \<Rightarrow> aexpt" where
  "plust (Nt n1) (Nt n2) = Nt (n1 + n2)" |
  "plust (Nt n) a = (if n = 0 then a else Plust (Nt n) a)" |
  "plust a (Nt n) = (if n = 0 then a else Plust a (Nt n))" |
  "plust a1 a2 = Plust a1 a2"

(* In multiplication, we have 2 special cases: null factor (zero) and neutral factor (one) *)
fun times :: "aexpt \<Rightarrow> aexpt \<Rightarrow> aexpt" where
  "times (Nt n1) (Nt n2) = Nt (n1 * n2)" |
  "times (Nt n) a = 
    (if n = 0 then (Nt 0) else
    if n = 1 then a else
    Times (Nt n) a)" |
  "times a (Nt n) =  
    (if n = 0 then (Nt 0) else
    if n = 1 then a else
    Times a (Nt n))" |
  "times a1 a2 = Times a1 a2"

(* Let's test times *)
value "times (Nt 3) (Nt 4)" (* = 12 | Ok*)
value "times (Nt 3) (Nt 0)" (* = 0 | Ok*)
value "times (Nt 3) (Nt 1)" (* = 3 | Ok*)
value "times (Nt 0) (Nt 4)" (* = 0 | Ok*)
value "times (Nt 1) (Nt 4)" (* = 4 | Ok*)
value "times (Add (Nt 3) (Nt 2)) (Nt 4)" (* = aexpt | Ok*)
value "times (Nt 4) (Add (Nt 3) (Nt 2))" (* = aexpt | Ok*)
value "times (Add (Nt 3) (Nt 2)) (Add (Nt 3) (Nt 2))" (* = aexpt | Ok*)

(* Times case is added to our simplification function *)
fun asimpt :: "aexpt \<Rightarrow> aexpt" where
  "asimpt (Nt n) = Nt n" |
  "asimpt (Vt v) = Vt v" |
  "asimpt (Plust a1 a2) = plust (asimpt a1) (asimpt a2)" |
  "asimpt (Times a1 a2) = times (asimpt a1) (asimpt a2)"

(* Proving that plust function has distributive properties *)
lemma avalt_plust [simp] : "avalt (plust a1 a2) s = avalt a1 s + avalt a2 s"
  apply (induction a1 a2 rule: plust.induct)
  apply (simp_all)
  done

(* Proving that times function has distributive properties *)
lemma avalt_times [simp] : "avalt (times a1 a2) s = avalt a1 s * avalt a2 s"
  apply (induction a1 a2 rule: times.induct)
  apply (auto)
  done

(* Finally, proving that our simplification function is correct *)
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
datatype lexp = Nl int
  | Vl vname
  | Plusl lexp lexp
  | LET vname lexp lexp

(* 
  Now, for a proper avaliation, we need to implement the LET aval. 
  Basically, this means that we need to replace the ocurrence of 
  variable x in a2 by expression a1.
*)
fun lval :: "lexp \<Rightarrow> state \<Rightarrow> int" where
  "lval (Nl n) s = n" |
  "lval (Vl x) s = s x" |
  "lval (Plusl a1 a2) s = lval a1 s + lval a2 s" |
  "lval (LET x a1 a2) s = lval a2 (s(x := lval a1 s))"

value "lval (Vl x) (s 5)" 
value "lval (LET v (Plusl (Nl 1) (Nl 2)) (Plusl (Nl 5) (Vl v))) s" (* It works *)

(*
  Here we want to transform an lexp expression into an aexp one.
  Pretty straighforward for int and variables. Addition is done
  recursively. For the LET constructor, we just use our subst function,
  which already apply the variable value over an aexp expression, with
  recursion over the expression parameters.
  Piece of cake!
*)
fun inline :: "lexp \<Rightarrow> aexp" where
  "inline (Nl n) = N n" | 
  "inline (Vl x) = V x" | 
  "inline (Plusl a1 a2) = Plus (inline a1) (inline a2)" | 
  "inline (LET x a1 a2) = subst x (inline a1) (inline a2)" 

(* 
  Proving that inline function is correct is proving that we 
  can correctly evaluate the resulting expression. 
*)
theorem inline_correctness : "lval l s = aval (inline l) s"
  apply (induction l arbitrary: s)
  apply auto
  done


(* EXERCISE 3.7 *)
(* Extensions can be done with definitions *)
definition Le :: "AExp.aexp \<Rightarrow> AExp.aexp \<Rightarrow> bexp" where
  "Le a1 a2 = Not (Less a2 a1)"

definition Eq :: "AExp.aexp \<Rightarrow> AExp.aexp \<Rightarrow> bexp" where
  "Eq a1 a2 = And (Not (Less a1 a2)) (Not (Less a2 a1))"

(* Correctness of both operations is easy over definitions *)
theorem Le_correctness : "bval (Le a1 a2) s = (AExp.aval a1 s \<le> AExp.aval a2 s)"
  apply (auto simp add: Le_def)
  done

theorem Eq_correctness : "bval (Eq a1 a2) s = (AExp.aval a1 s = AExp.aval a2 s)"
  apply (auto simp add: Eq_def)
  done


(* EXERCISE 3.8 *)
datatype ifexp = Bi bool 
  | If ifexp ifexp ifexp 
  | Less2 AExp.aexp AExp.aexp

(* 
  The If statement should evaluate the first parameter and, based on that
  give the evaluation of the second or the third.
*)
fun ifval :: "ifexp \<Rightarrow> state \<Rightarrow> bool" where
  "ifval (Bi v) s = v" |
  "ifval (If a b c) s = (if (ifval a s) then (ifval b s) else (ifval c s))" |
  "ifval (Less2 a1 a2) s = (AExp.aval a1 s < AExp.aval a2 s)"

fun b2ifexp :: "bexp \<Rightarrow> ifexp" where
  "b2ifexp (Bc v) = Bi v" |
  "b2ifexp (Not b) = If (b2ifexp b) (Bi False) (Bi True)" |
  "b2ifexp (And b1 b2) = If (b2ifexp b1) (b2ifexp b2) (Bi False)" |
  "b2ifexp (Less a1 a2) = Less2 a1 a2" 

(* 
  What does If a b c means? (a \<and> b) \<or> (\<not>a \<and> c), right?
  But we need to get rid of that disjunction, since we don't have it.
  So we negate two times! \<not>\<not>((a \<and> b) \<or> (\<not>a \<and> c)), leading to:
  \<not>(\<not>(a \<and> b) \<and> \<not>(\<not>a \<and> c))
  
*)
fun if2bexp :: "ifexp \<Rightarrow> bexp" where
  "if2bexp (Bi v) = Bc v" |
  "if2bexp (If a b c) = Not( And 
    (Not ((And (if2bexp a) (if2bexp b)))) 
    (Not ((And (Not (if2bexp a)) (if2bexp c))))
  )" |
  "if2bexp (Less2 a1 a2) = Less a1 a2"

(* Proving correctness is proving that the resulting expression evaluates right *)
theorem b2ifexp_correctness : "ifval (b2ifexp e) s = bval e s"
  apply (induction e)
  apply auto
  done

theorem if2bexp_correctness : "bval (if2bexp e) s = ifval e s"
  apply (induction e)
  apply auto
  done


(* EXERCISE 3.9 *)
datatype pbexp = VAR vname
  | NOT pbexp
  | AND pbexp pbexp
  | OR pbexp pbexp

(* Evaluates an expression *)
fun pbval :: "pbexp \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> bool" where
  "pbval (VAR v) s = s v" |
  "pbval (NOT b) s = (\<not> pbval b s)" |
  "pbval (AND b1 b2) s = (pbval b1 s \<and> pbval b2 s)" |
  "pbval (OR b1 b2) s = (pbval b1 s \<or> pbval b2 s)"

(* Tells if the boolean expression is in the negative normal formula *)
fun is_nnf :: "pbexp \<Rightarrow> bool" where
  "is_nnf (VAR _) = True" |
  "is_nnf (NOT (VAR _)) = True" |
  "is_nnf (NOT _) = False" |
  "is_nnf (AND b1 b2) = (is_nnf b1 \<and> is_nnf b2)" |
  "is_nnf (OR b1 b2) = (is_nnf b1 \<or> is_nnf b2)" 

value "is_nnf (AND (VAR a) (NOT (VAR B)))"
value "is_nnf (OR (VAR a) (NOT (VAR B)))"
value "is_nnf (NOT (OR (VAR a) (NOT (VAR B))))"
value "is_nnf (NOT (AND (VAR a) (VAR B)))" (* It works! *)

fun nnf :: "pbexp \<Rightarrow> pbexp" where
  "nnf (VAR v) = VAR v" |
  "nnf (NOT (VAR v)) = NOT (VAR v)" |
  "nnf (NOT (NOT b)) = nnf b" |
  "nnf (NOT (AND b1 b2)) = OR (nnf (NOT b1)) (nnf (NOT b2))" |
  "nnf (NOT (OR b1 b2)) = AND (nnf (NOT b1)) (nnf (NOT b2))" |
  "nnf (AND b1 b2) = AND (nnf b1) (nnf b2)" |
  "nnf (OR b1 b2) = OR (nnf b1) (nnf b2)"

value "nnf (NOT (OR (VAR a) (VAR B)))" (* It works! *)

(* 
  Lemma nnf_correctness raises a subgoal, requiring to prove that
  we prove that the NOT operator properly negate an expression.
  So we prove it.  
*)
lemma negation_correctness [simp] : "pbval (nnf (NOT b)) s = (\<not> (pbval (nnf b) s))"
  apply (induction b)
  apply auto
  done

(* Here, the correctness follows easily. Induction is enough. *)
theorem nnf_correctness : "pbval (nnf b) s = pbval b s"
  apply (induction b)
  apply auto
  done

(* TODO: explain the induct rule *)
theorem is_nff_correctness : "is_nnf (nnf b)"
  apply (induction b rule: nnf.induct)
  apply auto
  done

end