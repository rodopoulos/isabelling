theory CS_Chap3

  imports Main

begin
type_synonym vname = string
datatype aexp = N int | V vname | Plus aexp aexp

type_synonym val = int
type_synonym state = "vname \<Rightarrow> val"

fun aval :: "aexp \<Rightarrow> state \<Rightarrow> val" where
  "aval (N n) s = n" |
  "aval (V x) s = s x" |
  "aval (Plus a1 a2) s = aval a1 s + aval a2 s"

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

fun plus :: "aexp \<Rightarrow> aexp \<Rightarrow> aexp" where
  "plus (N i1) (N i2) = N (i1 + i2)" |
  "plus a (N i) = (if i=0 then a else Plus a (N i))" |
  "plus (N i) a = (if i=0 then a else Plus (N i) a)" |
  "plus a1 a2 = Plus a1 a2"

lemma aval_plus [simp] : "aval (plus a1 a2) s = aval a1 s + aval a2 s"
  apply (induction rule: plus.induct)
  apply (auto)
  done

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


(* EXERCISE 3. *)


(* EXERCISE 3. *)


(* EXERCISE 3. *)


(* EXERCISE 3. *)


(* EXERCISE 3. *)


(* EXERCISE 3. *)


end