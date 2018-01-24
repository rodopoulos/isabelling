theory CS_Chap4

imports Main

begin

(* EXERCISE 4.1 *)
datatype 'a tree = Tip | Node "'a tree" 'a "'a tree"

fun set :: "'a tree \<Rightarrow> 'a set" where
  "set Tip = {}" |
  "set (Node l x r) = set l \<union> {x} \<union> set r"

value "set (tree (Node (Node Tip 1 Tip) 2 (Node Tip 1 Tip)))"

(*
  A tree is ordered if all elements on the left 
  of the topmost element are smaller than it and
  all elements on his right are bigger than it.
*)
fun ord :: "int tree \<Rightarrow> bool" where
  "ord Tip = True" |
  "ord (Node l x r) = (
    (\<forall> a \<in> (set l). (a < x)) \<and> 
    (\<forall> b \<in> (set r). (b > x))
  )"

value "ord ((Node (Node Tip 1 Tip) 2 (Node Tip 1 Tip)))"
value "ord ((Node (Node Tip 1 Tip) 2 (Node Tip 3 Tip)))" 
(* It works! *)

fun ins :: "int \<Rightarrow> int tree \<Rightarrow> int tree" where
  "ins n Tip = (Node Tip n Tip)" |
  "ins n (Node l x r ) = (
    if n < x then Node (ins n l) x r
    else if n > x then Node l x (ins n r)
    else Node l x r
  )"

value "ins 1 ((Node (Node Tip 2 Tip) 3 (Node Tip 4 Tip)))"
value "ins 3 ((Node (Node Tip 2 Tip) 3 (Node Tip 4 Tip)))"
value "ins 5 ((Node (Node Tip 2 Tip) 3 (Node Tip 4 Tip)))" 
(* It works! *)

theorem ins_correctness_1 [simp] : "set(ins x t) = {x} \<union> set t"
  apply (induction t)
  apply (auto)
  done

theorem ins_correctness_2 : "ord t \<Longrightarrow> ord (ins n t)"
  apply (induction t)
  apply (auto)
  done

(* EXERCISE 4.2 *)
end