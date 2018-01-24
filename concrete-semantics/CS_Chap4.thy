theory CS_Chap4

imports Main "~~/src/HOL/IMP/Star"

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
(* Very trivial. Just follow exercise commands. *)
inductive palindrome :: "'a list \<Rightarrow> bool" where
  empt': "palindrome []" |
  sing': "palindrome [x]" |
  step': "palindrome xs \<Longrightarrow> palindrome (a # xs @ [a])"

theorem palindrome_reverse: "palindrome xs \<Longrightarrow> rev xs = xs"
  apply(induction rule: palindrome.induct)
  apply(simp_all)
  done


(* EXERCISE 4.3 *)
inductive star' :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" for r where
  refl' : "star' r x x" |
  step' : "star' r x y \<Longrightarrow> r y z \<Longrightarrow> star' r x z"

(* These two next lemmas are not required, but let's play a little with the definitions*)
lemma "star r x x \<Longrightarrow> star' r x x"
  apply (induction)
  apply (rule refl')
  apply (simp_all)
  done

lemma "star' r x x \<Longrightarrow> star r x x"
  apply (induction)
  apply (simp_all)
  done

(*
  Ok, now let's prove the first formula. 
  The lemma below is required for the subgoal left
  after we apply the reflection rule of star
*)
lemma star_trans: "star r x y \<Longrightarrow> r y z \<Longrightarrow> star r x z"
  apply (induction rule: star.induct)
  apply (auto intro: star.refl star.step)
  done

theorem  "star' r x y \<Longrightarrow> star r x y"
  apply (induction rule: star'.induct)
  apply (rule star.refl)
  apply (auto simp add: star_trans)
  done

(* As above, the theorem left a subgoal and we need this lemma *)
lemma star'_trans: "star' r y z \<Longrightarrow> r x y \<Longrightarrow> star' r x z"
  apply (induction rule: star'.induct)
  apply (auto intro: star'.refl' star'.step')
  done

theorem "star r x y \<Longrightarrow> star' r x y"
  apply (induction rule: star.induct)
  apply (auto simp add: star'_trans intro: star'.refl')
  done

end