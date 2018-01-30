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


(* EXERCISE 4.4 *)
inductive iter :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
  izero: "iter r 0 x x" |
  istep: "r x y \<Longrightarrow> iter r n y z \<Longrightarrow> iter r (n+1) x z"

theorem "star r x y \<Longrightarrow> \<exists> n. iter r n x y"
  apply (induction rule: star.induct)
  apply (auto intro: izero istep)
  done


(* EXERCISE 4.5 *)
datatype alpha = a | b

inductive S :: "alpha list \<Rightarrow> bool" where
  s1: "S []" |
  s2: "S w \<Longrightarrow> S (a # w @ [b])" |
  s3: "\<lbrakk>S w1; S w2\<rbrakk> \<Longrightarrow> S (w1 @ w2)"

inductive T :: "alpha list \<Rightarrow> bool" where
  t1: "T []" |
  t2: "\<lbrakk>T w1; T w2\<rbrakk> \<Longrightarrow> T(w1 @ a # w2 @ [b])"

lemma T_to_s3 : "\<lbrakk>T w2; T w1\<rbrakk> \<Longrightarrow> T (w1 @ w2)"
  apply (induction rule: T.induct)
  apply (simp)
  apply (metis t2 append_assoc)
  done

(* 
  Here, the subgoals are complexer.
  
  We use t1 rule to kill the subgoal concerning the empty string
  The lemma above kills the subgoal about the appending operation. 
  However, this raises the problem of s2. For that, we use Metis in
  rules t1 and t2, in addition to Nil constant.
  
  We are basically saying that T can produce strings that S also can. 
*)
theorem S_to_T: "S w \<Longrightarrow> T w"
  apply (induction rule: S.induct)
    apply (simp add: t1)
  apply (metis t1 t2 append_Nil)
  apply (auto intro: T_to_s3)
  done

(* 
  All subgoals here claims for S rules.
  Hence, this theorem goes easily with them. 
*)
theorem T_to_S : "T w \<Longrightarrow> S w"
  apply (induction rule: T.induct)
  apply (auto intro: s1 s2 s3)
  done

(* If we proved that T w \<Longrightarrow> S w and S w \<Longrightarrow> T w, then T w = S w! *)
corollary "S w = T w"
  apply (auto simp add: T_to_S S_to_T)
  done

end