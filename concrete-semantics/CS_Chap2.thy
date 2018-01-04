theory CS_Chap2

  imports Main
    
begin

(* EXERCISE 2.1 *)
value "1 + (2::nat)"
value "1 + (2::int)"
value "1 - (2::nat)"
value "1 - (2::int)"


(* EXERCISE 2.2 *)
fun add :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "add 0 n = n" |
  "add (Suc m) n = Suc(add m n)"

lemma add_0 [simp]: "add m 0 = m"
  apply (induction m)
   apply auto
  done

lemma add_2 [simp]: "add m (Suc n) = Suc(add m n)"
  apply (induction m)
   apply (auto)
  done
    
theorem add_commutative: "add m n = add n m"
  apply (induction m)
  apply auto
  done
        
theorem add_associative: "add a (add b c) = add (add a b) c"
  apply (induction a)
   apply (auto)
  done

fun double:: "nat \<Rightarrow> nat" where
  "double 0 = 0" |
  "double (Suc n) = Suc(Suc(double n))"
    
lemma double_is_2add: "double n = add n n"
  apply (induction n)
   apply auto
  done

(* EXERCISE 2.3 *)
fun count:: "'a list \<Rightarrow> 'a \<Rightarrow> nat" where
  "count [] _ = 0" |
  "count (x # xs) n = 
    (if x = n then (Suc (count xs n))
    else count xs n)"

theorem "count xs n \<le> length xs"
  apply (induction xs)
  apply auto
  done


(* EXERCISE 2.4 *)
(* fun snoc: appends an element to the end of a list*)
fun snoc:: "'a list \<Rightarrow> 'a \<Rightarrow> 'a list" where
  "snoc [] x = x # []" |
  "snoc (x # xs) y = x # (snoc xs y)" 

value "snoc [a,b,c] d" (*it works!*)

(* 
  We have to prove that length after snoc function is correct,
  so, in reverse function, length is preserved
*)
lemma snoc_length_correctness [simp]: "length(snoc xs x) = Suc(length xs)"
  apply (induction xs)
   apply auto
  done
  
(* fun reverse: reverse a list recursively, using snoc *)  
fun reverse:: "'a list \<Rightarrow> 'a list" where
  "reverse [] = []" |
  "reverse (x # xs) = snoc (reverse xs) x"
  
value "reverse [a, b, c]" (* It works! *)

(* 
  Now we need this lemma due to show that reverse function preserve
  the order even with a snoc applied
*)
lemma reverse_preserve [simp]: "reverse (snoc xs x) = x # (reverse xs)"
  apply (induction xs)
  apply auto
  done

(* The theorem follows easily *)    
theorem "reverse (reverse xs) = xs"
  apply (induction xs)
   apply auto
  done
    
(* EXERCISE 2.5 *)
fun sum_upto:: "nat \<Rightarrow> nat" where
  "sum_upto 0 = 0" |
  "sum_upto n = n + sum_upto(n - 1)"
    
value "sum_upto 2"
value "sum_upto 5" (* It works! *)
  
theorem "sum_upto n = n * (n + 1) div 2"
  apply (induction n)
  apply auto
  done


(* EXERCISE 2.6 *)
datatype 'a tree = 
  Tip 
  | Node "'a tree" 'a "'a tree"

fun contents :: "'a tree \<Rightarrow> 'a list" where
  "contents Tip = []" |
  "contents (Node l x r) = contents l @ [x] @ contents r"

value "contents (tree 2)"
value "snoc (contents (tree 2 3 4)) 2" (* it works! *)

fun sumtree :: "nat tree \<Rightarrow> nat" where
  "sumtree Tip = 0" |
  "sumtree (Node l x r) = sumtree l + x + sumtree r"

fun sumlist :: "nat list \<Rightarrow> nat" where
  "sumlist [] = 0" |
  "sumlist (x # xs) = x + sumlist xs"

value "sumtree (tree 1 2 3)"
value "sumlist [1, 2, 3]" (* It works! *)

theorem "sumtree t = sum_list(contents t)"
  apply (induction t)
   apply auto
  done


(* EXERCISE 2.7 *)

(* The first rule tells to store values in leaves as well*)
datatype 'a tree2 = 
  Leaf 'a
  | Node "'a tree2" 'a "'a tree2"

fun mirror :: "'a tree2 \<Rightarrow> 'a tree2" where
  "mirror (Leaf x) = Leaf x" | 
  "mirror (Node l x r) = Node (mirror r) x (mirror l)"

lemma mirror_correctness [simp]: "mirror(mirror t) = t"
  apply (induction t)
   apply auto
  done

fun pre_order :: "'a tree2 \<Rightarrow> 'a list" where
  "pre_order (Leaf x) = [x]" |
  "pre_order (Node l x r) = x # pre_order l @ pre_order r"

fun post_order :: "'a tree2 \<Rightarrow> 'a list" where
  "post_order (Leaf x) = [x]" |
  "post_order (Node l x r) = post_order l @ post_order r @ [x]"

value "pre_order (tree2 1 2 3)"
value "post_order (tree2 1 2 3)"

theorem "pre_order(mirror t) = rev (post_order t)"
  apply (induction t)
   apply auto
  done


(* EXERCISE 2.8 *)
(* This is a nice example of the using multiple hashtags *)
fun intersperse :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "intersperse a [] = []" |
  "intersperse a (x # xs) = x # (a # intersperse a xs)"

theorem "map f (intersperse a xs) = intersperse (f a) (map f xs)"
  apply (induction xs)
  apply auto
  done 


(* EXERCISE 2.9 *)
(* 
  This function is tail-recursive: the induction step
  begins with the function itself.
*)
fun itadd :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "itadd 0 m = m" |
  "itadd (Suc m) n = itadd m (Suc n)"

value "itadd 1 2"
value "itadd 1 (itadd 1 1)" (* It works! *)

(* Arbitrary on n makes induction possible *)
theorem "itadd m n = add m n"
  apply (induction m arbitrary: n)
   apply auto
  done


(* EXERCISE 2.10 *)

datatype tree0 = Tip | Node tree0 tree0

fun nodes :: "tree0 \<Rightarrow> nat" where
  "nodes Tip = 1" |
  "nodes (Node l r) = 1 + nodes l + nodes r"

value "nodes (tree0 Node 1 2)" (* It works *)

fun explode :: "nat \<Rightarrow> tree0 \<Rightarrow> tree0" where
  "explode 0 t = t" |
  "explode (Suc n) t = explode n (Node t t)"

(* 
  A n-factor explode is equivalent to expanding your current tree in n levels.
  Hence, you are adding 2^i nodes for each i-th level. This is basic induction
  over tree height, resulting in 2^n - 1
*)
value "explode 0 (tree0 Tip)" (* = 1 *)
value "explode 1 (tree0 Tip)" (* = 3 *)
value "explode 2 (tree0 Tip)" (* = 7 *)
value "explode 3 (tree0 Tip)" (* = 15 *)

(*
  However, when your initial tree already has T nodes, where T = nodes t,
  you need to count and explode then as well. Therefore, we need to add
  the explosion on each subtree: 2^n * T.
*)
value "explode 0 (tree0 Node l r)" (* = 3 *)
value "explode 1 (tree0 Node l r)" (* = 7 *)
value "explode 2 (tree0 Node l r)" (* = 15 *)
value "explode 3 (tree0 Node l r)" (* = 31 *)

(* Adding the two parts, we have: N = 2^n * T + 2^n - 1 *)
theorem "nodes (explode n t) = 2^n * nodes t + 2^n - 1"
  apply (induction n arbitrary: t)
   apply (auto simp add:algebra_simps)
  done


(* EXERCISE 2.11 *)
datatype exp = Var
  | Const int
  | Add exp exp
  | Mult exp exp

(* 
  Note that this simply evaluates an expression and, 
  if it has and variable, replaces it by the second argument 
*)
fun eval :: "exp \<Rightarrow> int \<Rightarrow> int" where
  "eval Var n = n" |
  "eval (Const k) n = k" |
  "eval (Add a b) n = eval a n + eval b n" |
  "eval (Mult a b) n = eval a n * eval b n"

value "eval (Add (Const 2) (Const 4)) 1"
value "eval (Add (Var) (Const 4)) 1" 
value "eval (Add (Mult (Const 1) (Const 2)) Var) 2" (* It works! *)

(*
  In evalp, for each element on the list, we sum it with the product of n
  and the evalp with the rest of the list.
  The last iteration will always add 0.

  At the end, the expression will be composed by several products. If you
  transform them in operands, you will have the expected polynomial   
*)
fun evalp :: "int list \<Rightarrow> int \<Rightarrow> int" where
  "evalp [] n = 0" |
  "evalp (x # xs) n = x + n * evalp xs n" 

value "evalp [1, 2, 4] 1" (* It works! *)

(*
  coeffs function translates an expression into our polynomial-list form.
  This means we convert each term of the expression in a list item. Hence,
  an expression like Add (Mult (Const 1) (Const 2) Var) will
  be converted in []. For every possible expression element: 
  
  - For a constant k, we just add it to the list
  - For a variable, we
  - For an addition, we must sum all terms of the operands 
    resulting in a one Const element list
  - For a product, we apply the same logic of addition, but using multiplication
*)

fun sumexp :: "int list \<Rightarrow> int list \<Rightarrow> int list" where
  "sumexp [] xs = xs" |
  "sumexp xs [] = xs" |
  "sumexp (x # xs) (y # ys) = (x + y) # sumexp xs ys"

fun scalar_mult :: "int \<Rightarrow> int list \<Rightarrow> int list" where
  "scalar_mult n [] = []" |
  "scalar_mult n (x # xs) = n*x # scalar_mult n xs"

fun multexp :: "int list \<Rightarrow> int list \<Rightarrow> int list" where
  "multexp [] xs = []" |
  "multexp (x # xs) ys = sumexp (scalar_mult x ys) (0 # multexp xs ys)"

fun coeffs :: "exp \<Rightarrow> int list" where
  "coeffs Var = [0, 1]" |
  "coeffs (Const k) = [k]" |
  "coeffs (Add a b) = sumexp (coeffs a) (coeffs b)" |
  "coeffs (Mult a b) = multexp (coeffs a) (coeffs b)"

value "coeffs (Add (Const 2) (Var))"
value "coeffs (Mult Var Var)"
value "evalp (coeffs (Mult Var Var)) 2" (* It works! *)

lemma evalp_preserve_sum [simp]: "evalp (sumexp xs ys) n = evalp xs n + evalp ys n"
  apply (induction rule:sumexp.induct)
  apply (auto simp add:Int.int_distrib)
  done

lemma evalp_preserve_scalar_mult [simp]: "evalp (scalar_mult n xs) x = n * evalp xs x"
  apply (induction xs)
  apply (auto simp add:Int.int_distrib)
  done

lemma evalp_preserve_mult [simp]: "evalp (multexp xs ys) n = evalp xs n * evalp ys n"
  apply (induction xs)
  apply (auto simp add:Int.int_distrib)
  done

theorem evalp_coeffs: "evalp (coeffs e) x = eval e x"
  apply (induction e)
  apply (auto)
  done

end

