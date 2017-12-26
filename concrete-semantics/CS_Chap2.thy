theory CS_Chap2

  imports Main
    
begin

(* EXERCISE 2.1 *)
value "1 + (2::nat)"
value "1 + (2::int)"
value "1 + 2"
value "1 - (2::nat)"
value "1 - (2::int)"
value "1 - 2"
  
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
    
theorem add_comm: "add m n = add n m"
  apply (induction m)
  apply auto
  done
        
theorem add_assoc: "add a (add b c) = add (add a b) c"
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
  Tip | 
  Node "'a tree" 'a "'a tree"

fun contents:: "'a tree \<Rightarrow> 'a list" where
  "contents Tip = []" |
  "contents (Node l x r) = (contents l) @ [x] @ (contents r)"

value "contents (tree 2)"
value "snoc (contents (tree 2 3 4)) 2" (* it works! *)

fun sum_tree:: "nat tree \<Rightarrow> nat" where
  "sum_tree Tip = 0" |
  "sum_tree (Node l x r) = (sum_tree l) + x + (sum_tree r)"

fun sum_list:: "nat list \<Rightarrow> nat" where
  "sum_list [] = 0" |
  "sum_list (x # xs) = x + sum_list xs"

value "sum_tree (tree 1 2 3)"
value "sum_list [1, 2, 3]"

lemma "sum_tree t = sum_list(contents t)"
  apply (induction t)
   apply auto
  done

  


end

