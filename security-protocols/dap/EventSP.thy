(*header{* Theory of Events for Security Protocols that use Smartphones with QR-Code readers *}*)

theory EventSP imports "~~/src/HOL/Auth/Message" begin

consts  (*Initial states of agents -- parameter of the construction*)
  initState :: "agent => msg set"

datatype smartphone = Smarphone agent

datatype  
  event = Says    agent agent msg
        | Notes   agent       msg
        | Gets    agent       msg
        | Inputs  agent       smartphone msg (* agent visually displays message to smartphone... *)
        | Gets_s  smartphone  msg (* ... smartphone receives it *)
        | Outputs smartphone  agent msg (* smartphone gives information to be inputed in agent... *)
        | Gets_a  agent       msg (* ... agent receives it*)
    
consts 
 bad        :: "agent set"  (* compromised agents *)
 connected  :: "smartphone set" (* network connected smartphones *)
 badp       :: "smartphone set" (* compromised smartphones *)
 stolen     :: "smartphone set" (* stolen smartphones *)

specification (bad)
  Spy_in_bad  [iff]: "Spy \<in> bad"
  Server_not_bad [iff]: "Server \<notin> bad"
  apply (rule exI [of _ "{Spy}"], simp)
  done
  
specification (stolen)
  Server_phone_not_stolen [iff]: "Smartphone Server \<notin> stolen"
  Spy_phone_not_stolen [iff]: "Smartphone Spy \<notin> stolen"
  apply blast
  done

specification (badp)
  (* Spy phone is secured because she already can use it freely *)
  Spy_phone_in_bad [iff]: "Smartphone Spy \<notin> badp"  
  Server_phone_not_bad [iff]: "Smartphone Server \<notin> badp"
  apply blast
  done

(* Agents' knowledge definition over a trace is extended to comprehend new Smartphone events *)
primrec knows :: "agent \<Rightarrow> event list \<Rightarrow> msg set" where
  knows_Nil :  "knows A [] = initState A" |
  knows_Cons : "knows A (ev # evs) =
    (case ev of
        Says A' B X \<Rightarrow> 
          if (A = A' | A = Spy) then insert X (knows A evs)
          else (knows A evs)
      | Notes A' X \<Rightarrow>
          if (A = A' | (A = Spy & A' \<in> bad)) then insert X (knows A evs)
          else knows A evs
      | Gets A' X \<Rightarrow>
          if (A = A' & A \<noteq> Spy) then insert X (knows A evs)
          else knows A evs
      | Inputs A' P X \<Rightarrow>
          if (A = A') then insert X (knows A evs)
          else knows A evs
      | Gets_s P X \<Rightarrow>
          if (A = Spy & P \<in> connected & P \<in> badp) then insert X (knows A evs)
          else knows A evs
      | Outputs P A' X \<Rightarrow>
          if (A = A' | (A = Spy & P \<in> connected & P \<in> badp)) then insert X (knows A evs)
          else knows A evs
      | Gets_a A' X \<Rightarrow>
          if (A = A' & A \<noteq> Spy) then insert X (knows A evs)
          else knows A evs
  )"
  
primrec used :: "event list \<Rightarrow> msg set" where
  used_Nil  : "used [] = (\<Union> B. parts (initState B))" |
  used_Cons : "used (ev # evs) = 
    (case ev of   
        Says A B X \<Rightarrow> parts {X} \<union> (used evs)
      | Notes A X \<Rightarrow> parts {X} \<union> (used evs)
      | Gets A X \<Rightarrow> used evs
      | Inputs A P X \<Rightarrow> parts {X} \<union> used evs
      | Gets_s P X \<Rightarrow> used evs
      | Outputs P A X \<Rightarrow> parts {X} \<union> used evs
      | Gets_a A X \<Rightarrow> used evs
  )" 


  
lemma Notes_imp_used [rule_format] : 
  "Notes A X \<in> set evs \<longrightarrow> X \<in> used evs"
apply (induct_tac evs)
apply (auto split: event.split) 
done

lemma Says_imp_used [rule_format] :
  "Says A B X \<in> set evs \<longrightarrow> X \<in> used evs"
apply (induct_tac evs)
apply (auto split: event.split) 
done




lemmas parts_insert_knows_A = parts_insert [of _ "knows A evs"] for A evs

lemma knows_Spy_Says [simp] :
  "knows Spy (Says A B X # evs) = insert X (knows Spy evs)"
by simp

lemma knows_Spy_Gets [simp] :
  "knows Spy (Gets B X # evs) = knows Spy evs"
by simp

lemma knows_Spy_Notes [simp] : 
  "knows Spy (Notes A X # evs) = 
    (if A \<in> bad then insert X (knows Spy evs) else knows Spy evs)"
by simp

lemma knows_Spy_Inputs [simp] : 
  "knows Spy (Inputs A P X # evs) = 
    (if A = Spy then insert X (knows Spy evs) else knows Spy evs)"
by simp

lemma knows_Spy_Gets_s [simp] :
  "knows Spy (Gets_s P X # evs) = 
    (if (P \<in> connected & P \<in> badp) then insert X (knows Spy evs) else knows Spy evs)"
by simp

lemma knows_Spy_Outputs [simp] : 
  "knows Spy (Outputs P A X # evs) = 
    (
      if A = Spy then insert X (knows Spy evs)
      else if (P \<in> connected & P \<in> badp) then insert X (knows Spy evs)
      else knows Spy evs
    )"
by simp

lemma knows_Spy_Gets_a [simp] :
  "knows Spy (Gets_a A X # evs) = knows Spy evs"
by simp


lemma knows_Spy_subset_knows_Spy_Says :
  "knows Spy evs \<subseteq> knows Spy (Says A B X # evs)"
by (simp add: subset_insertI)

lemma knows_Spy_subset_knows_Spy_Notes :
  "knows Spy evs \<subseteq> knows Spy (Notes A X # evs)"
by force

lemma knows_Spy_subset_knows_Spy_Gets :
  "knows Spy evs \<subseteq> knows Spy (Gets A X # evs)"
by (simp add: subset_insertI)

lemma knows_Spy_subset_knows_Spy_Inputs :
  "knows Spy evs \<subseteq> knows Spy (Inputs A P X # evs)"
by auto

lemma knows_Spy_subset_knows_Spy_Gets_s :
  "knows Spy evs \<subseteq> knows Spy (Gets_s P X # evs)"
by (simp add: subset_insertI)

lemma knows_Spy_subset_knows_Spy_Outputs :
  "knows Spy evs \<subseteq> knows Spy (Outputs P A X # evs)"
by (simp add: subset_insertI)

lemma knows_Spy_subset_knows_Spy_Gets_a :
  "knows Spy evs \<subseteq> knows Spy (Gets_a A X # evs)"
by (simp add: subset_insertI)  

end