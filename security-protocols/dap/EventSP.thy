(*header{* Theory of Events for Security Protocols that use Smartphones with QR-Code readers *}*)

theory EventSP imports "~~/src/HOL/Auth/Message" begin

consts  (*Initial states of agents -- parameter of the construction*)
  initState :: "agent => msg set"

datatype smartphone = Smarphone agent

datatype  
  event = Says  agent agent msg
        | Notes agent       msg
        | Gets  agent       msg
        | Shows agent       msg
        | Scans smartphone agent msg 
    
consts 
 bad     :: "agent set"  (* compromised agents *)
 stolen  :: "smartphone set" (* stolen smartphones *)
 secureM :: "bool" (* assumption of secure means between agents and their phones *)

specification (bad)
  Spy_in_bad  [iff]: "Spy \<in> bad"
  Server_not_bad [iff]: "Server \<notin> bad"
  apply (rule exI [of _ "{Spy}"], simp)
  done

specification (stolen)
  Phone_Server_not_stolen [iff]: "Smartphone Server \<notin> stolen"
  Spy_Server_not_stolen [iff]: "Smartphone Spy \<notin> stolen"
  apply blast
  done

 
primrec used :: "event list \<Rightarrow> msg set" where
  used_Nil: "used [] = (\<Union> B. parts (initState B))" |
  used_Cons: 
    "used (ev # evs) = 
      (case ev of   
        Says A B X \<Rightarrow> parts {X} \<union> (used evs) |
        Notes A X \<Rightarrow> parts {X} \<union> (used evs) |
        Gets A X \<Rightarrow> used evs |
        Shows P X \<Rightarrow> parts {X} \<union> (used evs) |
        Scans P A X \<Rightarrow> parts {X} \<union> (used evs))" 

lemma Notes_imp_used [rule_format]: "Notes A X \<in> set evs --> X \<in> used evs"
apply (induct_tac evs)
apply (auto split: event.split) 
done

lemma Says_imp_used [rule_format]: "Says A B X \<in> set evs --> X \<in> used evs"
apply (induct_tac evs)
apply (auto split: event.split) 
done

lemma MPair_used [rule_format]:
     "MPair X Y \<in> used evs --> X \<in> used evs & Y \<in> used evs"
apply (induct_tac evs)
apply (auto split: event.split) 
done



(* primrec knows :: "agent \<Rightarrow> event list \<Rightarrow> msg set" where
  knows_Nil: "knows A [] = initState A" |
  knows_Cons: 
    "knows A (ev # evs) = (case ev of
      Says A' B X \<Rightarrow>
        if (A = A' | A = Spy) then insert X (knows A evs) else knows A evs |
      Notes A' X \<Rightarrow>
        if (A = A' | (A = Spy & A' \<in> bad)) then insert X (knows A evs) else knows A evs |
      Gets A' X \<Rightarrow>
        if (A = A' & A \<noteq> Spy) then insert X (knows A evs) else knows A evs |
      Shows A' X \<Rightarrow>
        if (A = A' | A = Spy) then insert X (knows A evs) else knows A evs |
      Scans P A' X \<Rightarrow> 
        if () )"
*)             
end