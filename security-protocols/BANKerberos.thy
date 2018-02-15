(*
  Title: BAN Kerberos Review
  Author: Felipe Rodopoulos de Oliveira
*)

theory BANKerberos

imports "~~/src/HOL/Auth/Public"

begin

(* DEFINITION OF CURRENT TIME *)
abbreviation CT :: "event list \<Rightarrow> nat" where
  "CT == length"

(* DEFINITION OF LIFETIME FOR ENTITIES *)
consts sesKlife :: nat (* session key *)
consts authlife :: nat (* authenticator *)

specification (sesKlife) sesKlife_freshness [iff]: "2 \<le> sesKlife"
  by blast

specification (authlife) authlife_freshness [iff]: "authlife \<noteq> 0"
  by blast

(* DEFINITION OF EXPIRATION PREDICATES *)
abbreviation
  expiredK :: "[nat, event list] => bool" where
  "expiredK T evs == sesKlife + T < CT evs"

abbreviation
  expiredA :: "[nat, event list] => bool" where
  "expiredA T evs == authlife + T < CT evs"


(* PROTOCOL MODEL *)
inductive_set bankerberos :: "event list set" where

  (* Nothing going on in the network *)
  NIL: "[] \<in> bankerberos" |

  (* Modeling the spy omnipotent premises.
     - evfk is a trace
     - X is derivable from the Spy's knowledge set
     - B is not the Spy

    Then the Spy can send a fraudulent message to B
  *)
  Fake: "\<lbrakk> evfk \<in> bankerberos; X \<in> synth (analz (spies evfk)) \<rbrakk>
    \<Longrightarrow> Says Spy B X # evfk \<in> bankerberos" |


  (* First step: A issues the Server with the communication pair of agents *)
  BK1: "\<lbrakk> evs1 \<in> bankerberos \<rbrakk> 
    \<Longrightarrow> Says A Server \<lbrace>Agent A, Agent B\<rbrace> # evs1 \<in> bankerberos" |

  (* 2nd step: the Server responds A. For this, we that:
    - Event is valid
    - Session key K is fresh
    - Session key K is symmetric
    - Step 1 occured: Agent A must have issued the Server
  *)
  BK2: "\<lbrakk> evs2 \<in> bankerberos; Key K \<notin> used evs2; K \<in> symKeys;
        Says A' Server \<lbrace> Agent A, Agent B \<rbrace> \<in> set evs2 \<rbrakk> 
    \<Longrightarrow> Says Server A (Crypt (shrK A) 
          \<lbrace> Number (CT evs2), Agent B, Key K, 
            (Crypt (shrK B) \<lbrace> Number (CT evs2), Agent A, Key K \<rbrace>) 
          \<rbrace>) # evs2 \<in> bankerberos" |

  (* 3rd step: A send the ticket and the authenticator to B. Hence:
    - Event is valid
    - Step 2 occured
    - Step 1 occured 
    - Timestamp for session key is not expired
  *)
  BK3: "\<lbrakk> evs3 \<in> bankerberos;
          Says S A (Crypt (shrK A) \<lbrace> Number Tk, Agent B, Key K, Ticket \<rbrace>) \<in> set evs3;
          Says A Server \<lbrace>Agent A, Agent B\<rbrace> \<in> set evs3;
          \<not> expiredK Tk evs3 \<rbrakk>
    \<Longrightarrow> Says A B \<lbrace> Ticket, Crypt K \<lbrace> Agent A, Number (CT evs3) \<rbrace> \<rbrace> # evs3 \<in> bankerberos" |

  (* 4th step: B send his authenticator to A. For that:
    - Event is valid
    - Step 3 ocurred
    - Timestamp for session key is not expired
    - Timestamp for authenticator is not expired
  *)
  BK4: "\<lbrakk> evs4 \<in> bankerberos;
          Says A' B \<lbrace> 
             (Crypt (shrK B) \<lbrace>Number Tk, Agent A, Key K\<rbrace>),
             (Crypt K \<lbrace>Agent A, Number Ta\<rbrace>)
          \<rbrace> \<in> set evs4;
          \<not> expiredK Tk evs4;
          \<not> expiredA Ta evs4
        \<rbrakk> 
    \<Longrightarrow> Says B A (Crypt K (Number Ta)) # evs4 \<in> bankerberos" | 

  (* Finally modeling the disclosure of key and leaking of info by a compromised agent *)
  Oops: "\<lbrakk> evop \<in> bankerberos; 
           Says Server A (Crypt (shrK A) \<lbrace>Number Tk, Agent B, Key K, Ticket\<rbrace>) \<in> set evop;
           expiredK Tk evop \<rbrakk>
    \<Longrightarrow> Notes Spy \<lbrace>Number Tk, Key K\<rbrace> # evop \<in> bankerberos"


(* MODELING THE PROTOCOL POSSIBILITIES *)
(* 
  We have to prove that it is possible that some trace reach an end. 
  This happens when we have a fresh session key being shared between A and B
*)

(* declare [[show_types]] *)
(* declare [[show_sorts]] *)
(* declare [[show_consts]] *)

lemma "\<lbrakk> Key K \<notin> used []; K \<in> symKeys \<rbrakk> 
        \<Longrightarrow> \<exists> Timestamp. \<exists> evs \<in> bankerberos. 
          Says B A (Crypt K (Number Timestamp)) \<in> set evs"
  apply (cut_tac sesKlife_freshness)
  apply (intro exI)
  apply (intro bexI)
  apply (rule_tac [2] bankerberos.BK4)
  apply (rule_tac [2] bankerberos.BK3)
  apply (rule_tac [2] bankerberos.BK2)
  apply (rule_tac [2] bankerberos.BK1)
  apply (rule_tac [2] bankerberos.NIL)
  apply (simp) (* Killing subgoal 1: including event of BK4 *)
  apply (simp) (* Killing subgoal 2: first premise for BK2 \<rightarrow> K is fresh *)
  apply (simp) (* Killing subgoal 3: second premise for BK2 \<rightarrow> K is a symmetric key*)
  apply (simp) (* Killing subgoal 4: third premise for BK2 \<rightarrow> BK1 happened *)
  apply (simp) (* Killing subgoal 5: first premise for BK3 \<rightarrow> BK2 happened *)
  apply (simp) (* Killing subgoal 6: second premise for BK3 \<rightarrow> BK1 happened *)
  apply (simp (no_asm_simp)) (* Killing subgoal 7: third for BK3 \<rightarrow> Tk is valid *)
  apply (simp) (* Killing subgoal 8: first premise for BK4 \<rightarrow> BK happened *)
  apply (simp (no_asm_simp)) (* Killing subgoal 9: second premise for BK4 \<rightarrow> Tk is valid *)
  apply (simp) (* Killing subgoal 10: third premise for BK4 \<rightarrow> Ta is valid *)
  (* apply (simp_all (no_asm_simp))+ *) 
done


(* Defining BEFORE function, that returns all events before a certain event *)
fun before :: "event \<Rightarrow> event list \<Rightarrow> event list" where
  "before ev evs = takeWhile (\<lambda>z. z \<noteq> ev) (rev evs)"


(* TODO: Needed these two for proving both lemmas below. Don't know why. *)
declare Says_imp_knows_Spy [THEN parts.Inj, dest]
declare parts.Body [dest]
declare analz_into_parts [dest]
declare Fake_parts_insert_in_Un [dest]


lemma Oops_reveals_ticket :
  "Says S A (Crypt Ka \<lbrace>Timestamp, B, K, Ticket\<rbrace>) \<in> set evs
    \<Longrightarrow> Ticket \<in> parts (spies evs)"
  apply blast
done

lemma Oops_reveals_key : 
  "Says Server A (Crypt (shrK A) \<lbrace>Timestamp, B, K, Ticket\<rbrace>) \<in> set evs 
    \<Longrightarrow> K \<in> parts(spies evs)"
  apply blast
done

lemma [simp] : "evs \<in> bankerberos \<Longrightarrow> Key (shrK A) \<in> parts(spies evs) = (A \<in> bad)"
  apply (erule bankerberos.induct)
  apply (frule_tac [7] Oops_reveals_key)
  apply (frule_tac [5] Oops_reveals_ticket)
  apply (simp_all)
  apply (blast)
  apply (blast)
  apply (blast)
done

lemma "evs \<in> bankerberos \<Longrightarrow> (Key (shrK A) \<in> analz(spies evs)) = (A \<in> bad)"
  apply (auto)
done


end