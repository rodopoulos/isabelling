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

lemma "\<lbrakk> Key K \<notin> used []; K \<in> symKeys \<rbrakk> 
        \<Longrightarrow> \<exists> Timestamp. \<exists> evs \<in> bankerberos. 
          Says B A (Crypt K (Number Timestamp)) \<in> set evs"
  apply (cut_tac sesKlife_freshness)
  apply (intro exI)
  apply (intro bexI)
  apply (rule_tac [2] bankerberos.NIL [THEN bankerberos.BK1, THEN bankerberos.BK2, THEN bankerberos.BK3, THEN bankerberos.BK4])
  apply (possibility)
  apply (simp_all (no_asm_simp))
  done


end