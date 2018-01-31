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
consts authlife :: nat (* authenticators *)

(* DEFINITION OF EXPIRATION PREDICATES *)
abbreviation expiredK :: "[nat, event list] \<Rightarrow> bool" where
  "expiredK Tk evs == ((CT evs) - Tk > sesKlife)"

abbreviation expiredA :: "[nat, event list] \<Rightarrow> bool" where
  "expiredA Ta evs == ((CT evs) - Ta > authlife)"


(* PROTOCOL MODEL *)
inductive_set bankerberos :: "event list set" where

  (* Nothing going on in the network *)
  NIL: "[] \<in> bankerberos" |

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
        Says A' Server \<lbrace>Agent A, Agent B\<rbrace> \<in> set evs2 \<rbrakk> 
    \<Longrightarrow> Says Server A (Crypt (shrK A) 
          \<lbrace> Number CT evs2, Agent B, Key K, (Crypt (shrK B) 
            \<lbrace> Number CT evs2, Agent A, Key K \<rbrace>) 
          \<rbrace>) # evs2 \<in> bankerberos" |

  (* 3rd step: A send the ticket and the authenticator to B. Hence:
    - Event is valid
    - Step 2 occured
    - Step 1 occured 

  BK3: "\<lbrakk>
          evs3 \<in> bankerberos;
          Says Server A (Crypt (shrK A) \<lbrace> Number Tk, Agent B, Key K, 
            (Crypt (shrK B) \<lbrace> Number Tk, Agent A, Key K \<rbrace>)
          \<rbrace>) \<in> set evs3;
          Says A Server \<lbrace>Agent A, Agent B\<rbrace> \<in> set evs2
        \<rbrakk>
    \<Longrightarrow> Says A B \<lbrace>
          (Crypt (shrK B) \<lbrace> Number CT evs2, Agent A, Key K \<rbrace>, 
          (Crypt K \<lbrace> Agent A, Number (CT evs3) \<rbrace>)
        \<rbrace> # evs3 \<in> bankerberos"
  *)
  

end