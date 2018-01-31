(*
  Title: BAN Kerberos Review
  Author: Felipe Rodopoulos de Oliveira
*)

theory BANKerberos

imports "~~/src/HOL/Auth/Public"

begin

(* DEFINITION OF CURRENT TIME *)
abbreviation CT :: "event list \<Rightarrow> nat" where
  "CT == lenght"

(* DEFINITION OF LIFETIME FOR ENTITIES *)
consts sesKlife :: nat
consts authlife :: nat


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
    - Agent A must have issued the Server
  *)
  BK2: "\<lbrakk> evs2 \<in> bankerberos; Key K \<notin> used evs2; K \<in> symKeys;
        Says A' Server \<lbrace>Agent A, Agent B\<rbrace> \<in> set evs2 \<rbrakk> 
    \<Longrightarrow> Says Server A (Crypt (shrK A) 
          \<lbrace> Number CT evs2, Agent B, Key K, (Crypt (shrK B) 
            \<lbrace> Number CT evs2, Agent A, Key K\<rbrace>) 
          \<rbrace>) # evs2 \<in> bankerberos" |

  (* 3rd step: A send the ticker and the authenticator to B. Hence:
    - Event is valid
    - 
  *)
  "BK3: \<lbrakk> evs3 \<in> bankerberos; \<rbrakk>"

end