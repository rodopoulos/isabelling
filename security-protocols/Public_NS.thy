(*
  Title: Public-key Needham Schroeder Review
  Author: Felipe Rodopoulos de Oliveira
*)

theory Public_NS

imports "~~/src/HOL/Auth/Public"

begin

consts ns_public :: "event list set"

inductive_set nspublic :: "event list set" where

  Nil: "[] \<in> nspublic"

  | Fake: "\<lbrakk>evsf \<in> nspublic; X \<in> synth (analz (knows Spy evsf))\<rbrakk>
    \<Longrightarrow> Says Spy B X # evsf \<in> nspublic"

  | NS1: "\<lbrakk>evs1 \<in> nspublic; Nonce Na \<notin> used evs1\<rbrakk> 
    \<Longrightarrow> Says A B (Crypt (pubK B) \<lbrace>Nonce Na, Agent A\<rbrace>) # evs1 \<in> nspublic"

  | NS2: "\<lbrakk>evs2 \<in> nspublic; Nonce Nb \<notin> used evs2;
         Says A' B (Crypt (pubK B) \<lbrace>Nonce Na, Agent A\<rbrace>) \<in> set evs2 \<rbrakk> 
    \<Longrightarrow> Says B A (Crypt (pubK A) \<lbrace>Number Na, Number Nb, Agent B\<rbrace>) # evs2 \<in> nspublic"

  | NS3: "\<lbrakk>evs3 \<in> nspublic;
           Says A B (Crypt (pubK B) \<lbrace>Nonce Na, Agent A\<rbrace>) \<in> set evs3;
           Says B' A (Crypt (pubK A) \<lbrace>Number Na, Number Nb, Agent B\<rbrace>) \<in> set evs3\<rbrakk> 
    \<Longrightarrow> Says A B (Crypt (pubK B) (Nonce Nb)) # evs3 \<in> nspublic"

 
declare analz_into_parts [dest]
    
lemma Spy_only_see_compromised_keys [simp] :
  "evs \<in> nspublic \<Longrightarrow> (Key (priK A) \<in> parts (knows Spy evs)) = (A \<in> bad)"
  apply (erule nspublic.induct) (* apply protocol steps *)
  (* Just simply everything. Agent A private key never appears in any message *)
  apply (simp_all)
  (* We are left with one subgoal. We have the two first premises. 
     Luckily, the third one is presented in Inductive Method theory
  *)
  apply (frule_tac Fake_parts_insert) 
  (* Simplify everything. Proof is done. *)
  apply (auto)
  done
  
lemma Spy_only_see_leaked_keys [simp] :
  "evs \<in> nspublic \<Longrightarrow> (Key (priK A) \<in> analz (knows Spy evs)) = (A \<in> bad)"
  (* This is obvious given that analz H \<subseteq> parts H *)
  apply (auto)
  done

end