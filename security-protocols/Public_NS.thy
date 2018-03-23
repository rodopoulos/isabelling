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

lemma Spy_see_keys_for_compromised_agents :
  "evs \<in> nspublic \<Longrightarrow> (Key (priK A) \<in> parts (knows Spy evs)) = (A \<in> bad)"
  apply (erule nspublic.induct)
  apply (simp_all)
  apply auto
  done

end