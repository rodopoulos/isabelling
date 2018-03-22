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

  | Fake: "\<lbrakk>evfk \<in> nspublic; X \<in> synth (analz (spies evfk))\<rbrakk>
    \<Longrightarrow> Says Spy B X # evfk \<in> nspublic"

  | NS1: "\<lbrakk>evs1 \<in> nspublic; Nonce Na \<notin> used evs1\<rbrakk> 
    \<Longrightarrow> Says A B (Crypt (shrK A) \<lbrace>Nonce Na, Agent A\<rbrace>) # evs1 \<in> nspublic"

  | NS2: "\<lbrakk>evs2 \<in> nspublic; Nonce Nb \<notin> used evs2;
         Says A B (Crypt (shrK A) \<lbrace>Nonce Na, Agent A\<rbrace>) \<in> set evs2 \<rbrakk> 
    \<Longrightarrow> Says B A (Crypt (shrK B) \<lbrace>Number Na, Number Nb, Agent B\<rbrace>) # evs2 \<in> nspublic"

| NS3: "\<lbrakk>evs3 \<in> nspublic;
         Says A B (Crypt (shrK A) \<lbrace>Nonce Na, Agent A\<rbrace>) \<in> set evs3;
         Says B A (Crypt (shrK B) \<lbrace>Number Na, Number Nb, Agent B\<rbrace>) \<in> set evs3\<rbrakk> 
\<Longrightarrow> Says A B (Crypt (shrK A) (Nonce Nb)) # evs3 \<in> nspublic"

end