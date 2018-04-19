(*header{* Theory for Events for Security Protocols that use Smartphones with QR-Code readers *}*)

theory Smartphone imports "./EventSP" "~~/src/HOL/Auth/Message" begin

definition legalUse :: "smartphone \<Rightarrow> bool" ("legalUse (_)") where
  "legalUse P == P \<notin> stolen"
  

definition illegalUse :: "smartphone \<Rightarrow> bool" ("illegalUse (_)") where
  "illegalUse P == P \<in> stolen"

end