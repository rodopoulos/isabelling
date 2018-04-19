(*header{* Theory of Events for Security Protocols that use Smartphones with QR-Code readers *}*)

theory EventSP imports "~~/src/HOL/Auth/Message" begin

consts  (*Initial states of agents -- parameter of the construction*)
  initState :: "agent => msg set"

datatype smartphone = Smarphone agent

text{*Four new events express the traffic between an agent and his card*}
datatype  
  event = Says  agent agent msg
        | Notes agent       msg
        | Gets  agent       msg
        | Shows agent smartphone msg
        | Scans smartphone  msg 
    
consts 
 bad     :: "agent set"  (*compromised agents*)
 stolen  :: "smartphone set" (* stolen smart cards *)
 secureM :: "bool"(*assumption of secure means between agents and their cards*)

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

end