--------------------- MODULE TwoPhaseCommit ----------------------
EXTENDS Naturals, TLC


(*
--algorithm TwoPhaseCommit {
  variables 
    managers = {"bob", "chuck", "dave", "everett", "fred"};
    a = 0;
        
  process (Restaurant \in managers)
  {
    c0: a := a + 1;
    c1: goto c0;     
  }; \* end Restaurant process block

} \* end algorithm
*)    
\* BEGIN TRANSLATION
VARIABLES managers, a, pc

vars == << managers, a, pc >>

ProcSet == (managers)

Init == (* Global variables *)
        /\ managers = {"bob", "chuck", "dave", "everett", "fred"}
        /\ a = 0
        /\ pc = [self \in ProcSet |-> "c0"]

c0(self) == /\ pc[self] = "c0"
            /\ a' = a + 1
            /\ pc' = [pc EXCEPT ![self] = "c1"]
            /\ UNCHANGED managers

c1(self) == /\ pc[self] = "c1"
            /\ pc' = [pc EXCEPT ![self] = "c0"]
            /\ UNCHANGED << managers, a >>

Restaurant(self) == c0(self) \/ c1(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in managers: Restaurant(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

==================================================================