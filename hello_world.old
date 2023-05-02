------------------------------- MODULE hello_world -------------------------------
EXTENDS Integers, Naturals, TLC


(* 
--fair algorithm hello_world {
variables 
    TaskList = {"Task1"};
    a = 0;

process (Task \in TaskList) 
{
    a1: if (a > 5) a := 0 else a:= a + 1;
    a2: print a;    
    a3: goto a1;
}; \* end process

} *)




\* BEGIN TRANSLATION
VARIABLES TaskList, a, pc

vars == << TaskList, a, pc >>

ProcSet == (TaskList)

Init == (* Global variables *)
        /\ TaskList = {"Task1"}
        /\ a = 0
        /\ pc = [self \in ProcSet |-> "a1"]

a1(self) == /\ pc[self] = "a1"
            /\ IF a > 5
                  THEN /\ a' = 0
                  ELSE /\ a' = a + 1
            /\ pc' = [pc EXCEPT ![self] = "a2"]
            /\ UNCHANGED TaskList

a2(self) == /\ pc[self] = "a2"
            /\ PrintT(a)
            /\ pc' = [pc EXCEPT ![self] = "a3"]
            /\ UNCHANGED << TaskList, a >>

a3(self) == /\ pc[self] = "a3"
            /\ pc' = [pc EXCEPT ![self] = "a1"]
            /\ UNCHANGED << TaskList, a >>

Task(self) == a1(self) \/ a2(self) \/ a3(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in TaskList: Task(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

Stopper == /\ a /= 3
           /\ a /= 4

=============================================================================
