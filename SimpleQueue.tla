------------------------------- MODULE SimpleQueue -------------------------------
EXTENDS Integers, Naturals, TLC

 (* --fair algorithm algo {
variables 
    \* Represent the 3 tasks we have in the application
    ApplicationTask = "Application";
    MQTTAgentTask = "MQTTAgent";
    NetworkTask = "Network"; \* We model the network as a process as it acts concurrently
    QMax = 5 ;
    agentQueue = 0;


fair process (App = ApplicationTask) 
{
    a1: await agentQueue < QMax; agentQueue := agentQueue + 1;
    a2: skip;   
    a3: goto a1 
}; \* end process

fair process (Agent = MQTTAgentTask) 
{
    \* The Agent blocks until there is any message to process, if there is it processes it and continues
    
    A1: await agentQueue > 0; agentQueue := agentQueue - 1;
    A2: skip;    
    A3: goto A1
}; \* end process

fair process (Network = NetworkTask)
{
    \* The network task will wait until there is room in the queue, if there is it receives a packet assuming infinite source 
    N1: await agentQueue < QMax; agentQueue := agentQueue + 1;
    N2: skip;
    N3: goto N1
} ; \* end process

}

*)



\* BEGIN TRANSLATION
VARIABLES ApplicationTask, MQTTAgentTask, NetworkTask, QMax, agentQueue, pc

vars == << ApplicationTask, MQTTAgentTask, NetworkTask, QMax, agentQueue, pc
        >>

ProcSet == {ApplicationTask} \cup {MQTTAgentTask} \cup {NetworkTask}

Init == (* Global variables *)
        /\ ApplicationTask = "Application"
        /\ MQTTAgentTask = "MQTTAgent"
        /\ NetworkTask = "Network"
        /\ QMax = 5
        /\ agentQueue = 0
        /\ pc = [self \in ProcSet |-> CASE self = ApplicationTask -> "a1"
                                        [] self = MQTTAgentTask -> "A1"
                                        [] self = NetworkTask -> "N1"]

a1 == /\ pc[ApplicationTask] = "a1"
      /\ agentQueue < QMax
      /\ agentQueue' = agentQueue + 1
      /\ pc' = [pc EXCEPT ![ApplicationTask] = "a2"]
      /\ UNCHANGED << ApplicationTask, MQTTAgentTask, NetworkTask, QMax >>

a2 == /\ pc[ApplicationTask] = "a2"
      /\ TRUE
      /\ pc' = [pc EXCEPT ![ApplicationTask] = "a3"]
      /\ UNCHANGED << ApplicationTask, MQTTAgentTask, NetworkTask, QMax, 
                      agentQueue >>

a3 == /\ pc[ApplicationTask] = "a3"
      /\ pc' = [pc EXCEPT ![ApplicationTask] = "a1"]
      /\ UNCHANGED << ApplicationTask, MQTTAgentTask, NetworkTask, QMax, 
                      agentQueue >>

App == a1 \/ a2 \/ a3

A1 == /\ pc[MQTTAgentTask] = "A1"
      /\ agentQueue > 0
      /\ agentQueue' = agentQueue - 1
      /\ pc' = [pc EXCEPT ![MQTTAgentTask] = "A2"]
      /\ UNCHANGED << ApplicationTask, MQTTAgentTask, NetworkTask, QMax >>

A2 == /\ pc[MQTTAgentTask] = "A2"
      /\ TRUE
      /\ pc' = [pc EXCEPT ![MQTTAgentTask] = "A3"]
      /\ UNCHANGED << ApplicationTask, MQTTAgentTask, NetworkTask, QMax, 
                      agentQueue >>

A3 == /\ pc[MQTTAgentTask] = "A3"
      /\ pc' = [pc EXCEPT ![MQTTAgentTask] = "A1"]
      /\ UNCHANGED << ApplicationTask, MQTTAgentTask, NetworkTask, QMax, 
                      agentQueue >>

Agent == A1 \/ A2 \/ A3

N1 == /\ pc[NetworkTask] = "N1"
      /\ agentQueue < QMax
      /\ agentQueue' = agentQueue + 1
      /\ pc' = [pc EXCEPT ![NetworkTask] = "N2"]
      /\ UNCHANGED << ApplicationTask, MQTTAgentTask, NetworkTask, QMax >>

N2 == /\ pc[NetworkTask] = "N2"
      /\ TRUE
      /\ pc' = [pc EXCEPT ![NetworkTask] = "N3"]
      /\ UNCHANGED << ApplicationTask, MQTTAgentTask, NetworkTask, QMax, 
                      agentQueue >>

N3 == /\ pc[NetworkTask] = "N3"
      /\ pc' = [pc EXCEPT ![NetworkTask] = "N1"]
      /\ UNCHANGED << ApplicationTask, MQTTAgentTask, NetworkTask, QMax, 
                      agentQueue >>

Network == N1 \/ N2 \/ N3

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == App \/ Agent \/ Network
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)
        /\ WF_vars(App)
        /\ WF_vars(Agent)
        /\ WF_vars(Network)

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION



=============================================================================
