---------------------------- MODULE Counter ----------------------------
EXTENDS Integers, TLC

CONSTANTS NumProcesses

VARIABLES 
    counter,      \* The shared counter
    pc,           \* Program counter for each process
    local         \* Local variable for each process

vars == <<counter, pc, local>>

Init ==
    /\ counter = 0
    /\ pc = [p \in 1..NumProcesses |-> "Get"]
    /\ local = [p \in 1..NumProcesses |-> 0]

Get(p) ==
    /\ pc[p] = "Get"
    /\ local' = [local EXCEPT ![p] = counter]
    /\ pc' = [pc EXCEPT ![p] = "Inc"]
    /\ UNCHANGED counter

Inc(p) ==
    /\ pc[p] = "Inc"
    /\ counter' = local[p] + 1
    /\ pc' = [pc EXCEPT ![p] = "Done"]
    /\ UNCHANGED local

Next == \E p \in 1..NumProcesses : Get(p) \/ Inc(p)

Spec == Init /\ [][Next]_vars

\* Properties
TypeOK ==
    /\ counter \in Nat
    /\ pc \in [1..NumProcesses -> {"Get", "Inc", "Done"}]
    /\ local \in [1..NumProcesses -> Nat]

\* This property will be violated due to race conditions
FinalCounterCorrect ==
    (\A p \in 1..NumProcesses : pc[p] = "Done") => counter = NumProcesses

\* Temporal property: eventually all processes complete
EventuallyAllDone ==
    <>(\A p \in 1..NumProcesses : pc[p] = "Done")

=======================================================================