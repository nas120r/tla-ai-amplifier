----------------------- MODULE ProducerConsumer -----------------------
EXTENDS Integers, Sequences, TLC

CONSTANTS 
    Producers,      \* Set of producers
    Consumers,      \* Set of consumers  
    QueueCapacity,  \* Maximum queue size
    MaxValue        \* Maximum value to produce

VARIABLES
    queue,          \* The shared queue
    produced,       \* Values produced by each producer
    consumed,       \* Values consumed by each consumer
    nextValue       \* Next value to produce

vars == <<queue, produced, consumed, nextValue>>

Init ==
    /\ queue = <<>>
    /\ produced = [p \in Producers |-> <<>>]
    /\ consumed = [c \in Consumers |-> <<>>]
    /\ nextValue = 1

Produce(p) ==
    /\ Len(queue) < QueueCapacity
    /\ nextValue <= MaxValue
    /\ queue' = Append(queue, nextValue)
    /\ produced' = [produced EXCEPT ![p] = Append(@, nextValue)]
    /\ nextValue' = nextValue + 1
    /\ UNCHANGED consumed  \* AI helps maintain this!

Consume(c) ==
    /\ Len(queue) > 0
    /\ LET value == Head(queue) IN
        /\ queue' = Tail(queue)
        /\ consumed' = [consumed EXCEPT ![c] = Append(@, value)]
    /\ UNCHANGED <<produced, nextValue>>  \* AI helps maintain this!

Next ==
    \/ \E p \in Producers : Produce(p)
    \/ \E c \in Consumers : Consume(c)

Spec == Init /\ [][Next]_vars

\* Properties from informal description (AI can help translate these)
TypeOK ==
    /\ queue \in Seq(1..MaxValue)
    /\ Len(queue) <= QueueCapacity
    /\ produced \in [Producers -> Seq(1..MaxValue)]
    /\ consumed \in [Consumers -> Seq(1..MaxValue)]
    /\ nextValue \in 1..(MaxValue + 1)

\* "No value is lost" - AI helped formalize this
NoValueLost ==
    LET AllProduced == UNION {Range(produced[p]) : p \in Producers}
        AllConsumed == UNION {Range(consumed[c]) : c \in Consumers}
        InQueue == Range(queue)
    IN AllProduced = AllConsumed \cup InQueue

\* "Values are consumed in order" - AI helped formalize this
ConsumedInOrder ==
    \A c \in Consumers : IsOrdered(consumed[c])
    
IsOrdered(seq) ==
    \A i \in 1..(Len(seq)-1) : seq[i] < seq[i+1]

=======================================================================