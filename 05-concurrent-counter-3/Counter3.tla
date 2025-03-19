---- MODULE Counter3 ----
EXTENDS Naturals, FiniteSets

\* We define a constant for an undefined (uninitialized) value
CONSTANT UNDEFINED
\* We define a constant for the set of threads
CONSTANT Threads

\* Number of threads (as cardinality of the Threads set)
NThreads == Cardinality(Threads)

(* Possible states of a thread
   - started = before incrementing the counter
   - read = after reading the current value
   - done = after writing the incremented value
   Note how the thread state serves as a program counter/instruction pointer *)
ThreadPC == { "started", "read", "done" }

\* The state includes the counter and the state of all threads.
VARIABLES counter, threadState
vars == <<counter, threadState>>

(* Initial state of counter and threads.
   We don't just keep the program counter for each thread,
   but also the value of the counter after reading it.
   The state of each thread is be represented as a record with elements pc and val. *)
Init == /\ counter = 0
        /\ threadState = [t \in Threads |-> [pc |-> "started", val |-> UNDEFINED]]

\* Action: A thread reads the counter.
\* Can only happen if it's in the "started" state
\* Updates the pc and val of the thread state (does not modify the counter)
Read(thread) == /\ threadState[thread].pc = "started"
                /\ threadState' = [threadState EXCEPT ![thread] = [pc |-> "read", val |-> counter]]
                /\ UNCHANGED <<counter>>

\* Action: A thread updates the counter.
\* Can only happen if it's in the "read" state
\* Updates the pc of the thread state, and modifies the counter based on it
Inc(thread) == /\ threadState[thread].pc = "read"
               /\ threadState' = [threadState EXCEPT ![thread] = [@ EXCEPT !.pc = "done"]]
               /\ counter' = threadState[thread].val + 1

\* Combine all actions into a Next action (where one thread performs an action)
Next == \E thread \in Threads : 
        \/ Read(thread)
        \/ Inc(thread)

(* For our liveness property (counter will reach NThreads),
   we need to assume that the threads will not hang/crash.
   We can do that with weak fairness. *)
Liveness == WF_vars(Next)

\* The specification of the system as a combination of Init, Next, and our liveness assumptions.
Spec == Init /\ [][Next]_vars /\ Liveness

----
\* Invariant: Types are as expected
TypeOK == /\ counter \in Nat 
          /\ \A thread \in Threads : threadState[thread].pc \in ThreadPC
          /\ \A thread \in Threads : threadState[thread].val \in Nat \cup {UNDEFINED}
THEOREM Spec => []TypeOK

\* Invariant: Counter between 0 and the number of threads 
CounterOK == counter \in 0..NThreads
THEOREM Spec => []CounterOK

\* Helper definition stating that all threads are done
Done == \A thread \in Threads : threadState[thread].pc = "done"

\* Liveness: Eventually, all threads are done and the counter is NThreads
\* This property will be violated, yielding a behavior with counter < NThreads
CounterN == <>(Done /\ counter = NThreads)
THEOREM Spec => CounterN

\* Invariant: Never end up with a final value = 0
NotDoneAndZero == ~(Done /\ counter = 0)
THEOREM Spec => []NotDoneAndZero

\* Invariant: Never end up with a final value = 1
\* This invariant will be violated, yielding a behavior with counter = 1
NotEndWithOne == ~(Done /\ counter = 1)
THEOREM Spec => []NotEndWithOne
====