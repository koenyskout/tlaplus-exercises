---- MODULE Counter1 ----
EXTENDS Naturals

\* Possible states of a thread
\* - started = before incrementing the counter
\* - done = after incrementing the counter
ThreadState == { "started", "done" }

\* state includes the counter and the state of both threads
VARIABLES counter, thread1, thread2
vars == <<counter, thread1, thread2>>

\* Initial state of counter and threads
Init == /\ counter = 0
        /\ thread1 = "started"
        /\ thread2 = "started"

\* Action: Thread 1 increases the counter.
\* Can only happen if it's in the "started" state
Inc1 == /\ thread1 = "started"
        /\ counter' = counter + 1
        /\ thread1' = "done"
        /\ UNCHANGED thread2

\* Action: Thread 2 increases the counter.
\* Can only happen if it's in the "started" state
Inc2 == /\ thread2 = "started"
        /\ counter' = counter + 1
        /\ thread2' = "done"
        /\ UNCHANGED thread1

\* Combine all actions into a Next action
Next == \/ Inc1
        \/ Inc2

(* For our liveness property (counter will reach 2),
   we need to assume that the threads will not hang/crash.
   We can do that with weak fairness. *)
Liveness == WF_vars(Next)

\* The specification of the system as a combination of Init, Next, and our liveness assumptions.
Spec == Init /\ [][Next]_vars /\ Liveness

----
\* Invariant: Types are as expected
TypeOK == /\ counter \in Nat 
          /\ thread1 \in ThreadState
          /\ thread2 \in ThreadState

THEOREM Spec => []TypeOK

\* Invariant: Counter between 0 and 2
CounterOK == counter \in 0..2
THEOREM Spec => []CounterOK

\* Liveness: Counter eventually becomes 2
Counter2 == <>(counter = 2)
THEOREM Spec => Counter2
====