---- MODULE Counter2 ----
EXTENDS Naturals

\* We define a constant for an undefined (uninitialized) value
CONSTANT UNDEFINED

(* Possible states of a thread
   - started = before incrementing the counter
   - read = after reading the current value
   - done = after writing the incremented value
   Note how the thread state serves as a program counter/instruction pointer *)
ThreadPC == { "started", "read", "done" }

\* state includes the counter and the state of both threads
VARIABLES counter, thread1, thread2
vars == <<counter, thread1, thread2>>

\* Initial state of counter and threads.
\* We don't just keep the program counter for each thread,
\* but also the value of the counter after reading it
Init == /\ counter = 0
        /\ thread1 = <<"started", UNDEFINED>>
        /\ thread2 = <<"started", UNDEFINED>>

\* Action: Thread 1 reads the counter.
\* Can only happen if it's in the "started" state
Read1 == /\ thread1[1] = "started"
         /\ thread1' = <<"read", counter>>
         /\ UNCHANGED <<thread2, counter>>

\* Action: Thread 1 updates the counter.
\* Can only happen if it's in the "read" state
Inc1 == /\ thread1[1] = "read"
        /\ thread1' = <<"done", counter>>
        /\ counter' = thread1[2] + 1
        /\ UNCHANGED <<thread2>>

\* Action: Thread 2 reads the counter.
\* Can only happen if it's in the "started" state
Read2 == /\ thread2[1] = "started"
         /\ thread2' = <<"read", counter>>
         /\ UNCHANGED <<thread1, counter>>

\* Action: Thread 1 updates the counter.
\* Can only happen if it's in the "read" state
Inc2 == /\ thread2[1] = "read"
        /\ thread2' = <<"done", counter>>
        /\ counter' = thread2[2] + 1
        /\ UNCHANGED <<thread1>>


\* Combine all actions into a Next action
Next == \/ Read1
        \/ Inc1
        \/ Read2
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
          /\ thread1[1] \in ThreadPC
          /\ thread1[2] \in Nat \cup {UNDEFINED}
          /\ thread2[1] \in ThreadPC
          /\ thread2[2] \in Nat \cup {UNDEFINED}
THEOREM Spec => []TypeOK

\* Invariant: Counter between 0 and 2
CounterOK == counter \in 0..2
THEOREM Spec => []CounterOK

\* Helper definition stating that all threads are done
Done == thread1[1] = "done" /\ thread2[1] = "done"

\* Liveness: Eventually, all threads are done and the counter is 2
\* This property will be violated, yielding a behavior with counter=1
Counter2 == <>(Done /\ counter = 2)
THEOREM Spec => Counter2

\* Invariant: Never end up with a final value = 0
NotDoneAndZero == ~(Done /\ counter = 0)
THEOREM Spec => []NotDoneAndZero
====