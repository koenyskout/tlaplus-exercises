---- MODULE WaterPouring ----
EXTENDS Integers \* Import module to work with integers

Jugs == 1..3 \* Numbering the jugs

\* Define a function for the capacity of each jug
Capacity == [j \in Jugs |-> CASE j = 1 -> 8
                              [] j = 2 -> 5
                              [] j = 3 -> 3 ]

VARIABLE contents \* The contents of all jugs (a function)
vars == <<contents>>

----

\* Helper definition: remaining capacity of a jug
Remaining(jug) == Capacity[jug] - contents[jug]

----

\* Initial state: we start with 8 liters in jugs 1, and the others empty.
Init == contents = [j \in Jugs |-> IF j = 1 THEN 8 ELSE 0]

\* Action: Empty the 'from' jug completely.
\* Can only be done if the 'to' jug has enough remaining capacity.
\* We use a LET construct to name the amount we're pouring
Empty(from, to) == LET amount == contents[from] IN
    /\ Remaining(to) >= amount
    /\ contents' = [contents EXCEPT ![from] = @ - amount,
                                    ![to] = @ + amount]

\* Action: Fill up the 'to' jug completely.
\* Can only be done if the 'from' jug contains enough water
\* We use a LET construct to name the amount we're pouring
Fill(from, to) == LET amount == Remaining(to) IN
    /\ contents[from] > amount
    /\ contents' = [contents EXCEPT ![from] = @ - amount,
                                    ![to] = @ + amount]

\* Combine all actions (we empty or fill one of the jugs from another)
Next == \E from, to \in Jugs : \/ Empty(from, to)
                               \/ Fill(from, to)

\* The specification of the puzzle as a combination of Init and Next.
Spec == Init /\ [][Next]_vars

----

\* Invariant: Types are as expected
TypeOK == contents \in [Jugs -> 0..8]
THEOREM Spec => []TypeOK

\* Invariant: contents is positive and never exceeds capacity
ContentsOK == \A j \in Jugs : 0 <= contents[j] /\ contents[j] <= Capacity[j]
THEOREM Spec => []ContentsOK

\* Invariant: no water is lost
NoWaterLost == contents[1] + contents[2] + contents[3] = 8

(* If we want to make this formula independent of the number of jugs,
   we can do this by defining a recursive TotalContents operator that sums 
   the contents of a given set of jugs.
   Note how we can use CHOOSE to select any jug from the set *)
RECURSIVE TotalContents(_)
TotalContents(jugs) == IF jugs = {}
                       THEN 0
                       ELSE LET someJug == CHOOSE j \in jugs : TRUE IN
                            contents[someJug] + TotalContents(jugs \ {someJug})
NoWaterLost_alt == TotalContents(Jugs) = 8

THEOREM Spec => []NoWaterLost_alt

(* If we also want to remove the constant 8 from the formula, we can rephrase
   this as a temporal formula that states that the total contents doesn't change
   between states. We need to use the [][...]_vars here.
   Notice how we can just write TotalContents(Jugs)' to denote the total contents
   in the after state. *)
NoWaterLost_alt2 == [][TotalContents(Jugs)' = TotalContents(Jugs)]_vars


\* To find a solution, we state an invariant that no solution is possible
\* A counterexample found by TLC then gives us the solution.
Solution == contents = [j \in Jugs |-> CASE j = 1 -> 4
                                         [] j = 2 -> 4
                                         [] j = 3 -> 0 ]
NoSolution == ~Solution

====
