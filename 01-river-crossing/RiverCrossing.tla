---- MODULE RiverCrossing ----

Items == { "chicken", "fox", "corn", "farmer" } \* All items in the puzzle
Sides == { "left", "right" } \* The sides they can be on

VARIABLE itemsAt \* Function that keeps track of where each item is located
vars == <<itemsAt>> \* All variables (here only one)

----

\* Helper definitions
OtherSide(side) == IF side = "left" THEN "right" ELSE "left"
AtSameSide(item1, item2) == itemsAt[item1] = itemsAt[item2]
\* A state is unsafe is the chicken is left unattended with the fox or the corn
Unsafe == \/ /\ AtSameSide("chicken", "fox")
             /\ ~AtSameSide("chicken", "farmer")
          \/ /\ AtSameSide("chicken", "corn")
             /\ ~AtSameSide("chicken", "farmer")

----

\* Initial state: all on the left
Init == itemsAt = [ i \in Items |-> "left" ]

\* Action: only the farmer crosses.
\* Only allowed if the new state is not unsafe (note the prime).
CrossOnlyFarmer ==
    /\ itemsAt' = [itemsAt EXCEPT !["farmer"] = OtherSide(@)]
    /\ ~Unsafe'

\* Action: the farmer crosses together with an item.
\* Only allowed if the new state is not unsafe (note the prime).
CrossWithItem(item) ==
    /\ itemsAt' = [itemsAt EXCEPT ![item] = OtherSide(@),
                                  !["farmer"] = OtherSide(@)]
    /\ ~Unsafe'

\* Combine all actions (only farmer + cross with any item)
Next == \/ CrossOnlyFarmer
        \/ \E item \in Items : CrossWithItem(item)

\* The specification of the puzzle as a combination of Init and Next.
Spec == Init /\ [][Next]_vars

----
\* Invariant: Types are as expected
TypeOK == itemsAt \in [Items -> Sides]
THEOREM Spec => []TypeOK

\* Invariant: Never move into an unsafe state
Safe == ~Unsafe
THEOREM Spec => []Safe

\* To find a solution, we state an invariant that no solution is possible
\* A counterexample found by TLC then gives us the solution.
Solution == \A i \in Items: itemsAt[i] = "right"
NoSolution == ~Solution
====