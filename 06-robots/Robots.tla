---- MODULE Robots ----
EXTENDS Integers, FiniteSets

(*
Module for robots moving on a square grid.
This model is not complete (it can deadlock).
Once you understand the model, try to find a way to remove the potential deadlock.
*)

\* GridSize is a number, Robots a set (of model values), and UNDEFINED a model value
CONSTANTS GridSize, Robots, UNDEFINED

\* Positions on the grid as a cartesian product
Positions == (1..GridSize) \X (1..GridSize)
\* Helper functions for grid positions
abs(x) == IF x < 0 THEN -x ELSE x
IsAdjacent(p1, p2) == abs(p1[1] - p2[1]) + abs(p2[2] - p2[2]) = 1

(* Status of a robot:
 - thinking: robot is planning its next move (after completing its previous move)
 - waitForReservation: robot decided where to go, and is waiting for a reservation for that square
 - readyToMove: robot acquired the reservation, and is ready to start moving *)
RobotStatuses == { "thinking", "waitForReservation", "readyToMove" }

\* Model variables: state of all robots (a function), and the reservations per robot (a function)
VARIABLES robotState, reservations
vars == <<robotState, reservations>>

----
\* Helper definitions

\* The set of all possible robot state functions.
\* Each robot has its own state record. The next position can be undefined.
AllRobotStates == [Robots -> [status: RobotStatuses,
                              current: Positions,
                              next: Positions \cup {UNDEFINED}]]

\* Helper operators to get state values for a robot
CurrentPosition(robot) == robotState[robot].current
NextPosition(robot) == robotState[robot].next
Status(robot) == robotState[robot].status

\* Expresses that no two robots are on the same position (should be an invariant of the model)
NoOverlap == \A r1, r2 \in Robots : r1 # r2 => CurrentPosition(r1) # CurrentPosition(r2)

\* The set of all initial robot states (records):
\* status = "thinking", the robot can be at any position, and next is undefined
InitialRobotStates == [status: {"thinking"},
                       current: Positions,
                       next: {UNDEFINED}]

\* Operators to check if a position is reserved or not                           
IsReservedBy(pos, robot) == pos \in reservations[robot]
IsReserved(pos) == \E r \in Robots : IsReservedBy(pos, r)

\* Operators to add/remove a reservation.
Acquire(robot, pos) == reservations' = [reservations EXCEPT ![robot] = @ \cup {pos} ]
Release(robot, pos) == reservations' = [reservations EXCEPT ![robot] = @ \ {pos} ]

----

(* Initial situation: 
   - every robot is at some position (without overlap),
   - every robot holds a reservation for its own position (and nothing else)
   - every robot is idle and has a goal position
*)
Init == /\ robotState \in [Robots -> InitialRobotStates]
        /\ NoOverlap
        /\ reservations = [r \in Robots |-> {CurrentPosition(r)}]

(* Action: decide on the next position to go to.
   Can only happen in the 'thinking' state, and a robot can only move to an adjacent square
   Successful execution puts the robot into 'waitForReservation' state.
*)
PickNextPosition(robot, nextPos) == 
    /\ robotState[robot].status = "thinking"
    /\ IsAdjacent(CurrentPosition(robot), nextPos)
    /\ robotState' = [robotState EXCEPT ![robot] = [@ EXCEPT !.next = nextPos, !.status = "waitForReservation"]]
    /\ UNCHANGED reservations

(* Action: make a reservation for the next position.
   This is only possible if the robot is in the 'waitForReservation' state,
   and the next position hasn't been reserved yet by another robot (to be enforced by the central reservation manager).
   Successful execution puts the robot in the 'readyToMove' status.
*)
MakeReservation(robot) == LET nextPos == NextPosition(robot) IN
    /\ robotState[robot].status = "waitForReservation"
    /\ ~IsReserved(nextPos) \* Only allow reservations when square not yet reserved
    /\ Acquire(robot, nextPos)
    /\ robotState' = [robotState EXCEPT ![robot] = [@ EXCEPT !.status = "readyToMove"]]

(* Action: move the robot to its next position, and release the reservation for its previous position.
   Can only happen in the 'readyToMove' state.
   Successful execution puts the robot back into the 'thinking' status. *)
MoveToNext(robot) ==
    /\ robotState[robot].status = "readyToMove"
    /\ robotState' = [robotState EXCEPT ![robot] = [@ EXCEPT !.current = NextPosition(robot), !.next = UNDEFINED, !.status = "thinking"]]
    /\ Release(robot, robotState[robot].current) \* release reservation of previous position after moving

(* Combine the 3 possible actions into one Next operator *)
Next == 
    \/ \E r \in Robots : MoveToNext(r)
    \/ \E r \in Robots, p \in Positions : PickNextPosition(r, p)
    \/ \E r \in Robots : MakeReservation(r)

(* Spec combines Init and Next *)
Spec == Init /\ [][Next]_vars

----
\* Invariant: Types are always as expected
TypeOK == /\ robotState \in AllRobotStates
          /\ reservations \in [Robots -> SUBSET Positions]
THEOREM Spec => []TypeOK

\* Invariant: Robots never collide
THEOREM Spec => []NoOverlap

\* Invariant: Every robot holds at most 2 reservations.
Max2Reservations == \A r \in Robots : Cardinality(reservations[r]) <= 2
THEOREM Spec => []Max2Reservations
====