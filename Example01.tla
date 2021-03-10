----------------------------- MODULE Example01 -----------------------------

EXTENDS Integers

(*--algorithm wire
variables
    people = {"alice", "bob"},
    acc = [p \in people |-> 5],
    sender = "alice",
    receiver = "bob",
    amount = 3;

\* INVARIANTE    
define
    NoOverdrafts == \A p \in people: acc[p] >= 0
end define;

begin
    skip;
end algorithm;*)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-a569e391777147060068de8e45b9ff96 (chksum(pcal) = "837e18bd" /\ chksum(tla) = "dc417d61") (chksum(pcal) = "837e18bd" /\ chksum(tla) = "dc417d61") (chksum(pcal) = "837e18bd" /\ chksum(tla) = "dc417d61") (chksum(pcal) = "837e18bd" /\ chksum(tla) = "dc417d61") (chksum(pcal) = "837e18bd" /\ chksum(tla) = "dc417d61")
VARIABLES people, acc, sender, receiver, amount, pc

(* define statement *)
NoOverdrafts == \A p \in people: acc[p] >= 0


vars == << people, acc, sender, receiver, amount, pc >>

Init == (* Global variables *)
        /\ people = {"alice", "bob"}
        /\ acc = [p \in people |-> 5]
        /\ sender = "alice"
        /\ receiver = "bob"
        /\ amount = 3
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ TRUE
         /\ pc' = "Done"
         /\ UNCHANGED << people, acc, sender, receiver, amount >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Lbl_1
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-00db241003d28b71c47dff56c8b4c557

=============================================================================
\* Modification History
\* Last modified Tue Feb 09 19:44:26 CET 2021 by jesusmarin
\* Created Sat Oct 17 17:23:30 CEST 2020 by jesusmarin
