----------------------------- MODULE Example03 -----------------------------

EXTENDS Integers

(*--algorithm wire
variables
    people = {"alice", "bob"},
    acc = [p \in people |-> 5],
    sender = "alice",
    receiver = "bob",
    \* amount \in 1..6; \* HA CAMBIADO AMOUNT. POSIBLE FIX:
    amount \in 1..acc[sender];
    
define
    NoOverdrafts == \A p \in people: acc[p] >= 0
end define;

begin
    Withdraw:
        acc[sender] := acc[sender] - amount;
    Deposit:
        acc[receiver] := acc[receiver] + amount;
end algorithm;*)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-605fa74deafda7b3c8f3567c8e535957 (chksum(pcal) = "3730e780" /\ chksum(tla) = "b24e463b") (chksum(pcal) = "f8cc1ca0" /\ chksum(tla) = "ec090ae7") (chksum(pcal) = "3730e780" /\ chksum(tla) = "b24e463b") (chksum(pcal) = "f8cc1ca0" /\ chksum(tla) = "ec090ae7") (chksum(pcal) = "3730e780" /\ chksum(tla) = "b24e463b") (chksum(pcal) = "f8cc1ca0" /\ chksum(tla) = "ec090ae7")
VARIABLES people, acc, sender, receiver, amount, pc

(* define statement *)
NoOverdrafts == \A p \in people: acc[p] >= 0


vars == << people, acc, sender, receiver, amount, pc >>

Init == (* Global variables *)
        /\ people = {"alice", "bob"}
        /\ acc = [p \in people |-> 5]
        /\ sender = "alice"
        /\ receiver = "bob"
        /\ amount \in 1..acc[sender]
        /\ pc = "Withdraw"

Withdraw == /\ pc = "Withdraw"
            /\ acc' = [acc EXCEPT ![sender] = acc[sender] - amount]
            /\ pc' = "Deposit"
            /\ UNCHANGED << people, sender, receiver, amount >>

Deposit == /\ pc = "Deposit"
           /\ acc' = [acc EXCEPT ![receiver] = acc[receiver] + amount]
           /\ pc' = "Done"
           /\ UNCHANGED << people, sender, receiver, amount >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Withdraw \/ Deposit
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-c7e8d0cd79370ddf52496be81b058fde

=============================================================================
\* Modification History
\* Last modified Fri Mar 05 11:54:23 CET 2021 by jesusmarin
\* Created Sat Oct 17 17:32:10 CEST 2020 by jesusmarin
