---------------------------- MODULE TwoPhaseCommit -----------------------------

EXTENDS Integers, FiniteSets

CONSTANT Node
ASSUME IsFiniteSet(Node)

CONSTANT Input
ASSUME Input \in [Node -> {0, 1}]

VARIABLE state
VARIABLE coordinatorState
VARIABLE msgs

vars == <<state, coordinatorState, msgs>>

Message ==
  [type: {"vote_commit"}, node: Node] \union
  [type: {"vote_abort"}, node: Node] \union
  [type: {"commit"}] \union
  [type: {"abort"}]

TypeOk ==
  /\ state \in [Node -> {"pending", "committed", "aborted"}]
  /\ coordinatorState \in {"pending", "committed", "aborted"}
  /\ msgs \in SUBSET Message

VoteCommit(n) ==
  /\ Input[n] = 1
  /\ msgs' = msgs \union {[type |-> "vote_commit", node |-> n]}
  /\ UNCHANGED <<state, coordinatorState>>

VoteAbort(n) ==
  /\ Input[n] = 0
  /\ msgs' = msgs \union {[type |-> "vote_abort", node |-> n]}
  /\ UNCHANGED <<state, coordinatorState>>

SendCommit ==
  /\ coordinatorState = "pending"
  /\ \A n \in Node : [type |-> "vote_commit", node |-> n] \in msgs
  /\ msgs' = msgs \union {[type |-> "commit"]}
  /\ coordinatorState' = "committed"
  /\ UNCHANGED state

SendAbort ==
  /\ coordinatorState = "pending"
  /\ msgs' = msgs \union {[type |-> "abort"]}
  /\ coordinatorState' = "aborted"
  /\ UNCHANGED state

Abort(n) ==
  /\ [type |-> "abort"] \in msgs
  /\ state' = [state EXCEPT ![n] = "aborted"]
  /\ UNCHANGED <<coordinatorState, msgs>>

Commit(n) ==
  /\ [type |-> "commit"] \in msgs
  /\ state' = [state EXCEPT ![n] = "committed"]
  /\ UNCHANGED <<coordinatorState, msgs>>

Init ==
  /\ state = [n \in Node |-> "pending"]
  /\ coordinatorState = "pending"
  /\ msgs = {}

Next ==
  \/ \E n \in Node : VoteCommit(n)
  \/ \E n \in Node : VoteAbort(n)
  \/ SendCommit
  \/ SendAbort
  \/ \E n \in Node : Abort(n)
  \/ \E n \in Node : Commit(n)

Spec == Init /\ [][Next]_vars

THEOREM Spec => TypeOk

AC == INSTANCE AtomicCommit
THEOREM Spec => AC!Spec

================================================================================
