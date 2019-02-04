----------------------------- MODULE AtomicCommit ------------------------------

EXTENDS Integers, FiniteSets

CONSTANT Node
ASSUME IsFiniteSet(Node)

CONSTANT Input
ASSUME Input \in [Node -> {0, 1}]

VARIABLE state

TypeOk ==
  /\ state \in [Node -> {"pending", "committed", "aborted"}]

Commit(n) ==
  /\ \A m \in Node : Input[m] = 1
  /\ \A m \in Node : state[m] /= "aborted"
  /\ state' = [state EXCEPT ![n] = "committed"]

Abort(n) ==
  /\ \A m \in Node : state[m] /= "committed"
  /\ state' = [state EXCEPT ![n] = "aborted"]

Init ==
  /\ state = [n \in Node |-> "pending"]

Next ==
  \/ \E n \in Node : Commit(n)
  \/ \E n \in Node : Abort(n)

Spec == Init /\ [][Next]_state

AllAgree ==
  ~ \E n, m \in Node: state[n] = "committed" /\ state[m] = "aborted"

ValidCommit ==
  (\E n \in Node : state[n] = "committed") => (\A n \in Node : Input[n] = 1)

THEOREM Spec => [](TypeOk /\ AllAgree /\ ValidCommit)

================================================================================
