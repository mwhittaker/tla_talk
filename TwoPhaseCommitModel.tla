-------------------------- MODULE TwoPhaseCommitModel --------------------------

EXTENDS TwoPhaseCommit, TLC

CONSTANT n1, n2, n3
N == {n1, n2, n3}
Symmetry == Permutations(N)
I == n1 :> 1 @@ n2 :> 1 @@ n3 :> 1
ACSpec == AC!Spec

================================================================================
