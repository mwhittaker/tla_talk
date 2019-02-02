# TLA+ Talk

## Overview
TLA+ is a language for specifying concurrent and distributed systems and for
checking that these systems do what you expect. It has been used in industry:

    - See "Formal Methods for Real-World Systems" on Page 3 of [this CACM
      article][amazon_cacm].

and in academia:

    - Raft: https://ramcloud.stanford.edu/~ongaro/thesis.pdf
    - EPaxos: http://www.cs.cmu.edu/~imoraru/epaxos/tr.pdf
    - TAPIR: https://syslab.cs.washington.edu/papers/tapir-tr-v2.pdf

## Tutorial
Note that this tutorial is stolen from Leslie Lamport's excellent video course:
https://lamport.azurewebsites.net/video/videos.html. If you want to learn TLA+,
I recommend watching this series.

- DieHard
    - Play clip.
    - We model the execution of a system as a series of states.
    - A specification of a system describes the set of legal executions.
    - A specification does NOT provide instructions on _how_ to transition
      states, just which state transitions are legal.
    - We model the state of the system with two variables, big and small.
    - Init says the initial state of the system.
    - Next, we can specify formulas that describe legal state transitions.
    - A primed variable like small' represents the value of variable small in
      the next state.
    - Note that we have to constrain every variable. For example, if we did not
      constraint big' in FillSmall, then the value of big' could be anything.
    - /\ is conjunction, \/ is disjuntion.
    - Next is the disjunction of all our formula.
    - We can specify invariants for our executions. For example, small should
      be in the set {0, 1, 2, 3} and big should be in the range {0, 1, 2, 3, 4,
      5}.
    - TLC is a model checker. It checks that all executions of our system
      satisfy the invariants we claim.
    - Show cfg file.
    - Run TLC with TypeOk only.
    - Flipping invariant checking on our head, we can also find particular
      executions, like NotFourGallons.
    - Pause for questions.
- AtomicCommit

## Limitations and Alternatives

[amazon_cacm]: https://cacm.acm.org/magazines/2015/4/184701-how-amazon-web-services-uses-formal-methods/fulltext
