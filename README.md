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
    - We model the execution of a system as a series of states.
    - A specification of a system describes the set of legal executions.
    - A specification does NOT provide instructions on _how_ to transition
      states, just which state transitions are legal.
    - Play clip: https://youtu.be/6cAbgAaEOVE.
    - EXTENDS is like import.
    - We model the state of the system with two variables, big and small.
    - Note that TLA+ is untyped.
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
    - Atomic commit is the problem where a set of nodes are all initially
      assigned a value 0 or 1. They must all agree to abort or commit. The
      nodes can only agree to abort if all initial values are 1.
    - Explain Constants and assumptions.
    - Explain functions.
    - Explain \A and \E.
    - Explain EXCEPT.
    - Explain /=.
    - Explain specs.
    - Explain theorem.
    - Note that we haven't really specified a system. We've specified the legal
      behaviors allowed by a particular problem, namely atomic commit.
- TwoPhaseCommit
    - Now, we'll look at a particular implementation of atomic commit, namely
      two-phase commit.
    - Explain tuples.
    - Explain records and messages. Messages never dropped.
    - I said two-phase commit implements atomic commit, but what do I mean by
      that? Can we formalize that?
    - Draw execution of two-phase commit, erase everything that is not state.
      The theorem says that anything satisfying the two-phase commit spec also
      satisfies the atomic commitment spec.

## Limitations and Alternatives
- Model checking is not theorem proving.
    - Model checkers exhaustively enumerate executions looking for errors, but
      they're not proving anything about the correctness of your specification.
    - If there are infinite executions, you cannot check all of them.
    - Even if TLC does terminate, it often depends on a choice of constants.
    - Anecdote: [Generalized Paxos][genpaxos] has a TLA+ specification, but [a
      later paper][FGGC_tr] shows that this definition is incorrect (see 6.3)!
    - There is no substitute for a simple proof.
- TLA+ is for specifications, not for implementations.
    - You can't run TLA+ specs. Even if your specification is correct, you may
      implement it incorrectly.
    - Need to resort to automated theorem proving for really being confident
      that code is bug free.
- TLC can be slow, really slow
    - I ran TLC on my BPaxos stuff on 64 cores for hours and I exhausted 16 GB
      of disk before it could finish. Could take days to simulate.
    - See https://lamport.azurewebsites.net/video/video7-script.pdf slide 200.
- Sometimes hard to check if your system is doing what you expect.
    - Your specification might accidentally be disallowing certain actions that
      you think should be legal.
    - Your invariants are satisfied, so it's hard to tell when this is
      happening.
    - Liveness constraints can help discover this.
- Levels of testing:
    - unit tests
    - quickcheck
    - model checking
    - automated theorem proving

## Other Things
- Constant expression vs state expression vs action expression vs temporal
  formula
- Liveness
- More advanced forms of refinement
- PlusCal
- TLAPS

## Resources
- [Specifying Systems](https://lamport.azurewebsites.net/tla/book.html)
- [Introduction to TLA+ Model Checking in the Command Line][command_line]
- [TLA+ in Practice and Theory](https://pron.github.io/tlaplus)
- [Practical TLA+](https://www.apress.com/gp/book/9781484238288)
- [Standard Library][stdlib]

[amazon_cacm]: https://cacm.acm.org/magazines/2015/4/184701-how-amazon-web-services-uses-formal-methods/fulltext
[genpaxos]: https://www.microsoft.com/en-us/research/wp-content/uploads/2016/02/tr-2005-33.pdf
[FGGC_tr]: https://drive.google.com/file/d/0BwFkGepvBDQoRjNYRGJTdWQ0SzA/view
[command_line]: https://medium.com/@bellmar/introduction-to-tla-model-checking-in-the-command-line-c6871700a6a2
[stdlib]: https://github.com/tlaplus/tlaplus/tree/8bc89d303ce22a96f401104feed7452ba49111ef/tlatools/src/tla2sany/StandardModules
