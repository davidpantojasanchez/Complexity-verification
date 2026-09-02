# Complexity verification in Dafny

This project develops a Dafny methodology for computer-assisted verification of
computational-complexity proofs, currently focused on NP-completeness. Set Cover
is the case study: the repository verifies its certificate checker, the
correctness of a reduction from Hitting Set, and polynomial upper bounds for the
checker and reduction.

## Repository map

- `Problems/`: mathematical problem definitions.
- `Problems/CDPC.dfy`: weighted binary CDPC semantics and certificate relation.
- `Reductions/`: functional correctness of reductions in both directions.
- `Verifications/`: complete interface-based certificate verifiers, including
  Set Cover variants and the unsuffixed `VerificationCDPC.dfy` default.
- `HittingSetToSetCover/`: executable Hitting Set to Set Cover transformation.
- `Auxiliary/Set.dfy`: abstract set interfaces and operation-cost model.
- `Auxiliary/ConcreteSet.dfy`: concrete immutable-set implementations.
- `Auxiliary/Interview.dfy`: binary CDPC interview model and abstract interface.
- `Auxiliary/ConcreteInterview.dfy`: immutable interview implementation and factory.
- `Auxiliary/Lemmas.dfy`: reusable proof lemmas.
- `Experiments/`: verified, non-production investigations; see the
  [nested-collection abstraction report](Experiments/README.md).

The analysis directories contain three versions:

- `_base`: functional proof without costs.
- `_simple`: costs written explicitly by the algorithm author.
- `_interfaces`: costs obtained through the abstract set interfaces.
