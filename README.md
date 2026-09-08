# Complexity verification in Dafny

This project develops a Dafny methodology for computer-assisted verification of
computational-complexity arguments. Set Cover is the main case study: certificate
checking, correctness of the Hitting Set reduction, and polynomial bounds on
abstract operation counters. Weighted binary CDPC is an ongoing second case study.

No end-to-end bit-complexity or absolute NP-completeness theorem is established.
The Set Cover to CDPC correctness proof is unfinished and currently contains
proof bypasses; consult the current status before using it.

## Repository map

| Directory | Purpose |
| --- | --- |
| `Problems/` | Mathematical definitions of Set Cover, Hitting Set and weighted binary CDPC. |
| `Verifications/` | Certificate checkers and cost proofs; CDPC ghost helpers live in `VerificationCDPC_aux.dfy`. |
| `Reductions/` | Mathematical transformations and correctness arguments, including unfinished Set Cover → CDPC. |
| `PolyTransformations/` | Executable Hitting Set → Set Cover transformations and cost analyses. |
| `Auxiliary/` | Abstract traits, immutable implementations, cost models and reusable lemmas; `Example.dfy` is a standalone Fibonacci example. |

The Set Cover checker and Hitting Set → Set Cover transformation have three
variants: `_base` has functional correctness without costs, `_simple` has explicit
author-written costs, and the unsuffixed default uses instrumented interfaces.
CDPC does not have this trio.

Set Cover definitions, reductions and checkers use valid instances whose complete
set family covers the universe. The budget `k` is any natural number, without an
upper bound. Checkers test certificate correctness; instance validity is a
precondition. Contracts distinguish instance validity, basic certificate
admissibility, and certificate correctness. Admissibility bounds Set Cover member
sizes, Hitting Set certificate size, and CDPC tree question labels. It does not
assume a solution. Set Cover checkers require admissibility; CDPC checks actual
question labels through CheckInterviewFits without assuming their admissibility.
Representation conditions remain separate. Witness-preservation
lemmas are in `Auxiliary/Lemmas.dfy`; encodings and polynomial CDPC witness size
remain open.

## Working documentation

Start with [agent instructions](AGENTS.md), then
[current state and verification](project-info/PROJECT_STATE.md) and
[active decisions](project-info/DECISIONS.md).
[Future work](project-info/FUTURE_WORK.md) records open work and observed defects;
[the changelog](project-info/CHANGELOG.md) records completed changes.

These support files are local: `.gitignore` excludes `AGENTS.md`, `project-info/`,
`Experiments/` and `CDPC_reference/`. A clone does not receive them through the
current tracked tree. Experiments are optional evidence; the CDPC reference is
read-only historical material.

## Verification

The local toolchain is Dafny 4.11.0. Verify sources separately, including proof
helper files, with a 60-second limit per obligation:

```powershell
dafny verify --verification-time-limit 60 Verifications/VerificationSetCover.dfy
```

With local support files available, also run `./project-info/verify-all.ps1`.
It locates Dafny through `DAFNY_EXE`, PATH, or the VS Code extension. It currently
stops at its policy scan because proof bypasses occur in both the historical
reference and the active CDPC reduction. Its `-Files` option does not restrict
that scan. See `PROJECT_STATE.md` for the exact validation scope.
