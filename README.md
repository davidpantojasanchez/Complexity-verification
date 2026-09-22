# Complexity verification in Dafny

This project develops a Dafny methodology for computer-assisted verification of
computational-complexity arguments. Set Cover is the main case study: certificate
checking, correctness of the Hitting Set reduction, and polynomial bounds on
abstract operation counters. Multiplicity-based binary CDPC is an ongoing second case study;
its instances carry the finite question set explicitly alongside fitness,
multiplicity, private questions and the four thresholds.

No end-to-end bit-complexity or absolute NP-completeness theorem is established.
The Set Cover to CDPC correctness proof is unfinished and currently contains
proof bypasses.

## Repository map

| Directory | Purpose |
| --- | --- |
| `Problems/` | Mathematical definitions of Set Cover, Hitting Set and multiplicity-based binary CDPC. |
| `Verifications/` | Certificate checkers and cost proofs; CDPC ghost helpers live in `VerificationCDPC_aux.dfy`. |
| `NPMembership/` | Representation contracts for NP arguments; Set Cover uses an ordered family and Boolean selection certificates. Construction and the composed checker are pending. |
| `Reductions/` | Mathematical transformations and correctness arguments, including unfinished Set Cover → CDPC. |
| `PolyTransformations/` | Executable Hitting Set → Set Cover and Set Cover → CDPC transformations, with cost analyses. |
| `Auxiliary/` | Abstract traits, immutable implementations, cost models and reusable lemmas grouped into arithmetic, native-collection, trait and cost layers; `Example.dfy` is a standalone Fibonacci example. |

The Set Cover checker and Hitting Set → Set Cover transformation have three
variants: `_base` has functional correctness without costs, `_simple` has explicit
author-written costs, and the unsuffixed default uses instrumented interfaces.
CDPC does not have this trio.

Instrumented nested collections use specialized interfaces such as `SetSet`,
`Map_Map_T`, `Map_Set_T` and `Map_MapSet_T`: comparisons use contents and the
cost model accounts for every represented nesting level. The executable
Set Cover → CDPC transformation has a degree-four collection-counter bound;
its functional correctness remains pending.

## Mathematical scope

Set Cover instances require the complete set family to cover the universe; the
budget `k` may be any natural number. Each problem exposes instance validity and
certificate correctness. Set Cover checkers assume simple certificate-size bounds;
the CDPC checker rejects oversized interviews with an initial bounded traversal.
Lemmas prove that every correct certificate satisfies the size bounds, so this
rejection preserves positive certificates. Public cost bounds depend only on the
instance; efficient validation or construction of the required representations
remains a separate obligation for a complete NP argument.
Correct CDPC interviews have at most `2*M*Q + 1` nodes, for `M` candidate types
and `Q` questions. These results use abstract collection costs. Encodings and
bit-complexity bounds remain open.

## Verification

The project uses Dafny 4.11.0. You can verify directly in your IDE, or, with
`dafny` available on PATH:

```powershell
dafny verify --verification-time-limit 60 Verifications/VerificationSetCover.dfy
```

The limit applies per verification obligation. Verify dependencies separately as
well: checking a file does not verify the bodies of its included declarations.
For example, the CDPC checker and its proof helpers are checked with:

```powershell
dafny verify --verification-time-limit 60 Verifications/VerificationCDPC_aux.dfy
dafny verify --verification-time-limit 60 Verifications/VerificationCDPC.dfy
```
