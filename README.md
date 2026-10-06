# Complexity verification in Dafny

This project uses Dafny to verify correctness and computational-complexity
properties for certificate checkers and problem transformations, with Set Cover,
Hitting Set and CDPC as case studies.

## Repository map

| Directory | Contents |
| --- | --- |
| `Problems/` | Problem definitions and related lemmas. |
| `Verifications/` | Certificate checkers and their proofs. |
| `Reductions/` | Mathematical reductions. |
| `Transformations/` | Executable problem transformations. |
| `Collections/` | Collection traits and concrete implementations. |
| `Lemmas/` | Reusable mathematical and cost lemmas. |
| `Examples/` | Standalone examples and simpler checker variants. |
| `Tests/` | Verification regression checks. |
| `Experiments/` | Exploratory and historical work. |

## Verification

This project uses Dafny 4.11.0. You can verify directly in your IDE, or, with
`dafny` available on PATH, run from the repository root:

```powershell
dafny verify --verification-time-limit 60 Verifications/VerificationSetCover.dfy
```
