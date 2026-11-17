# Complexity verification in Dafny

This project uses Dafny to verify computational complexity properties,
with the NP-complexity of Set Cover, Hitting Set and CDPC as case studies.

## Repository map

| Directory | Contents |
| --- | --- |
| `Problems/` | Problem definitions and related lemmas. |
| `Verifications/` | Certificate checkers and their proofs. |
| `Reductions/` | Mathematical reductions. |
| `Transformations/` | Executable problem transformations. |
| `Collections/` | Collection traits and concrete implementations. |
| `Arithmetic/` | Scalar arithmetic, binary lengths and costed native operations. |
| `Foundations/` | Shared ghost models, representation contexts and mathematical/cost proofs. |

## Verification

This project uses Dafny 4.11.0. Every proof verifies in under 60 seconds. You can
verify directly in your IDE, or, with `dafny` available on PATH, run from the
repository root e.g.:

```powershell
dafny verify --verification-time-limit 60 Verifications/VerificationSetCover.dfy
```
