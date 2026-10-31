# Affine reverse Faber–Krahn inequalities in Lean

This repository proves the three principal results of *An affine reverse
Faber–Krahn inequality via information decay*, by Matthew J. Colbrook and
George Stepaniants.

| Result | Conclusion |
| --- | --- |
| M01: affine reverse Faber–Krahn | One universal positive constant bounds `λ₁(SK) |K|^(2/n)` by `C n`, for every positive dimension and convex body, with an actual determinant-one linear map `S`. |
| M02: Gaussian position | Every origin-symmetric volume-one convex body in maximal Gaussian measure position satisfies `λ₁(K) ≤ C n`, with a universal constant. |
| M03: information to spectrum | For each `P ≥ 2`, one constant `C(P)` gives `λ₁(D) ≤ C(P)(n + √(n I(ν∣γ)))` for the original even isotropic log-concave laws, Poincaré bound, finite relative information and symmetric supporting bodies. |

The selected declaration is
`AffineFK.affine_reverse_faber_krahn_principal_results`, with conjunction
`(M01 ∧ M02) ∧ M03`. Its complete conventional definitions and statement
are in [Challenge.lean](Challenge.lean); its genuine proof is in
[Solution.lean](Solution.lean). Solution imports two proof endpoints and
their 992 source modules under `AffineFK/`. All 992 are unchanged copies of
the previously checked development. No geometric, groundstate or desired
spectral conclusion is an extra hypothesis.

The eigenvalue is the genuine variational infimum on the closure of compact
smooth Dirichlet tests in the value–gradient graph. No smooth-boundary
assumption is imposed. The relative Fisher functional uses the actual
Radon–Nikodym density and square-root Sobolev energy; finiteness and
integrability guards precede real-valued conversions. See the
[correspondence table](docs/correspondence.md).

## Verification

The authoritative final package evidence is
[verification/certificate.json](verification/certificate.json), with actual
commands, outputs, source hashes and version pins. The independent AI reviews
and compiled statement/private-proof comparison are under `verification/`.
The final check uses ordinary Linux sandboxed Comparator and all six bundled
kernels: Lean paranoid, lean4lean, nanoda, con-leche, con-ron and Lean default.

Only `propext`, `Classical.choice` and `Quot.sound` are permitted.
Solution and its supporting proof sources contain no `sorry`, unproved
custom axioms or native-execution proof shortcuts. Challenge contains one
deliberate benchmark placeholder under the saved specification protocol;
Solution never imports it. `definition_names` is empty, so referenced fixed
definitions must be compared by their bodies. The placeholder count is
disclosed separately from the genuine proof development's zero count.

This verifies the three theorem conclusions. The
[proof-departure account](docs/proof-departures.md) identifies the manuscript
arguments retained, the stronger proved geometric input and alternative
variational arguments. The [scope account](docs/scope.md) lists excluded
background assertions. No full-manuscript or human-review certification is
asserted. AI proof construction and AI reviews are disclosed in
[formalization.yaml](formalization.yaml).

## Build and replay

The exact toolchain is Lean `v4.35.0-rc3`; Mathlib and its full dependency
graph are pinned in `lake-manifest.json`. Ordinary Comparator requires Linux
with `bwrap` and working user namespaces. This repository supplies proof
sources, not a bundled Mathlib cache or Lean installation.

After installing the pinned Lean toolchain, obtain the pinned dependencies
and Mathlib cache, then build from the repository root:

```sh
lake exe cache get
lake build
lake env lean AxiomAudit.lean
python3 scripts/check_package.py
lake comparator --config comparator.json --paranoid
```

The first command may download dependencies; no dependency fetching occurs
in the Python checking runner. For timestamped, non-overwriting raw output:

```sh
python3 scripts/run_checks.py diagnostics --output .verification/diagnostics-local
python3 scripts/inspect_diagnostics.py --input .verification/diagnostics-local --output .verification/diagnostics-local.json
python3 scripts/run_checks.py comparator --output .verification/comparator-local
```

The runner requires the pinned Linux x86_64 executable hashes and checks the
cached Mathlib revision before invoking real Lean tools. It keeps the ordinary
sandbox enabled. Each output directory must be new. The package checker is a
file-integrity and policy preflight; it does not replace Lean or the kernels.

## Repository contents

- `Challenge.lean`, `Solution.lean`, `AxiomAudit.lean`: the submission interface.
- `AffineFK/`: the exact proof-source import closure and retained source notices.
- `AuditTools/`: separate compiled-statement and private-proof inspection tools.
- `docs/`: theorem correspondence, proof departures, scope and attribution.
- `verification/`: actual checking evidence, independent AI reviews, saved
  protocol/schema, source hashes and selected upstream originals/differences.
- `source/manuscript.tex`: the frozen manuscript used for correspondence.
- `scripts/`: portable checking and integrity tools.

Development experiments, stopped PDE work, earlier submission packets,
compiled artifacts and caches are excluded. `.gitattributes` preserves exact
reviewed bytes across platforms. New formalization code and documentation
use Apache-2.0; the MIT source family and the manuscript retain their own
licences and rights. See [NOTICE](NOTICE) and
[third-party attribution](docs/third-party.md).

For the final upload and registry fields, see [SUBMISSION.md](SUBMISSION.md).
