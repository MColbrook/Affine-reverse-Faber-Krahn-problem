# Upload and Palomar submission

The repository root contains the submission files. Upload its contents as a
single Git repository, preserving file bytes and paths. Do not upload `.lake/`,
`.verification/`, Python environments or locally generated build files.

The submission settings are:

| Field | Value |
| --- | --- |
| Title | A formal proof of an affine reverse Faber-Krahn inequality |
| Authors | Matthew J. Colbrook; George Stepaniants |
| Challenge module | `Challenge` |
| Solution module | `Solution` |
| Selected theorem | `AffineFK.affine_reverse_faber_krahn_principal_results` |
| Comparator configuration | `comparator.json` |
| Metadata | `formalization.yaml` |
| Definition holes | None: `definition_names: []` |
| Permitted axioms | `propext`, `Classical.choice`, `Quot.sound` |
| Lean | `leanprover/lean4:v4.35.0-rc3` |
| Mathlib | `b63f6e8a68d220e3b3bc4f3792bb53650d375f24` |

After uploading, identify the public repository URL and the exact commit
containing these files. Use that public repository URL and exact uploaded
commit for the registry fields, together with the configuration path if
requested.

The actual package-check verdict and raw evidence are in
`verification/certificate.json`. Keep that evidence and the reviewed
Challenge unchanged. Any subsequent source/interface change needs its own
appropriate review and checking before its verdict can be advertised.

The policy basis is the saved 27 October 2026 requirements and benchmark
protocol, plus read-only inspection of the installed rc3 Lake implementation.
The exact saved v0.4 metadata schema is included. This prepared package has
not been uploaded or registered.
The registry's own policy and execution determine final registration.

## Included limits and trust checks

The package checker verifies the saved 1,000-physical-line and 100-KiB
Challenge hard limits and the 10,000-line limit for every compiled Lean
source. Blank and comment lines count. The 327-line Challenge exceeds the
saved 300-line advisory threshold, while remaining under the hard limit and
below 32 KiB; its reviewed data layout is retained for readability.

One isolated Challenge-only theorem placeholder is deliberate. Solution
and all 992 supporting proof-source files are genuine. The final ordinary
sandboxed Comparator check uses `--paranoid` and retains six individual
kernel verdicts. No disabled sandbox, checker bypass, custom axiom or native
execution result supports the proof.
