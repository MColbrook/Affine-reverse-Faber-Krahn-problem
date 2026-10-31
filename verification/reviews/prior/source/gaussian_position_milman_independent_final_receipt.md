# Independent AI final source-evidence receipt

This closes the actual source-checking evidence for my complete non-author
mathematical review of the four root-authored proofs in
`AffineFK/GaussianPositionMilman.lean`. The earlier mathematical review and its
provisional JSON remain unchanged:

- `gaussian_position_milman_independent_review.md`, SHA-256
  `ed84a0a78e541c10af7d1801e310efaf3916ced7a70947b9281e07df129ea368`;
- `gaussian_position_milman_independent_review.json`, SHA-256
  `2f17a010244540dc625229af8deeb90c9f8d355d5c9a96fa92f80973b72d5c22`.

I found no mathematical, statement-fidelity, domain, constant or clarity defect.
The source remains exactly
`b990cd79d2de0dd6c045fd7189ff048846d9cc1561fab557fa1e0b45655e3958`.
The actual frozen source manifest is
`d7792769ac62f432029529a687ec9a65df67a1d951b92a35574ba1820a256d9b`.
The read-only audit
`audit/review_gaussian_position_milman_final_evidence.py` passed all **989**
source/probe pins, the two actual fetched logs, and all four fresh axiom reports.
It also compared both local logs byte-for-byte with the supplied evidence
archive. It ran no compiler, generator or checker.

The actual commands used the pinned Lean `4.35.0-rc3` Lake executable at
`/home/mjc249/.elan/toolchains/leanprover--lean4---v4.35.0-rc3/bin/lake`:

| Command suffix | Actual result | Log under `logs/branch_bochner/` |
|---|---|---|
| `build AffineFK.GaussianPositionMilman` | exit 0; 7.995 s | `gaussian-position-milman-main-build-01.txt` |
| `env lean audit/probes/GaussianPositionMilmanAxioms.lean` | exit 0; 7.009 s | `gaussian-position-milman-axioms-01.txt` |

The build log pins the exact final source and contains the actual successful
module compilation. The axiom log pins the exact frozen manifest and probe.
Each of the four actual `#print axioms` reports contains only `propext`,
`Classical.choice` and `Quot.sound`:

- `gaussianPosition_mahler_volume_product`;
- `gaussianPosition_dilated_polar_uniform_volume_lower`;
- `gaussianPosition_uniform_volume_one_ellipsoid_intersection`;
- `affine_reverse_faber_krahn`.

The separate final structured receipt is
`audit/gaussian_position_milman_independent_final_receipt.json`, SHA-256
`d5d5d1836fd6c9c534d5bb76c22afb7738a56edee3229a6947138de3e1716c73`.
It records the exact command, hash, exit code and time for each log.

The mathematical conclusion of this source branch is now unconditional: the
actual Mahler product gives the required uniform dilated-polar volume, the
genuine area/tilt construction gives the universal volume-one ellipsoid
intersection, and the previously proved analytic and affine reductions give
the original main theorem with a universal positive constant before dimension
and body. No output-geometric or output-spectral assumption remains in that
final theorem. All author/reviewer boundaries from the mathematical review
remain in force, including my header-only upstream port and reused-tilt
authorship.

This receipt closes source compilation and allowed-axiom evidence. It does not
infer the separate own Stage34 Mahler or final-main Comparator/six-kernel gate,
human review, or verification of every statement in the paper.
