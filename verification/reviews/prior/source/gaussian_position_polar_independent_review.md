# Independent AI review: polar geometry and coordinate volume transport

Reviewer: `/root/formalization_coverage`. Proof author: `/root/claim_inventory`.
This is a non-author AI mathematical, statement-fidelity and clarity review. I read
all 19 new theorem headers and complete proof bodies. I found no mathematical,
polarity, norm, Haar normalization, dimension, conversion, constant or trust defect.

The reviewed frozen sources are:

| Source | New theorems | SHA-256 |
|---|---:|---|
| `AffineFK/GaussianPositionPolarGeometry.lean` | 9 | `35994e7ba025daf077fcccead88d0ea538cd77a55e1a456a9af0f03b581426b8` |
| `AffineFK/GaussianPositionCoordinatePolar.lean` | 4 | `d1ad9180995ddbbc01e0b6bb5e514328733bd99df1573428e1ef952f4eb57abb` |
| `AffineFK/GaussianPositionPolarVolumeTransport.lean` | 6 | `e449cdc288bfa493b5ebc675ab7809732d127af704fc140d741ba5ad0f97e932` |

There are no new data definitions in this branch. The actual objects are the
standard Euclidean space, Mathlib's absolute polar for its real inner bilinear
form, the ordinary finite-coordinate vector space, and their standard Haar
volumes.

## Mathematical review

The polar is literally `(innerₗ E).polar K`. Closedness and convexity follow from
intersections of preimages of the real closed unit ball under actual continuous
linear functionals. Absolute polarity gives symmetry for every input set.
Cauchy–Schwarz gives the proved inner-ball inclusion from a genuine norm bound
on `K`. Conversely, testing a polar vector against its normalized vector of norm
`r / 2` gives the outer-ball bound `2 / r` when `ball 0 r ⊆ K`. The zero vector is
handled separately, and the strict open-ball condition is respected.

For an actual compact, convex, origin-symmetric body with nonempty interior, the
existing zero-in-interior result and these two ball estimates give an actual
compact polar with nonempty interior. The positive, finite Haar volume and
positive real volume have the required measurability and finiteness guards.
The dilation identities use exact Haar scaling by `n ^ n`, in both `ENNReal` and
real form. The identities retain the dimension-zero convention; the theorem
asserting preservation of nonempty interior under the nonzero dilation correctly
requires `0 < n`.

The coordinate polar is one-sided. Its equality with the absolute inner polar
uses the stated symmetry hypothesis and applies the bound to both `x` and `-x`.
The coordinate pairing agrees with the actual Euclidean inner product. The
`PiLp` continuous linear equivalence transports compactness, convexity, symmetry
and interior. Crucially, the volume comparison uses the genuine
`PiLp.volume_preserving_toLp` and `PiLp.volume_preserving_ofLp` theorems. Both Haar
volumes, and then their product, agree exactly; no norm-dependent comparison
factor is substituted.

The final arithmetic theorem explicitly assumes an actual volume-product lower
bound. Together with `Nat.factorial_le_pow`, it proves the exact conclusion
`4 ^ n ≤ volume.real (n • polar K)`. Its real conversions do not rely on invalid
monotonicity through infinity. No Stirling approximation or native numerical
execution is involved. This branch does not itself prove the assumed
volume-product bound or universal ellipsoid existence.

## Reuse and attribution

I checked the relevant primary Mathlib definitions and declarations at the pinned
Mathlib revision `b63f6e8a68d220e3b3bc4f3792bb53650d375f24`, including:

- `LinearMap.polar` and `LinearMap.polar_eq_biInter_preimage` in
  `Mathlib/Analysis/LocallyConvex/Polar.lean` (Moritz Doll and Kalle Kytölä);
- `Measure.addHaar_smul_of_nonneg` in the Lebesgue/Haar development;
- `PiLp.volume_preserving_toLp` and `PiLp.volume_preserving_ofLp` in
  `Mathlib/MeasureTheory/Measure/Haar/InnerProductSpace.lean`;
- the actual `PiLp` equivalence and inner-product correspondence, and
  `Nat.factorial_le_pow`.

The source attribution remains that of Mathlib and the new proof author. These
19 proofs import no upstream Mahler proof. I authored none of the 19 new proofs.
Reused frozen interior/geometric foundations are outside the new independent
mathematical-review claim here and retain their separately recorded provenance.

## Actual checking evidence

The read-only audit `audit/review_gaussian_position_polar.py` passed with 34
distinct frozen file pins, eight actual raw logs, and all 19 fresh axiom reports.
Its structured record is
`audit/gaussian_position_polar_independent_review.json`, SHA-256
`587eca851d0ae79c813e4a81ae4a7a4b844b49cc0f1f60f87f5118fd87d7e3e4`.
The source manifests are pinned at
`4c32353471a574c681087bbd060aed1f8c55cc64463797ea8fbd978aebe124bf`
(geometry) and
`46f5d04f7429429704401d1b0828d83b8724e7b5c3c8611bc892db110550d23c`
(coordinate/volume transport). The corresponding handoffs are also checked in
that JSON.

The actual commands used the Lean `4.35.0-rc3` Lake executable at
`/home/mjc249/.elan/toolchains/leanprover--lean4---v4.35.0-rc3/bin/lake`:

| Command suffix | Actual result | Raw log under `logs/branch_polar_geometry/` |
|---|---|---|
| `build AffineFK.GaussianPositionPolarGeometry` | exit 0, 8.505 s | `source-build-02.txt` |
| `env lean audit/probes/GaussianPositionPolarGeometryAxioms.lean` | exit 0, 4.837 s; 9 reports | `axioms-01.txt` |
| `build AffineFK.GaussianPositionPolarVolumeTransport` | exit 0, 7.526 s | `coordinate-volume-build-03.txt` |
| `env lean audit/probes/GaussianPositionCoordinatePolarAxioms.lean` | exit 0, 6.514 s; 10 reports | `coordinate-axioms-01.txt` |

The coordinate source itself compiled successfully as a child of the otherwise
failed second volume-target build. The preserved attempt-02 coordinate bytes
equal the final `d1ad9180…` source. The later explicit coordinate source receipt
(`coordinate-final-source-build-01.txt`, exit 0, 5.350 s) is correctly identified
as cached; I do not represent it as a fresh recompilation. All failed attempts
and their exact source states remain in the author history.

Each actual `#print axioms` report contains only `propext`, `Classical.choice`
and `Quot.sound`. No `sorry`, custom axiom or native-execution trust supports
these source proofs. I ran no new Lean or Comparator check during this review.

This source review is not a human review, a six-kernel acceptance certificate, an
unconditional Mahler or Milman theorem, or verification of the whole manuscript.
