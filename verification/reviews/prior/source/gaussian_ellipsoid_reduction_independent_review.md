# Independent AI review: ellipsoid geometry to the affine conclusion

Reviewer: `/root/palomar_requirements` (AI).

The new definition and all three complete theorem statements and proof
bodies in `AffineFK/GaussianEllipsoidSpectralReduction.lean` were read.
No mathematical, domain, constant, finiteness or statement-fidelity
defect was found in the frozen final source. The actual final ordinary
build and four axiom reports passed. This review does not assert a new
Comparator verdict or an unconditional proof of M01.

## Independence boundary

The reviewer did not author these four parent-authored declarations.
The reviewer did author some imported Gaussian, Brownian, spectral
transport and affine-reduction proofs. This review independently checks
the four new declarations and their use of those interfaces; it is not
an independent mathematical review of the reviewer's own imported
proofs. The separate non-author review of the reused 14-declaration
affine reduction is
`audit/affine_spectral_reduction_independent_review.json`, SHA256
`f464751f6f156bad49c2c07b870616351cb98e0f2a665953d2b040df8d6f1309`.
Checking all 737 transitive source hashes is an evidence check, not a
claim that all 737 source files were reread mathematically for this
review.

## Complete statement and proof review

1. `UniformVolumeOneEllipsoidIntersection a` is an ordinary proposition
   definition. It quantifies over every positive integer dimension and
   every original compact convex origin-symmetric volume-one body with
   nonempty interior. It asks for an actual origin ellipsoid, represented
   as an invertible linear image of a positive-radius closed Euclidean
   ball, with actual volume one and intersection volume at least `a^n`.
   There is no spectral, covariance, log-concavity or affine-output
   premise. The single constant `a > 0` is quantified before the
   dimension and body in the final hypothesis. This is the geometric
   content of original G05. Its existence remains an explicit hypothesis.

2. `maximal_gaussian_covariance_of_ellipsoid_intersection` starts with
   supplied actual geometric data and an already maximal Gaussian
   position of the same `K`. The proved ellipsoid mass theorem gives a
   special-linear image with Gaussian mass at least
   `exp(-(1 + |E(a)|)*n)`. Maximality compares that image's actual measure
   with the actual measure of this same `K`; no unproved change of
   position or covariance transfer is used. Gaussian measure is finite,
   so the real-measure comparison is legitimate. Actual volume one
   implies positive Gaussian mass before conditioning. The conditional
   probability instance is then derived from that positivity.

   The previously proved conditional covariance theorem supplies one
   positive scalar `alpha` and zero coordinate means. Actual coordinate
   `L²` membership justifies `covariance_eq_sub`, so the proof obtains
   the genuine raw coordinate moment matrix `alpha*Id`. Convexity and
   symmetry justify the proved conditional Gaussian Poincare bound and
   hence `alpha <= 1`. The mass/covariance theorem then gives precisely
   `exp(-2*(1 + |E(a)|)-1) <= alpha`. The direction of maximality, the
   centered-to-raw conversion, nonzero conditioning event and exact
   exponential factor were checked.

3. `symmetric_gaussian_spectral_bound_of_ellipsoid_intersections` fixes
   `c = exp(-2*(1 + |E(a)|)-1)` before any dimension or body. Positivity
   of the exponential gives `c > 0`; `|E(a)| >= 0` gives `c <= 1`.
   The actual analytic covariance-to-spectral theorem selects its one
   positive constant before the dimension and body. For each
   unit-volume origin-symmetric body already in maximal Gaussian
   position, the geometric hypothesis supplies an ellipsoid; the
   previous new theorem proves `c <= alpha <= 1` and the exact actual raw
   covariance for that same body. The analytic theorem therefore
   supplies `UniformSymmetricGaussianDirichletBound C`. No covariance or
   spectral conclusion is retained as an external input to this theorem.

4. `affine_reverse_faber_krahn_of_ellipsoid_intersections` extracts only
   the universal geometric constant and its property, derives the
   uniform symmetric spectral bound, and applies the separately proved
   affine reduction. The conclusion has one positive constant before
   all `n > 0` and all compact convex bodies with nonempty interior,
   followed by an actual `Matrix.SpecialLinearGroup` map. It includes
   finiteness of the genuine `H¹₀` Rayleigh eigenvalue on `interior(SK)`
   and the original real inequality
   `lambda(Int(SK)).toReal * volume(K).toReal^(2/n) <= C*n`.
   The underlying unrestricted reduction contributes exactly its factor
   four. No symmetry, centering, boundary smoothness, covariance or
   eigenfunction hypothesis is imposed on the unrestricted final body.

The selected final theorem is conditional only on the stated uniform
geometric existence property. This does not prove that property, does
not establish unconditional M01, and does not imply that all original
manuscript intermediate statements have been formalized. In particular,
unproved original intermediate displays are not removed or silently
identified with a different result by this review.

## Exact evidence

The frozen final source has SHA256
`b54ba15c858352a971f3ec44a757bb0d7476aaa01c933146bd1e7267d03eadd3`.
The manifest `audit/gaussian_ellipsoid_reduction_source_manifest.json`
has SHA256
`649f7dfbb7b52b1a81bd4500d40b4ac79593943774711476a2ff21cac5a1b738`.
All 737 current source/probe hashes in that manifest were checked.

The actual final source command was

```text
/home/mjc249/.elan/toolchains/leanprover--lean4---v4.35.0-rc3/bin/lake build AffineFK.GaussianEllipsoidSpectralReduction
```

It exited `0` in `10.036` seconds, with the exact final source hash in
`logs/branch_bochner/gaussian-ellipsoid-spectral-reduction-build-02.txt`.
The actual axiom command was

```text
/home/mjc249/.elan/toolchains/leanprover--lean4---v4.35.0-rc3/bin/lake env lean audit/probes/GaussianEllipsoidSpectralReductionAxioms.lean
```

It exited `0` in `6.607` seconds. All four actual reports are subsets of
`{propext, Classical.choice, Quot.sound}`. The exact probe and manifest
hashes appear in
`logs/branch_bochner/gaussian-ellipsoid-reduction-axioms-01.txt`.

The initial failed build is preserved. Its three repairs add the actual
conditional-probability instance derived from already proved positive
mass, simplify the diagonal raw-moment identity, and remove a no-op
`dsimp`. The independent audit compared all four complete declaration
headers with the preserved initial candidate and found no statement
change. The rejected candidate's hash matches the actual failed
`01` log. All three raw logs in
`audit/gaussian-ellipsoid-reduction-evidence-01.tar.gz` were byte-compared
with their local copies.

The read-only check
`python audit/review_gaussian_ellipsoid_reduction.py` completed
successfully. Its JSON receipt is
`audit/gaussian_ellipsoid_reduction_independent_review.json`, SHA256
`1da9684118264b2d3348c3bcdeeb3456606545805dc1795be2bdd2c3a548d48d`.
The check validates saved bytes and actual Lean output and is not a
kernel oracle. No proof source, frozen packet, configuration or metadata
was edited by this review.
