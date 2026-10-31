# Independent AI mathematical review: the geometric input and affine main theorem

Reviewer: `/root/formalization_coverage`. New proof author: `/root`.
I read the complete headers and bodies of all four theorems in
`AffineFK/GaussianPositionMilman.lean`, SHA-256
`b990cd79d2de0dd6c045fd7189ff048846d9cc1561fab557fa1e0b45655e3958`.
I found no mathematical, statement-fidelity, constant, domain or clarity defect.
This report initially records the mathematical reading; the author's final
source-pinned build and axiom evidence will be recorded separately when fetched.

## Four statements and proofs

1. `gaussianPosition_mahler_volume_product` has exactly the positive-dimensional
   compact, convex, nonempty-interior, origin-symmetry hypotheses required by the
   genuine Mahler theorem. The proof constructs the coordinate body through the
   actual `PiLp` equivalence, applies `OAI.SymmetricMahler.symmetric_mahler`, and
   transports the exact Haar-volume product back to Euclidean space. The
   one-sided coordinate polar and absolute Euclidean polar agree because the
   actual symmetry hypothesis is supplied. There is no norm or volume
   normalization factor omitted.
2. `gaussianPosition_dilated_polar_uniform_volume_lower` additionally assumes
   `volume K = 1` and derives `4 ^ n ≤ volume.real (n • polar K)` from that
   product. The reused arithmetic proof has the positive factorial denominator,
   the genuine `n! ≤ n^n` inequality, nonnegative real volume and exact Haar
   dilation. No numerical approximation is required.
3. `gaussianPosition_uniform_volume_one_ellipsoid_intersection` chooses the
   explicit positive constant `covarianceEllipsoidTiltIntersectionBase 4`
   **before** every dimension and body. The measurable finite-volume domain is
   the actual dilated polar, and its just-proved volume lower bound supplies the
   small-Jacobian selection theorem with `b = 4`. This is an actual selected
   point of that domain, not an assumed determinant conclusion. The inequality
   `det ≤ |det|` has the correct direction. The previously constructed tilted
   covariance ellipsoid and its actual normalization then give an invertible
   linear image of a positive-radius Euclidean ball, literal volume one and the
   dimension-exponential intersection lower bound. The radius is
   `sqrt (2 * n) > 0` under the original `0 < n` hypothesis. Its covariance,
   positive definiteness, density bounds, central-intersection comparison and
   normalization are supplied by genuine earlier source theorems. There is no
   supplied Milman, desired mass, covariance or ellipsoid-existence hypothesis.
4. `affine_reverse_faber_krahn` supplies this unconditional geometric theorem to
   the previously proved analytic and affine reduction. Its final type is
   `∃ C > 0, ∀ n > 0, ∀ K`, followed only by compactness, convexity and nonempty
   interior. It produces an actual `Matrix.SpecialLinearGroup` element and
   asserts finiteness of the actual H0 Rayleigh-infimum eigenvalue before using
   its real value. The conclusion is precisely
   `lambda_1(interior(S K)) * volume(K)^(2/n) ≤ C*n`.

I checked the exact called interfaces in the coordinate/polar transport,
small-Jacobian, tilted ellipsoid, geometric-to-covariance and unrestricted
affine-reduction modules. The final reduction supplies the actual large
symmetric subbody, translations, volume normalization, special-linear action and
factor four. The eigenvalue is the genuine infimum over nonzero H0 values, and
the exponent and all occurrences of `n` match the manuscript's main theorem.
No positivity, log-concavity, covariance, spectral, ground-state, Fisher or
ellipsoid hypothesis remains in the final main-theorem statement.

## Attribution and review boundary

The new assembly explicitly attributes the reused sharp symmetric Mahler proof
to the OpenAI math development at immutable commit
`7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a`. Its original Apache-2.0 source and
proof attribution remain bundled. The exact source target is
`OAI.SymmetricMahler.symmetric_mahler`, with ordinary coordinate Lebesgue volume
and its complete coordinate polar. The root's separate independent raw-Git-blob
and source-body review, and the actual pinned Lean build and axiom checks, remain
separate evidence for that reused proof.

I authored the header-only import/module port of those upstream sources, but no
original upstream mathematical proof body and none of the four new assembly
proofs. My new independent mathematical-review claim concerns these four
root-authored proofs and the fidelity of their applications. It does not claim
that I independently reread every proof in the 229-module Mahler development.
Some reused tilt and normalization lemmas are also my work; the root's separate
non-author reviews cover those. The coordinate/polar lemmas have my separate
non-author review. This explicitly preserves both author and reviewer boundaries.

## Checking status at the initial review

The source contains complete ordinary proofs, canonical imports and no custom
axiom, placeholder or native-execution trust. The local source file and called
definitions were read, but the reported successful remote build log was not yet
present locally at the time of this initial report. I have therefore not
inferred a source-pinned axiom result or six-kernel acceptance for these four
from the author's message. The independent evidence closure will use the actual
fetched logs and final handoff.

The own Stage34 Mahler Comparator run is also a separate pending check at this
point. This AI source review is not a human review, its own Comparator
certificate, or a claim that every statement in the manuscript has been
formalized. The main result's statement and complete new assembly are sound on
the genuine source interfaces reviewed here.
