# Original M01 and G05: independent AI statement-fidelity review

Reviewer: `/root/claim_inventory`, who did not author the four new `GaussianPositionMilman.lean` proofs. This review compares their complete statements and short composition bodies with the frozen manuscript and original 141-item inventory. The separate primary non-author mathematics review is by `/root/formalization_coverage`; its final receipt is `gaussian_position_milman_independent_final_receipt.md/json`. Some earlier reused C proofs were authored by this reviewer; this statement review does not present their reuse as a fresh non-author mathematical review of those proofs.

The reviewed source SHA256 is `b990cd79d2de0dd6c045fd7189ff048846d9cc1561fab557fa1e0b45655e3958`. The actual root source manifest is `d7792769ac62f432029529a687ec9a65df67a1d951b92a35574ba1820a256d9b`. Both complete source statements and the actual meanings of `UniformVolumeOneEllipsoidIntersection`, the special-linear action and the variational eigenvalue were read. No statement-fidelity defect was found.

## M01: exact original main statement

Original M01 is manuscript lines 124–130. The public `AffineFKProof.affine_reverse_faber_krahn` has the exact intended quantifier order:

`∃ C : ℝ, 0<C ∧ ∀ n>0, ∀ K, convex-body hypotheses → ∃ S∈SLₙ(ℝ), ...`.

There is **one finite positive real constant before every dimension and every body**. Only compactness, real convexity and nonempty actual interior are assumptions on the original body. There is no original-body symmetry, centering, unit-volume, smooth-boundary, supplied eigenfunction, log-concavity, covariance, Fisher information, Poincaré, positioning, geometric-output or desired spectral-bound premise. The final theorem has no remaining conditional geometry argument.

The output `S : Matrix.SpecialLinearGroup (Fin n) ℝ` is a literal determinant-one matrix. `gaussianPositionSLLinear` is its actual continuous linear equivalence through the standard Euclidean basis; its actual determinant is proved equal to one and its actual Lebesgue-volume preservation is already established. No unconstrained affine-map placeholder or additional translation replaces this `S`.

The conclusion is exactly

`λ₁(interior(S K)).toReal * volume(K).toReal^(2/n) ≤ C*n`,

together with an explicit proof that this actual extended eigenvalue is not infinity. The eigenvalue is the existing infimum of genuine nonzero-value Rayleigh quotients in the completed compact-test `H₀¹` space; its numerator is the actual squared gradient `L²` norm, without a Brownian-generator factor of one half. The value map is injective, so the nonzero-value condition is the intended nonzero function condition. Compactness/nonempty interior make the volume finite and positive; positive dimension makes the real exponent meaningful. Consequently neither `ENNReal.toReal ∞=0` nor a zero-volume convention weakens the displayed source result. Source M01's exact bound and all its intended quantifiers/domains are preserved.

## G05: the original ellipsoid-intersection consequence

Original G05 is manuscript lines 342–348, the universal volume-one origin-ellipsoid intersection input, not merely a later Gaussian-mass estimate. `gaussianPosition_uniform_volume_one_ellipsoid_intersection` proves

`∃ a>0, UniformVolumeOneEllipsoidIntersection a`.

The complete definition of that predicate is literal: the **same `a` is chosen before every `n>0` and every origin-symmetric volume-one compact convex body with nonempty interior**. It returns an actual continuous linear equivalence `A` and radius `R>0` with

`volume(A '' closedBall(0,R)) = 1`

and

`a^n ≤ volume(K ∩ (A '' closedBall(0,R))).toReal`.

Thus the returned ellipsoid is genuinely full-dimensional and origin-centered, with actual volume one and the original intersection-volume conclusion. There is no supplied ellipsoid, intersection bound, small-determinant point, reverse-volume-product estimate, covariance or main theorem in its hypotheses. The translated covariance ellipsoid is constructed upstream and its translation is removed by the proved central-intersection inequality. The fixed displayed radius `sqrt(2*n)` is positive in the required domain and imposes no restriction on the represented ellipsoid, since `A` is an arbitrary invertible linear equivalence.

The explicit base is `covarianceEllipsoidTiltIntersectionBase 4 = (1/(2*exp 1))/max(sqrt(4⁻¹)*covarianceEllipsoidBallVolumeBase,1)`. It depends on no dimension/body. Its positivity is proved and the denominator is at least one; its value is in particular below one, compatible with the inventory's optional normalization `a≤1`. The public source theorem returns the original manuscript's positive-base statement; it does not separately advertise an additional formal `a≤1` conjunct. This exact G05 consequence is not a claim to formalize every covering-number property of the full classical M-ellipsoid theorem.

## Composition, attribution and checking boundary

All four short proof bodies were read. The first transports the literal checked coordinate Mahler statement to the Euclidean inner polar through the actual body/volume bridge. The second applies the proved factorial/Haar arithmetic to obtain `volume.real(n K°)≥4^n`. The third derives finite measurable positive-volume polar-domain hypotheses, selects a genuine small-Jacobian point by the actual area argument, bounds the signed determinant by its absolute value and constructs/normalizes the actual origin ellipsoid. The fourth invokes the proved ellipsoid-to-Gaussian-position-to-analytic-to-affine reduction with this **derived** universal input. No desired output is inserted as a hypothesis along this composition.

The geometric proof uses the stronger pinned `openai/math` Mahler development at commit `7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a`, with retained original Apache-2.0 sources and actual port provenance. This is an alternative formal proof of the original G05 consequence; it does not claim that the proof is the same argument as the manuscript's Milman/Bobkov citation. The independent canonical target/data pre-review and actual coordinate/Haar bridge preserve the one-sided-versus-absolute polar and normalization details. No unproved volume-product theorem remains a parameter of these final source statements.

The actual source build `gaussian-position-milman-main-build-01.txt` records the matching final source hash, full Lake command, `EXIT_CODE: 0` and **7.995 seconds**. The fresh standalone `gaussian-position-milman-axioms-01.txt` records the matching probe/manifest hashes, four actual `#print axioms` reports using only `propext`, `Classical.choice`, `Quot.sound`, `EXIT_CODE: 0` and **7.009 seconds**. Both raw logs and the byte-identical two-log archive were inspected. All **989 source/probe byte pins** were checked; this hash audit is not a claim to have manually reread every one of those sources. No compiler, kernel or Comparator was rerun in this review.

At this review time the upstream Stage34 all-six gate and the separate final Main35 canonical Challenge/aggregate/gate are **not claimed accepted**. These are unconditional source theorem statements with an actual ordinary Lean build/axiom audit, while the final requested independent certification remains a separate evidence layer. M02 will receive its separate aggregate/Challenge review. The full manuscript, strict positivity/simplicity/all-groundstate claims, unrelated proof steps and all 141 entries are not silently promoted because M01/G05 now have source proofs. The frozen manuscript and inventory remain unchanged. No proof, definition, config, upstream original or metadata was edited during this review.
