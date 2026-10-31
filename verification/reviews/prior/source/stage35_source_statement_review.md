# Independent AI source review: both original main theorems

Reviewer: `/root/formalization_coverage`. Aggregate proof author:
`/root/palomar_requirements`; geometric/main composition author: `/root`.
I read both complete new statements and proof bodies in
`AffineFK/MainTheorems.lean`, SHA-256
`79e7f75588806e79d357b6792b569651ee024ce5318cecc6bbaab4f10faedf40`.
No mathematical, statement-fidelity, domain, quantifier, constant or clarity
defect was found. This is an independent non-author AI source review, not a
human review or this aggregate's own six-kernel certificate.

## Exact meaning and proof applications

`gaussian_reverse_faber_krahn` concludes
`∃ C : ℝ, 0 < C ∧ UniformSymmetricGaussianDirichletBound C`. I read the
complete fixed definition in `SymmetricAffineSpectralReduction.lean`: one
positive real constant precedes **all** positive integer dimensions and compact
convex origin-symmetric bodies with nonempty interior, volume one, and actual
maximal standard-Gaussian measure position. The conclusion bounds the actual
H0 Rayleigh-infimum eigenvalue by `ENNReal.ofReal (C*n)`. This finite upper bound
also gives eigenvalue finiteness. This is the full original M02 statement;
there is no input covariance, ground-state, Fisher, ellipsoid or spectral bound.

The proof obtains the already proved unconditional uniform volume-one
origin-ellipsoid intersection theorem, then applies the genuine
ellipsoid-to-symmetric-spectral reduction. A theorem previously conditional on
that geometric property is correctly used with its newly proved input. The
property is a derived conclusion here, not a new assumption on the body.

`affine_reverse_faber_krahn_main_theorems` is a conjunction. Its first component
is the complete inline original M01: one `C>0` precedes all `n>0` and all compact
convex bodies with nonempty interior. It produces an actual
`Matrix.SpecialLinearGroup (Fin n) ℝ` element, proves finiteness of the genuine
eigenvalue on `interior(S K)`, and proves

```text
lambda_1(interior(S K)).toReal * volume(K).toReal^(2/n) <= C*n.
```

There is no original-body symmetry, centering, unit-volume or boundary-smoothness
hypothesis. The second component is exactly M02 above. Each original theorem
has its own universal constant, as in the manuscript. The tuple proof applies
the two actual established theorems, without supplying any replacement output
hypothesis. My independent text comparison also checks that the complete inline
M01 type is identical to the root unconditional theorem modulo whitespace.

The eigenvalue is the infimum of actual squared-gradient/value-norm Rayleigh
quotients in the compact-test H0 completion. Its value map is injective, so the
nonzero-value condition is the nonzero-function condition. There is no
Brownian-generator factor of one half in this definition. The special-linear
action is the actual Euclidean linear equivalence of a determinant-one matrix.
Finiteness is established before M01 uses `toReal`; positive finite body volume
and the positive-dimensional exponent are preserved.

## Complete dependency route and review boundaries

I checked the actual used source interfaces and the separately closed review
chain, rather than treating the two short aggregate proofs as proofs of their
own imported prerequisites:

1. The attributed pinned Mahler development gives the actual coordinate
   volume-product bound. Exact symmetry/polar and `PiLp` Haar transport give the
   Euclidean product. Exact factorial and dilation arithmetic give
   `volume.real(n K°) >= 4^n`.
2. The genuine log-Laplace gradient has actual mean, derivative/covariance,
   injectivity and image in `K`. The genuine area formula selects a point of the
   actual polar domain with small determinant. Actual positive-definite
   covariance, ellipsoid mass and volume, central intersection and normalization
   yield one literal volume-one origin ellipsoid with a universal intersection
   base. No universal geometry is left as a premise in this final route.
3. Actual maximal-Gaussian-position existence and the same-body Gaussian
   mass/entropy/covariance calculations give a universal covariance lower bound.
   The analytic theorem constructs an actual even H0 first weak minimizer with
   a finite pointwise log-concave representative. Its weighted law, supported
   strong-log-concavity bound, independent convolution and covariance whitening
   give the actual Poincaré/information/support estimates. The explicit-density
   information-spectrum theorem applies to the constructed law. The genuine
   linear Rayleigh comparison and square-root absorption give M02.
4. Actual body-volume normalization and maximal positioning give the symmetric
   affine theorem. A genuinely constructed large symmetric subbody, translation,
   domain monotonicity and the exact factor four give unrestricted M01.

The new root geometric/main composition was separately read in full in
`gaussian_position_milman_independent_review.md` and closed against the actual
build/four-axiom evidence in
`gaussian_position_milman_independent_final_receipt.md/json`. Separate
non-author geometry, covariance-ellipsoid, whitening, ground-state and affine
reviews are pinned in the JSON accompanying this review. Existing accepted
Stage32/33 evidence is referenced for its actual scope; it is not represented
as acceptance of this new aggregate.

I authored neither new aggregate proof nor the root main composition. I did
author the upstream header-only port and some reused tilt/whitening work;
separate root/non-author reviews cover those boundaries. Original Mahler proof
bodies remain unchanged and attributed to the OpenAI math development at
commit `7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a`, with Apache-2.0 provenance
retained. I do not claim a new manual reading of all 990 imported source files.

## Actual source checking

The frozen source manifest is
`f06ec71052d535008f63d6c7fb78a9457ec5f615b0a5c6b8ed72b80aed22477d`.
The independent read-only audit `audit/review_stage35_main_source.py` passed
**990** recursive source/probe byte pins, their exact uploaded payload bytes,
the two actual logs and both fresh allowed-axiom reports. The 990 count is a
source-import manifest, **not** a newly computed private proof-dependency DAG.

| Actual command suffix, using the pinned rc3 Lake | Result | Raw log |
|---|---|---|
| `build AffineFK.MainTheorems` | exit 0; 7.751 s | `logs/branch_bridge/main-theorems-remote-01.txt` |
| `env lean AffineFK/MainTheoremsAxioms.lean` | exit 0; 6.839 s | `logs/branch_bridge/main-theorems-axioms-remote-01.txt` |

Both actual reports contain only `propext`, `Classical.choice` and `Quot.sound`.
The source has no placeholder, custom axiom or native-execution trust bridge.
Lean is `4.35.0-rc3`, commit
`470d5ce1400764999581fd26d5d72b00d990b0f4`, and Mathlib is
`b63f6e8a68d220e3b3bc4f3792bb53650d375f24`.
I ran no compiler or Comparator during this review.

The structured receipt is
`audit/stage35_source_statement_review.json`, SHA-256
`1da8665484a7e8a9ea3cf868df05e8de6ca856fa9cb0832e8b2549e645e3d92f`.
It pins the previous reviews and certificates, exact source/log hashes and the
independent type comparison. The final separately reviewed canonical packet,
compiled fixed-data comparison and its own ordinary sandboxed all-six gate
remain separate. Remaining manuscript-level obligations are listed in
`stage35_remaining_manuscript_obligations.md`; no whole-paper verification is
inferred from these two source theorems.
