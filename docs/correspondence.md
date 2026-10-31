# Correspondence between the manuscript and Lean

The reference is the frozen [manuscript](../source/manuscript.tex), SHA-256
`1d30574bf6a09012c0492449d6860884c993b191837c9c0d2a9bd17080a3d0bc`.
The source statements have not been weakened. The new combined declaration
has type `(M01 ∧ M02) ∧ M03`; it introduces no new mathematical premise.

| Claim and manuscript location | Exact domain, hypotheses and quantifiers | Formal conclusion and proof endpoint |
| --- | --- | --- |
| M01, lines 124–130 | There exists one real `C > 0`, before every natural `n > 0` and every compact convex `K ⊆ ℝⁿ` with nonempty interior. Neither symmetry nor centering nor smooth boundary is assumed. | There exists an actual `S : Matrix.SpecialLinearGroup (Fin n) ℝ`. The Dirichlet infimum on `interior (S K)` is finite and its real value times `volume(K)^(2/n)` is at most `C n`. First conjunct of `AffineFKProof.affine_reverse_faber_krahn_main_theorems`, in `AffineFK/MainTheorems.lean`; underlying geometric conclusion in `GaussianPositionMilman.lean`. |
| M02, lines 155–162 | There exists one real `C > 0`, before every `n > 0` and every compact convex origin-symmetric body with nonempty interior and volume one. Maximal Gaussian position means comparison with every literal special-linear image under the standard Gaussian. | The actual Dirichlet infimum on `interior K` is at most `C n`. This is the second conjunct of that same endpoint. No covariance lower bound, ellipsoid-existence or groundstate assertion is a premise. The constants for M01 and M02 may differ, as in the paper. |
| M03, lines 178–191 | For every real `P ≥ 2`, there exists one positive finite real `C(P)` before dimension, law and body. The law is a probability, invariant under negation, log-concave in the conventional compact-set formulation, with zero coordinate means and raw covariance `δᵢⱼ`, least Poincaré constant at most `P` and finite actual Gaussian-relative Fisher information. It is supported almost everywhere on the original compact convex origin-symmetric body `D` with nonempty interior. | The actual Dirichlet infimum on `interior D` is at most `C(P)(n + √(n I(ν∣γ)))`. The endpoint is `AffineFKProof.information_spectrum_logConcaveMeasure_uniform_constant`, in `AffineFK/InformationSpectrumLogConcaveMeasure.lean`. A log-concave density for the same law is derived; a density witness is not an additional assumption. |

## Dirichlet and boundary conventions

`unweightedSobolevGraph` is the closed value–gradient graph of compact smooth
tests on Euclidean space. `dirichletSobolev n U` is the closure of the tests
supported in the open set `U`, viewed by zero extension in that graph.
`dirichletValue` and `dirichletGradient` are its actual continuous projections.
The value map is injective. `dirichletEigenvalue` is the extended-nonnegative
infimum of the actual Rayleigh quotient over all nonzero values, with the
positive denominator justified by the proof development. Finiteness is
established before a real conversion is used.

This is the variational `H₀¹` definition in the manuscript. On compact tests,
the global zero-extension value–gradient norm equals the norm on the open
domain; completion gives the usual form-domain model. The standard
Friedrichs Dirichlet interpretation requires no smooth-boundary assumption.
See van den Berg, Hempel and Voigt, *J. Spectr. Theory* **5** (2015),
829–857, introduction and §1, [doi:10.4171/JST/115](https://doi.org/10.4171/JST/115).
The unbounded operator and full classical heat-kernel/spectral identification
are not separately exported theorems here. The final eigenvalue is for
`−Δ`; Brownian `Δ/2` time conventions are confined to the proof constants.

## Probability, Poincaré and information conventions

The covariance assumptions are actual Lebesgue integrals. A diagonal second
moment equal to one forces integrability and hence genuine coordinate
`L²` membership; a nonintegrable Bochner integral defaulting to zero cannot
satisfy that equation. Means and mixed products then have the needed `L¹`
guards. No undefined moment is silently treated as a valid isotropic moment.

`poincareConstant` is the least admissible constant for the true
variance–gradient inequality on compact smooth tests. Its extension to the
smooth `L²` and compact-test Sobolev completions used in the argument is
proved. These domains give the meaningful-integral interpretation of the
manuscript's convention.

`relativeFisherMeasure` is infinite unless the law is absolutely continuous.
For its actual Radon–Nikodym density `ρ`, the relative functional is infinite
off the square-root Sobolev and finite-second-moment domain. On that domain
it is the integral of `|2 ∇√ρ + x √ρ|²`. The ordinary energy is
`4 ∫ |∇√ρ|²`. Representatives, actual integrability and the finite isotropic
identity `I = J − n` are proved where used. Infinite information is never
converted into a spurious zero real energy.

The law-level log-concavity input is the compact-set inequality in
`IsLogConcaveMeasure`. Under the original finite-information hypothesis the
proof constructs a finite pointwise log-concave density representing the
same law. The general affine-support characterization of every possibly
singular log-concave law is unnecessary and is not claimed.

## Review boundary

The independent AI correspondence review and its separate documentary
cross-review are retained in
`verification/reviews/prior/principal_manuscript_lean_correspondence_review.md`
and `principal_correspondence_calibration_review.md`. They examined actual
definitions, hypotheses, domains, constants, quantifier order and conclusions.
Those historical documents also discuss G01/W13/S07; the present selected
benchmark contains only M01/M02/M03. Their original development-relative
references are historical, with an origin map beside them.

The new combined canonical interface has a separate non-author AI review
and actual compiled-data/private-proof inspection under `verification/`.
AI source-authorship boundaries are explicit; no human peer review is claimed.
The audit found no material mismatch or necessary mathematical correction to
these three theorem statements. Clarifying the Poincaré function domain and
the finite moment/Fisher hypotheses before the identity `I = J − n` would
improve the paper's exposition without changing its theorems.
