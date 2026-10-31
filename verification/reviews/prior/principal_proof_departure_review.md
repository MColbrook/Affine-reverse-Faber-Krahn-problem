# Principal conclusions and the manuscript's arguments

This is an **AI comparative argument-fidelity audit** by
`/root/formalization_coverage`, at the user's revised principal-results scope.
The manuscript reviewed has SHA-256
`1d30574bf6a09012c0492449d6860884c993b191837c9c0d2a9bd17080a3d0bc`.
I read the original principal arguments and the actual formal proof routes
identified below. I also checked their presence in the compiled recursive
proof/type-constant closures, rather than inferring use from imports alone.
The read-only audit script returns `PASS` for 16 concrete dependency paths
and pins 32 source/evidence files in the companion JSON.

I authored some reused formal analytic, geometric and Stein proofs and the
Stage36 presentation. This comparison does not replace the separate
non-author correctness reviews of those sources. In particular, it is not a
fresh independent proof certification of my own contributions. It makes no
human-review or historical-priority claim.

## Main finding

**The central information-theoretic/Brownian-bridge strategy has not been
bypassed.** The formal proof actually constructs the centred second-order
Stein tensor, obtains its normalized-sum decay, combines this with the
equal-input information jump and HSI inequality, derives the Gaussian
dilation exponent strictly greater than two, and uses the genuine independent
dyadic Gaussian bridge coefficients. Both convergent series—the probability
cost and uniform path-radius bound—remain essential. The Gaussian-weighted
groundstate, convolution, covariance whitening and final absorption also
remain in the main proof.

There are substantial **background and terminal-step proof departures**.
Consequently the accurate claim is that the stated principal conclusions
are verified by the formal proof development, with the checking status below;
it is not accurate to say that every manuscript argument or background
assertion has been verified line by line.

| Principal result | Correspondence with the original argument |
| --- | --- |
| M01/M02: affine and maximal-Gaussian-position spectral bounds | The symmetric-body spectral estimate, actual whitening construction, linear Rayleigh comparison, scalar absorption, symmetric-intersection averaging and volume normalization follow the paper's strategy. A different construction supplies the required nonnegative even log-concave groundstate. The universal geometric input is derived through a stronger attributed volume-product theorem. |
| M03: information to spectrum | The full original measure domain is retained. Finite information supplies absolute continuity; normalized small-ball masses and differentiation construct a same-law pointwise log-concave density. The information/entropy/dilation/bridge chain is used. Its final connection to the H0 Rayleigh infimum uses a direct variational argument instead of the paper's spectral expansion. |
| G01: universal Gaussian covariance position | Actual special-linear maximization, first variation, zero means and scalar covariance follow the paper. Literal shears and trace-free diagonal exponentials replace a general matrix-exponential variation without weakening the conclusion. A Gaussian dilation/Jensen calculation proves the needed entropy/covariance inequality directly. The Milman intersection prerequisite is supplied by an alternative stronger theorem, described below. |
| W13: unnormalized Rayleigh pullback | The formal theorem constructs the literal `f ∘ A`, proves its H0 membership and actual adjoint weak gradient, and cancels the same determinant factor from numerator and denominator. This is the manuscript's argument, extended to all open sets and dimensions where the formal statement is meaningful. No normalized surrogate is substituted in the final assertion. |
| S07: first-order Stein matrix | The actual coordinate Poisson problems, testing with coordinates, mean matrix `Id`, exact Hilbert–Schmidt discrepancy and finite-component vector identity follow the paper. The matrix is chosen before every compact smooth vector test and both integrands are genuinely integrable. The broader completion-graph theorem does not add an analytic premise to the original smooth positive-density domain. |

## Departures that should be disclosed

**Geometric input.** The paper invokes the classical consequence of Milman's
M-ellipsoid theorem that a volume-one symmetric body has a volume-one
ellipsoid with intersection at least an absolute base to the dimension.
The formal development does not formalize Milman's complete covering theorem.
It reuses the complete attributed symmetric Mahler proof from the pinned
OpenAI source development, giving the stronger actual product bound
`|K| |K°| ≥ 4^n/n!`. Genuine polar/Haar transport, exponential tilts,
injectivity of the mean map, the area formula and covariance ellipsoids then
derive the exact intersection consequence required here. This is a different
background proof, not a new assumption on the final theorem. Its provenance,
license, source port, independent reviews and own checking remain separate
from the paper's original Milman attribution. The publication should not say
that this development formally proves the full M-ellipsoid covering theorem,
nor present the stronger reused result as an original contribution of this
paper.

**Terminal bridge-to-spectrum step.** The paper identifies a killed Brownian
kernel with the Dirichlet heat kernel and uses its diagonal spectral
expansion. The formal route retains the actual killed bridge law and kernel,
but establishes an H1 bound for a killed density row by free-heat
approximation, finite logarithmic-grid estimates and Hilbert-graph compactness.
Its zero exterior value gives genuine H0 membership on the bounded convex
domain; its positive squared norm makes it a nonzero Rayleigh competitor.
Thus it reaches the actual variational eigenvalue without assuming a killed
generator identification or a spectral expansion. The derived intermediate
bound is `8B + 4n log 2`, whereas the manuscript's spectral argument gives
`4B + 2n log 2`. Both give the stated unspecified `C(p)(A+n)`. The sharper
intermediate display and the full spectral-expansion identification should
not be described as kernel-verified by this alternative proof.

**Groundstate prerequisites.** The paper starts with a positive simple first
eigenfunction and cites classical groundstate log-concavity. The formal main
proof constructs one actual normalized, even, nonnegative log-concave weak
first eigenfunction through finite Gaussian killing powers, nonlocal-form
approximation, compactness and representative limits. That is enough for
the weighted-density and whitening argument. It does not prove that every
first eigenfunction has the paper's strict positivity, uniqueness and
classical regularity properties. The unfinished positivity/PDE background
sources are unnecessary for the principal theorem and should remain clearly
outside its verified scope.

**Parity and nonsmooth passages.** The main tensor-existence path takes the
odd part of a constructed tensor. Reflection of compact tests preserves its
identity and does not increase its L2 energy. This avoids relying on parity
of the original Poisson representatives in that path; those original
solution-parity assertions were separately proved in the earlier parity
checkpoint. Similarly, the finite-Sobolev HSI and actual OU endpoint lemmas
allow the nonsmooth application without a general weak lower-semicontinuity
theorem as an additional assumption. The specific endpoints and equal-law
information jump needed here are established. This does not certify every
generic weak-LSC, unequal-input or every-time classical dissipation statement
that one might use in a broader theory.

## Check of the original bypassed bridge argument

I checked the manuscript's argument mathematically, independently of the
alternative formal proof. No defect was found, **conditional on the cited
standard killed-kernel and Dirichlet spectral theory**:

1. For `p>2`, the interval `1/p<a<1/2` is nonempty. The independent coefficient
   event has probability at least `exp(-A/(1-2^(1-ap)))`; finite products and
   continuity from above justify the infinite event and its positive mass.
2. At each level only one tent is nonzero. The coefficient bound therefore
   gives radius `R=1/(2(1-2^(a-1/2)))` and uniform convergence. Almost-sure
   agreement with the continuous bridge suffices for the survival probability.
   Since `0∈Int D`, compact `RD` lies strictly inside `2R Int D`.
3. For Brownian generator `Δ/2`, eigenvalues of `-Δ` appear as
   `exp(-λ_l t/2)`. The estimate
   `exp(-λ_l/2) ≤ exp(-λ_1/4) exp(-λ_l/4)` has the correct direction and factor.
   The free diagonal ratio is `2^(n/2)`, giving
   `λ_1(Ω) ≤ 4 log(1/q)+2n log 2`.
4. The dilation identity is `λ_1(D)=(2R)^2 λ_1(2R Int D)`, with the required
   direction. All resulting constants depend only on `p`.

The bounded convex domain is connected and has the boundary regularity
needed by the conventional Dirichlet theory; the evaluated point is strictly
interior. The manuscript also explicitly needs positive-time diagonal
convergence and free-kernel domination. These are standard analytic inputs,
not consequences of the elementary series algebra alone. This paragraph is
an AI mathematical audit, not a Lean proof of those inputs. The formal
variational route is the checked replacement.

## Consequence for the novelty and verification account

The potentially novel combination to emphasize is the superquadratic
Gaussian dilation profile obtained from second-order centering plus the
information jump, its conversion to bridge survival using the two geometric
series, and the Gaussian-weighted-groundstate whitening closure of the
spectral inequality. The actual formal proof uses these steps. The
comparison therefore found no bypass of that central combination by an
unrelated theorem that directly supplies the final spectral bound.

This is an argument-fidelity assessment, not a literature-priority search;
the separate primary-reference audit should decide attribution and priority
wording. No further background formalization is recommended under the new
scope. If a future account claims literal verification of the manuscript's
spectral display, it would need the killed-generator/spectral bridge itself;
that would strengthen the account, not repair a missing premise of the
already established principal conclusions.

At this audit cut, M01/M02 have their own actual ordinary sandboxed six-kernel
acceptance. M03/G01/W13/S07 have completed source checks and exact compiled
statement/proof diagnostics, while their own Stage36 six-kernel run is
parent-controlled and pending. This document does not infer its success.
The full manuscript remains unverified. The already completed new native
logarithmic-gradient port is preserved as source-level work; its additional
all-name axiom batch was planned but never launched after the scope change.
