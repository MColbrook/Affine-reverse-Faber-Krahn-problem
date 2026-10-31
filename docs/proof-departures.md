# The manuscript argument and the formal proof

The formal proof certifies the original M01/M02/M03 conclusions. It retains
the central new combination in the manuscript:

1. Centered second-order Stein identities give information decay for
   normalized sums.
2. The equal-input information-jump estimate and HSI argument give entropy
   decay and a superquadratic Gaussian-dilation profile.
3. An actual independent Gaussian dyadic-bridge coefficient event converts
   that profile into a spectral bound.
4. A weighted groundstate law, convolution and whitening supply the controlled
   isotropic law. The information-to-spectrum estimate and scalar absorption
   close the Gaussian-position bound; symmetric intersection and literal
   affine reduction give the general-body theorem.

These are genuine proof dependencies, not assumptions or an imported theorem
that directly supplies the desired principal conclusion. For profile power
`p > 2`, the choice `1/p < a < 1/2` makes both the coefficient-cost and uniform
radius series converge. These critical dyadic steps are formalized.

The proof makes the following documented departures.

## Stronger proved geometric input

The manuscript invokes Milman's ellipsoid-intersection consequence. The Lean
proof derives the required intersection statement using the complete sharp
symmetric volume-product theorem, `|K| |K°| ≥ 4^n/n!`, from the attributed
OpenAI development at commit `7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a`.
The exact polar/Haar transport, log-Laplace Jacobian and covariance-ellipsoid
normalization are proved locally. This establishes the needed universal
volume-one ellipsoid intersection, not every covering assertion of the full
Milman theorem. The stronger input is a genuine proof dependency, not an axiom
or a new theorem attributed to this manuscript.

## Terminal variational argument

The manuscript identifies a killed transition density with the Dirichlet
heat kernel and uses its diagonal spectral expansion. The formal proof
instead constructs an actual nonzero `H₀¹` killed-density-row competitor by
free-heat approximation, logarithmic-grid energy estimates and compactness.
It reaches the same actual Rayleigh infimum directly.

At the corresponding intermediate step, the formal estimate is
`8 B + 4 n log 2`, compared with the manuscript's `4 B + 2 n log 2`.
Both yield the stated conclusion with an unspecified constant depending only
on the profile power. The alternative proof does not certify the sharper
intermediate display by that route.

The original terminal calculation received a separate mathematical AI audit,
conditional on the standard killed-kernel and spectral inputs. The
`Δ/2` exponents, the two convergent series, free-kernel factor `2^(n/2)` and
final dilation direction were consistent. No error was found in that
calculation. This documentary audit is distinct from a Lean proof of those
classical inputs.

## Groundstate construction

The formal proof constructs one normalized, even, nonnegative log-concave
weak first minimizer by Gaussian killing powers, form approximation,
compactness and representative limits. It supplies the density and weak
energy identities required by the principal argument.

The manuscript also invokes strict positivity, simplicity and classical
groundstate log-concavity. Those stronger general assertions are not separate
theorems in this package. A later primary proof confirms the standard
Brascamp–Lieb attribution: P. Bryan, J. Clutterbuck and C. Rankin,
[arXiv:2605.01334v1](https://arxiv.org/abs/2605.01334v1), Theorem 1.3.
The reference audit explicitly records that the full original 1976 article
was not directly accessible; it does not claim an unseen theorem was checked.

## Specialized intermediate statements

The first Stein construction follows the coordinate Poisson and testing
argument. A later tensor existence construction takes an odd part, preserving
the test identity and reducing `L²` energy. It therefore avoids relying on
parity of a particular chosen Poisson representative.

Selected finite-Sobolev OU/HSI endpoints and the identical-copy information
jump suffice for the main application. They are proved on their actual
domains. They do not assert every-time classical dissipation, generic weak
Fisher lower semicontinuity or the full unequal-input information-jump theorem.
The general-integer Stein-sum identity is proved separately. The manuscript's
entropy-rate proposition and the qualification following its introductory
display explicitly concern dyadic indices; no all-integer entropy-rate
theorem is inferred from that argument.

The complete comparative audit is retained in
`verification/reviews/prior/principal_proof_departure_review.md`. Its author
contributed some reused proofs, so that comparative report is not represented
as an independent correctness endorsement of the author's own proof bodies.
Separate non-author source reviews and the actual kernel checks supply those
distinct checking layers.
