# Independent AI review: root's law-level bounds and scalar L2 dilation

Reviewer: `/root/formalization_coverage`. Author of the twelve new
declarations in `DirichletSupportL2Dilation` and
`GroundstateGaussianLawBounds`: `/root`. I read every complete type,
definition and proof body. No mathematical, statement-fidelity,
normalization, integrability, domain or trust defect was found.

This is independent **AI source review**, not human review, a fresh Lean
run by the reviewer, a Comparator verdict or full-paper verification.
Previously frozen unweighted-H1 foundations authored by the reviewer are
not independently self-reviewed here. The reused ordinary-Fisher
Jacobian/Lp/H1/adjoint energy transport was authored by sibling C and keeps
its earlier separate root review. All twelve new root declarations are
outside the reviewer's authorship.

The read-only audit `review_law_dilation_sources.py` passed, checking all
**361 source/probe pins**, **four actual raw logs**, and **twelve fresh
axiom reports**, each a subset of `propext`, `Classical.choice`,
`Quot.sound`. The exact JSON receipt is
`law_dilation_independent_review.json`, SHA256
`9c5d16ebbe4e940540f0ad61648251be8d8df1e26c21fd82480682f1ee99eb92`.
No Lean source was changed by the reviewer.

The nine dilation declarations use the actual continuous-linear scalar
equivalence for nonzero a. Its inverse is exactly multiplication by a^-1.
For positive a the genuine inverse determinant/Jacobian is a^-n, including
dimension zero. `supportDilationL2` is the actual sqrt-Jacobian times the
proved Lebesgue L2 pullback; its AE formula is justified by the true Lp
representative equalities. The existing exact change-of-variables energy
theorem gives equality of squared L2 norms, and nonnegative norms then
give the true isometry. Difference isometry follows from actual
linearity. Neither continuity of the dilation family in a nor strong
convergence of arbitrary dilated L2 functions is asserted in this file.

The coefficient upper bound explicitly requires a>=1/2, deriving a>0
before inverting it. Its a^-n<=2^n estimate and square-root monotonicity
are genuine scalar inequalities. The coefficient-limit theorem assumes
every scale is positive and the scale sequence converges to one, then
uses true inverse, power and square-root continuity. No zero-scale
fallback or limiting coefficient conclusion is assumed.

The three law-level declarations correctly separate a selected arbitrary
Lp representative from a pointwise strongly log-concave density
representing the **same actual probability law**. The first transfers
the true Poincare inequality through that actual equality of measures;
the representing density is measurable, nonnegative and has the genuine
quadratic strong-log-concavity tilt. Probability is installed from the
given law before the supported strong-LC theorem is applied.

The ground-state bound takes an actual H0 element satisfying the genuine
weak eigen-equation, nonzero element, AE nonnegative value, reflection
invariance of its actual Gaussian-weighted density law, and a true
Poincare bound or a genuine strong-LC representative of that law. It
uses the earlier proved exact identity

```text
J(Y) = 4*ell + integral(norm(x)^2, law(Y)).
```

The earlier identity supplies probability, true second-moment
integrability and finite numerical ordinary Fisher information. These
are obtained **before** the real Fisher value is used. Reflection gives
zero means, and the actual Poincare smooth-coordinate extension then
gives the norm-square moment at most n. Therefore J(Y).toReal<=4*ell+n
and the genuine ENNReal bound follow. The last theorem supplies its
Poincare premise through the actual representative equality and returns
Poincare, moment, finite Fisher and real Fisher bounds for that original
law. It does not assert ground-state parity/log-concavity or a good-law
construction from the domain alone.

Actual source evidence: the first dilation build failed and is retained;
the corrected L2 dilation02 exited zero in **10.734s**. Law-bounds01
exited zero in **9.645s**. The separate fresh command

```text
/home/mjc249/.elan/toolchains/leanprover--lean4---v4.35.0-rc3/bin/lake env lean audit/probes/LawDilationAxioms.lean
EXIT_CODE: 0
ELAPSED_SECONDS: 5.762
```

emitted the twelve actual allowed-axiom reports. The source manifest
records the complete recursively imported nested bundle pins. This is
ordinary source compiler/axiom evidence; no new six-mode comparison is
inferred. Lean remains the pinned 4.35.0-rc3 toolchain, Mathlib
`b63f6e8a68d220e3b3bc4f3792bb53650d375f24`.

Primary reuse includes Mathlib's actual determinant/scalar equivalence,
Haar change of variables, continuous linear Lp operators, actual L2 norm
integrals, finite-power and square-root continuity, and the previously
attributed genuine supported strong-log-concavity/Poincare development.
The original author/licence attribution remains in those sources. There
are no new placeholders, custom axioms, unsafe/native proof mechanisms
or assumptions of the displayed Fisher or dilation conclusions.

Still outside these twelve declarations: strong L2 dilation continuity,
ground-state existence/positivity/parity/log-concavity, covariance
whitening, killed-kernel Rayleigh/spectral identification and the full
affine reverse Faber--Krahn theorem. The three later dilation-limit
declarations are explicitly outside this frozen review scope.
