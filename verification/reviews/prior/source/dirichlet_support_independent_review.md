# Independent AI review of six Dirichlet support results

Reviewer: `/root/palomar_requirements`. I authored none of the six results in
`DirichletSupportCompact.lean` and `DirichletSupportDilation.lean`. I read each
complete declaration header and proof body. This is an AI review, not a human
endorsement or a Comparator certificate. Some older transitive sources have
separate authorship and independent reviews; this report does not claim a new
independent mathematical review of every transitive dependency.

No mathematical or statement-fidelity defect was found. The compact-support
theorem uses the actual completed global H1 graph and actual H0 closed core.
Mathlib's smooth separation construction supplies a compact smooth cutoff that
equals one on the given compact set and has a genuine uniform gradient bound.
The bounded H1 multiplier maps every compact smooth approximating core element
into the domain's core. Closure gives H0 membership of the product. The value
map is genuinely injective, so equality of the cutoff product and original value
identifies the original H1 element itself. No trace theorem is assumed.

The convexity lemma uses a closed point and an interior point in a strict convex
combination. Its assumptions are exactly a convex open set containing zero,
`0 ≤ a < 1`; no unsupported boundary inclusion is used. For `0 < a < 1`, the
actual invertible normalized H1 transport preserves the stated value and
adjoint-gradient formulas and carries almost-everywhere support to the genuine
image of the old support. Boundedness makes the closure compact; convexity puts
its strict contraction inside the open set. The prior cutoff theorem then
proves membership in the actual H0 domain. All dimensions, including zero,
remain in the formal domains.

Evidence is pinned in `dirichlet_support_independent_review.json`. The independent
read-only command is `python audit/review_dirichlet_support.py`. It checks all 54
source hashes against `dirichlet_support_source_manifest.json`, all six exact
fresh axiom reports, and the actual successful compact build 02, dilation build
03, and six-declaration axiom run. Their recorded durations are 10.089, 15.614,
and 5.440 seconds. Only `propext`, `Classical.choice`, and `Quot.sound` occur.
Failed earlier builds remain in the author's raw evidence archive.

These six results do not by themselves prove the limiting H1-to-H0 converse,
identify the killed Brownian energy with the variational Dirichlet form, or
prove any headline manuscript theorem. No new small Comparator run is claimed.
