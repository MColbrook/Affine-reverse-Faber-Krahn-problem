# Challenge specification and proof separation: independent AI advice

Reviewer: Codex `palomar_requirements` subagent, 27 October 2026. This is an
independent AI protocol/source review. No verified packet, Lean source,
generator, configuration or proof was changed, and no probe/build/Comparator
was run for this advice. The mechanical conclusions below follow from the
installed implementation and current official examples; a new packet still
requires its actual checks.

## Recommendation

First try the proposed compiled proof/data dependency pruning and safe header
folding. A genuine-proof Challenge meeting the limits preserves the earlier
zero-hole design without needing another statement format. Include the
dependencies of proof bodies as well as types, including necessary instances
and generated helpers. Preserve namespace/universe contexts and recheck the
new source: the earlier universe-name and formatting failures demonstrate why
source reduction is not itself a statement-equivalence certificate.

If that cannot fit, the official fallback is a **theorem declaration with a
Challenge-only proof placeholder**, and a genuine theorem in Solution. A
bare `axiom` target in Challenge does not match a proved theorem in Solution
under the installed rc3 Comparator. Do not implement that mixed-kind pair.

## What the installed Comparator actually accepts

Read directly from:

```text
C:/Users/MatthewColbrook/.elan/toolchains/leanprover--lean4---v4.35.0-rc3/src/lean/lake/Lake/Check/Compare.lean
```

The `compareAt` theorem-target branch permits these pairs:

```lean
| .thmInfo cc, .thmInfo sc
| .axiomInfo cc, .axiomInfo sc => ...
```

Every other pairing throws a constant-kind mismatch. Consequently a
Challenge `axiom target : P` and Solution `theorem target : P := proof`
would be rejected by that branch. This is static analysis of the actual
installed code, not a claimed new rejected-run log. Using an unproved axiom
in Solution to obtain matching kinds would contradict the permitted-axiom
requirement for a new mathematical claim.

A `theorem ... := by sorry` is a theorem-kind declaration, matching the kind
of a genuine Solution theorem. The comparator checks the selected theorem
types, then recursively compares their ordinary dependencies. It does not
compare selected theorem proof bodies. Actual Solution checking and axiom
closure must independently establish its genuine proof with the permitted
axioms only.

For the two completeness instances, use theorem-kind proposition proofs with
the same registered names and types on both sides. A named `instance` proving
`CompleteSpace ...` can be theorem-kind, as the earlier actual kind probes
showed. Do not classify declarations by source keywords alone; retain actual
compiled `getConstInfo` evidence for every final target.

## Official template and policy

The current [official Challenge template](https://raw.githubusercontent.com/PalomarRegistry/PalomarTemplate/main/Challenge.lean)
uses a theorem with a `sorry` proof. Its [Solution template](https://raw.githubusercontent.com/PalomarRegistry/PalomarTemplate/main/Solution.lean)
proves the same theorem with the actual library result and does not import
Challenge. This is the explicit published statement/proof separation pattern.

The current [submission policy](https://raw.githubusercontent.com/PalomarRegistry/PalomarPolicy/main/CONTRIBUTING.md),
sections 2.1--2.4, permits deliberate Challenge holes while requiring Solution
proofs to exclude forbidden axioms and native-execution bridges. It gives
Challenge 1,000 physical lines and 100 KiB, with warnings above 300 lines or
32 KiB. Solution instead has the general 10,000-physical-line Lean-source cap;
the Challenge-specific caps do not apply to it. Blank/comment lines count.
Challenge may not import project-specific proof or definition modules, even
if a previous packet verified them. The permitted Solution dependency scope
is broader. These are current policy facts, not registry acceptance of this
project.

## Reading the user's instruction accurately

The user required: “No sorry, unproved custom axioms or native-execution trust
may support the solution.” The user also requested a separately reviewed
Challenge and proofs in Solution. The literal trust boundary is the Solution
and its dependency closure; it is not a request that Challenge itself contain
complete proofs. The earlier wholly placeholder-free Challenge was our
implementation choice, not an additional human requirement.

My interpretation is that the official theorem-placeholder pattern satisfies
that instruction if all Solution proofs/definitions are genuine, Solution
never imports Challenge, no Challenge hole occurs in its transitive proof
closure, actual `#print axioms` reports contain only the permitted three,
and the new actual Comparator/kernel checks accept. This interpretation does
not authorize weakening theorem hypotheses/conclusions, omitting source
claims or changing conventional fixed definitions. Separate source-fidelity
review remains necessary.

The parent agent currently prefers zero holes everywhere if feasible. That
preference is respected by trying pruning first. If the official fallback is
later selected, describe Challenge expressly as an **unproved specification**
and Solution as the proved implementation. Do not keep a global claim such
as “zero proof holes in all files” when Challenge contains placeholders.
Report the Challenge placeholder count separately from Solution's zero
forbidden-axiom/placeholder closure. Existing verified zero-hole snapshots
must remain unchanged.

## Fixed definitions and alternative formats

Keep `definition_names: []` for fixed mathematical definitions. Under the
installed code that list denotes holes and skips their bodies. The required
fixed data/type definitions must instead remain ordinary dependencies of
selected theorem types, with actual reachability evidence and full recursive
ConstantInfo/body comparison. Explicit definitions and their mathematical
meanings still need independent review.

If avoiding the literal word `sorry` while allowing an unproved specification
were essential, a Challenge-only named axiom with the exact intended claim
could support a theorem-kind wrapper selected by Comparator. Solution would
contain a genuine theorem under the wrapper's name and no dependency on that
axiom. This follows the inspected matching logic, but is not the direct
official template and has not been tested here. It is still a Challenge hole,
duplicates statement text, and offers no advantage for the parent's preferred
zero-hole design or file-size goal. A bare axiom target remains incompatible
with a Solution theorem; a custom axiom supporting Solution remains forbidden.

A different option is to retain smaller independent genuine-proof packets or
eventually upstream reusable foundations into an approved canonical library.
Only actually approved/pinned library imports qualify; a local module or
prior registry snapshot cannot be treated as a Mathlib dependency. Proof
modules may be split on the Solution side if its general source cap becomes
relevant, while keeping the advertised theorem proofs genuine.

Before describing any new format as accepted, freeze and independently review
the complete intended statements, inspect actual declaration kinds and fixed
definition reachability, run the actual build/axiom/Comparator/kernel checks,
and retain the real output. Challenge-only specification holes must never be
used as evidence that an unproved source theorem has been formalised.
