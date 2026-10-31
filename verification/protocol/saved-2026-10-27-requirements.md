# Palomar preparation requirements

Independent AI research by the `palomar_requirements` Codex agent, 27 October
2026. This is a tooling and metadata review, not a mathematical or human review.
No registration or remote submission was performed. The main manuscript and Lean
statement/proof files were not edited by this reviewer.

## Environment selection

The authoritative [minimum toolchain file](https://raw.githubusercontent.com/PalomarRegistry/PalomarSubmission/main/toolchains.json)
currently has schema version 2 and minimum `v4.35.0-rc2`.
The [official template toolchain](https://raw.githubusercontent.com/PalomarRegistry/PalomarTemplate/main/lean-toolchain)
also uses `leanprover/lean4:v4.35.0-rc2`. The locally installed
`leanprover/lean4:v4.35.0-rc3` is new enough. If Mathlib is used, its resolved
revision must have exactly that toolchain, including the release-candidate suffix.
Pin both the release and the full dependency commit graph in the project's own
files. An existing compiled cache is useful for development but is not a
substitute for a portable manifest.

The old independent Comparator repository is archived. Use the `lake comparator`
shipped with the selected Lean release. Its command, exporter, checker, and
independent checkers are bundled in the toolchain; a separate Comparator Git pin
is not required for this current route. The template now demonstrates the core
command, rather than the older Landrun-based executable.

## Windows limitation, checked in the installed rc3 source

Inspected read-only:

```
C:/Users/MatthewColbrook/.elan/toolchains/leanprover--lean4---v4.35.0-rc3/src/lean/lake/Lake/CLI/Check.lean
C:/Users/MatthewColbrook/.elan/toolchains/leanprover--lean4---v4.35.0-rc3/src/lean/lake/Lake/CLI/Help.lean
C:/Users/MatthewColbrook/.elan/toolchains/leanprover--lean4---v4.35.0-rc3/src/lean/lake/Lake/Check/Compare.lean
```

`mkContext`, around lines 599--622 of `Check.lean`, rejects the ordinary
sandboxed mode on a non-Linux platform. The sandbox uses Linux namespaces and
`bwrap`. Both pre-exported-input options still reach this check before judging
the exports. They do **not** by themselves make the ordinary command work on
Windows. The [official Lake reference](https://lean-lang.org/doc/reference/latest/Build-Tools-and-Distribution/Lake/)
agrees about Linux-only sandboxing.

The installed Windows toolchain does contain `leanexport.exe`,
`leanchecker.exe`, `leanchecker-paranoid.exe`, `lean4lean.exe`, `nanoda_bin.exe`,
`con-leche.exe`, and `con-ron.exe`. Thus kernel replay tools are available, even
though native Windows cannot supply the normal sandbox.

The supported expert flag `--inadvisably-no-sandbox` can permit an actual local
Comparator run on Windows. It emits an explicit untrustworthiness warning. An
accepted run in that mode must be labelled **unsandboxed local Comparator
acceptance**, never described as an official Palomar-equivalent sandboxed run.
It enlarges the process-isolation trust surface; it does not turn a bad theorem
into a theorem. Kernel evidence and missing process isolation are separate facts.
For the ordinary security contract, rerun in a Linux environment with working
`bwrap` and user namespaces. Do not emulate `bwrap` with a pass-through script.

The two export options are:

```
lake comparator --config comparator.json \
  --challenge-from-export challenge.ndjson \
  --solution-from-export solution.ndjson
```

An export-only judgement concerns those export files. It does not establish that
they correspond to the source checkout. Keep the producing commands, file
hashes, and build logs if using this route.

## Challenge and proof separation

The [official example Challenge](https://raw.githubusercontent.com/PalomarRegistry/PalomarTemplate/main/Challenge.lean)
contains a deliberate statement placeholder; the [example Solution](https://raw.githubusercontent.com/PalomarRegistry/PalomarTemplate/main/Solution.lean)
proves the same named theorem without importing that Challenge. Comparator's
installed `compareAt` checks the declarations' names, kinds and types, then
recursively compares constants referenced by the statement.

A Challenge may instead contain a genuine proof. A theorem without a placeholder
is valid input: Comparator compares theorem types, not the two proof terms.
For this user's strict requirements, genuine independently checked proofs of the
selected fragment statements allow a wholly placeholder-free project. If a full
unproved intended theorem is retained as a `Prop`-valued definition, label it an
unproved target; it is not a proved theorem or a valid replacement for the result.

The Solution must not depend on the Challenge or on `sorryAx`,
`Lean.ofReduceBool`, an unproved project axiom, an opaque missing definition, or
a native-execution result. A syntax search alone does not prove this: obtain
actual `#print axioms` output and a kernel/Comparator verdict for every advertised
declaration. A valid implication whose hypotheses include an unproved analytic
input proves only that implication. Do not advertise its conclusion as
unconditional.

The [submission policy](https://raw.githubusercontent.com/PalomarRegistry/PalomarPolicy/main/CONTRIBUTING.md)
requires new modules and a small auditable Challenge. Its complete import
closure may use core and authenticated Mathlib, Tau Ceti or CSLib dependencies;
project-specific imported definitions are excluded. Statement definitions needed
locally should be explicit, conventional, documented, and checked by the separate
fidelity reviewer. Ordinary supporting lemmas do not establish the paper's main
result merely by being named in a Comparator configuration.

## Comparator configuration and commands

Use the [official configuration shape](https://raw.githubusercontent.com/PalomarRegistry/PalomarTemplate/main/comparator.json),
with project-specific theorem names and only the requested three axioms:

```json
{
  "challenge_module": "Challenge",
  "solution_module": "Solution",
  "theorem_names": ["TheActualFullyQualifiedDeclaration"],
  "definition_names": [],
  "permitted_axioms": ["propext", "Classical.choice", "Quot.sound"]
}
```

`theorem_names` must not be empty for a submission. Do not include
`external_kernels` in the submitted configuration. The registry controls the
additional checker configuration. `enable_nanoda` is accepted but ignored by
the registry and can be omitted.

The [official replay script](https://raw.githubusercontent.com/PalomarRegistry/PalomarTemplate/main/scripts/verify-comparator.sh)
checks for `bwrap`, `lake`, `lean`, and Python 3, and verifies the bundled tools.
It makes a protected temporary configuration selecting bundled NanoDa and
con-ron, then runs:

```
lake exe cache get
lake comparator --config <generated-configuration>
```

Core `--paranoid` additionally requests all bundled checkers, including
`leanchecker-paranoid`, `lean4lean`, `nanoda`, `con-leche`, and `con-ron`.
Report each actual acceptance or support/capacity decline separately. A missing
or failing checker is not acceptance. The root agent, rather than this research
reviewer, owns the actual checking runs and output logs.

## Metadata and source requirements

The [upstream v0.4 schema](https://raw.githubusercontent.com/mathlib-initiative/formalization.yaml/main/schema/v0.4.schema.json)
has required project, sources, automation and review sections. The
[template metadata](https://raw.githubusercontent.com/PalomarRegistry/PalomarTemplate/main/formalization.yaml)
and Palomar impose additional preparation requirements. Use `version: v0.4` and
fill these project-specific facts honestly:

| Field | Required meaning for this development |
| --- | --- |
| `project.name`, `project.description` | State the actual verified scope, including partial status. |
| `project.authors`, `project.responsible_maintainers` | Human names only; do not claim the paper's second author reviewed or formalised Lean without evidence. |
| `project.license` | An actual chosen SPDX licence matching a root licence file; do not invent author permission or silently relicense the manuscript. |
| `classification.arxiv`, `classification.msc2020` | Mathematics of the checked results, rather than the fact that Lean was used. |
| `sources` | Nonempty list with titles and relationship; this is source-based work, not a theorem first presented by the Lean files. |
| `status.scope` | Full paper target versus proved fragments, omitted prerequisites, and any changed hypotheses. |
| `status.sorry_count`, `status.sorry_in_definitions` | Actual nonnegative integers for the proof development. |
| `status.axioms` | Axioms actually used, determined from checking output. |
| `automation.methods` | Agent work, tactics, model disclosure if known, tools and setup. |
| `review.status`, `review.reviewers`, `review.notes` | Identify independent AI reviews as AI; distinguish them from kernel results and from human review. |
| `fidelity.divergences`, `alignment` | Source-to-Lean mapping and every material omission or weakening. |
| `acknowledgements` | Mathlib, reused proof authors, Lean and checker tools. |

All Lean files in a prospective submitted checkout require the module system and
must remain within the per-file policy caps; the Challenge has stricter limits.
Do not commit compiled artifacts outside `.lake`. Keep portable, exact dependency
pins. A public fixed Git commit and licence are required for an actual registry
submission; a local development folder alone is not registered or ready merely
because a supporting proof compiles.

The upstream schema is intentionally permissive. Passing a generic YAML/schema
check does not imply compliance with Palomar's tighter policy or statement
fidelity. Conversely, the template's Ruby validator mostly checks basic shape,
licence and remaining template sentinels; it is not the full registry verifier.

## Limits of this review

These findings combine official documents fetched on the stated date with
read-only inspection of the installed rc3 implementation. Some prose in the
policy describes the older standalone verifier pipeline, whereas the current
template uses bundled `lake comparator`; the current minimum file and installed
implementation give the concrete toolchain/command facts above. Registration
would be governed by the registry's actual selected policy and mechanical run.
No checker run or submission result is asserted by this report.
