# Proposed clean principal-results packet

AI design/statement assessment by `/root/claim_inventory`, 30 October 2026. This proposal changes no accepted source, snapshot, theorem or manuscript. No network, GitHub operation, Lean compilation, axiom query or Comparator/kernel run was performed. These candidate files are **not yet an upload-ready checked packet**.

## Recommended interface

Select one theorem, `AffineFK.affine_reverse_faber_krahn_principal_results`, with type `(M01 ∧ M02) ∧ M03`. Its left clause is the complete accepted Main35 type, copied without mathematical alteration. Its right clause is exactly the first clause of accepted Stage36. Grouping the conjunction this way reuses the accepted Main35 proof directly and avoids inventing three new proposition aliases or restating the inequalities under different conventions.

Solution needs only these two existing high-level proof endpoints:

```lean
public import AffineFK.MainTheorems
public import AffineFK.InformationSpectrumLogConcaveMeasure
```

Its entire new mathematical proof is conjunction introduction applied to the already proved endpoints. It never imports Challenge. No new analytic or geometric lemma is needed for this packaging step. These are the smallest stable high-level endpoints needed for direct reuse of the accepted conjunction plus M03; this is not a claim of a globally minimal proof DAG.

The exact static project-import closure has **992 existing modules**: all 989 accepted Main35 source files, byte-identical, and three accepted Stage36 files (`InformationSpectrumLogConcaveMeasure`, `LogConcaveMeasureBalls`, `LogConcaveMeasureDensity`). The Stage36 aggregate and the new G01/W13/S07 endpoint modules are unnecessary imports. The complete list and hashes are in `static_proof_source_manifest.json`. This is an actual source-import traversal, not a newly compiled private proof closure or borrowed acceptance of the new target.

## Canonical statement fidelity

| Selected clause | Exact scope preserved | Existing source proof |
|---|---|---|
| M01, manuscript 124–130 | One real positive universal constant before every positive natural dimension and every compact convex body with nonempty interior; a literal special-linear map; finite actual H0 Rayleigh eigenvalue; original real volume power `2/n` and bound `C*n`. No symmetry, volume-one, boundary regularity, information or groundstate hypothesis is added. | First clause of `AffineFKProof.affine_reverse_faber_krahn_main_theorems`. |
| M02, manuscript 155–162 | One real positive universal constant before every positive dimension; compact convex origin-symmetric body with nonempty interior, unit volume and actual maximal Gaussian position; actual eigenvalue at most `C*n`. | Second clause of that same accepted theorem; the complete fixed `UniformSymmetricGaussianDirichletBound` definition is present. |
| M03, manuscript 178–191 | Every real `P ≥ 2`, then one positive `C(P)` before dimension, law and supporting body; actual probability, negation invariance, set-based log-concavity, literal zero coordinate means and unit raw covariance, actual least Poincare bound, finite canonical relative Fisher information, AE support in the original symmetric convex body; actual eigenvalue at most `C(P)*(n+sqrt(n*I))`. | `AffineFKProof.information_spectrum_logConcaveMeasure_uniform_constant`. |

The separate constants in M01 and M02 are not forced to coincide. M03's constant remains outside all dimension/law/body quantifiers. The finite-information premise remains before `.toReal`; no density witness or desired information/spectral conclusion becomes an extra hypothesis. The source's variational H0 definition, canonical Euclidean volume, normalized standard Gaussian, and actual SL action retain their accepted complete meanings. The full integration-domain and weak/classical correspondence discussion remains in the frozen principal correspondence review (SHA256 `c267a2b82b5e926b491346d2f15e024f3eadbefa71b7e93f4fc5e82224862c16`).

Only M01/M02/M03 are selected. G01, W13 and S07 may legitimately occur as genuine internal proof dependencies, but are not extra advertised conjuncts. This design does not select strict positivity/simplicity or claim the entire manuscript is verified.

## Fixed data and source-copy boundary

Challenge has **29 complete conventional owners**: 26 data declarations (including the ambient abbreviation) and three genuine helper theorems. Nineteen owners are copied as whole namespace blocks from the accepted Main35 canonical Challenge. Ten M03-specific owners are copied as whole namespace blocks from accepted Stage36: actual set-based log-concavity; density measure; square-root Sobolev and Fisher definitions; canonical RN density and relative law information; actual Poincare predicate/infimum and its named Euclidean completeness proof.

The Fisher block deliberately retains the genuine `fisherInformation` owner because earlier compiled evidence showed generated-helper ownership may matter even when that owner is outside the ordinary TYPE closure. The design excludes weighted Stein and W13-only definitions. All complete copied blocks, scopes, opens and bodies are byte-identical after CRLF-to-LF normalization; their accepted origins and normalized hashes are recorded in `proposal_manifest.json`. No automated declaration-header/proof folding was applied. Duplicate mathematical names are rejected by the generator.

There is exactly **one Challenge-only benchmark placeholder**, as in the saved reviewed Palomar protocol. Solution has no placeholder, custom axiom or native-execution bridge. Config selects only the new conjunction, leaves `definition_names` empty and permits exactly `propext`, `Classical.choice` and `Quot.sound`. Empty definition holes preserve the requirement that referenced fixed definitions be compared by their actual bodies.

## Candidate files and limits

| File | Physical lines | Raw UTF-8 bytes | SHA256 |
|---|---:|---:|---|
| `Challenge.lean` | 327 | 22,148 | `f1e54850c2a7e20d96f5c26af48ec68dfa208d718837c6f91e966444172d01c1` |
| `Solution.lean` | 331 | 22,409 | `40e7bf57f72e19da664b408a95ab9fdca52caf883d9adf7cc351f7c50708e659` |
| `AxiomAudit.lean` | 3 | 98 | `ae9b8510fa4bb76d5397732612b1c72644ddbc8d9199d1b8f4fedb913897d459` |
| `comparator.json` | 13 | 268 | `cc5393783e0205e982a32ea7cd502d004be0ef3a17f83320f48d88a382e27fe7` |

Challenge is within the saved 1,000-line / 100-KiB hard caps and below 32 KiB; 327 lines exceeds the saved 300-line advisory threshold. Preserving the accepted import/declaration layout is preferable to an unnecessary untested formatter merely to suppress that warning. A later owner can trim imports only with fresh actual checking. These proposal files use explicit LF endings. The 992 proof modules individually satisfy the general 10,000-line source limit.

## Required before upload-ready status

The new root-module names, combined conjunction and reduced canonical data set require their own ordinary compilation, actual declaration-kind/type/body dependency comparison, standalone `#print axioms` evidence, official metadata validation and actual all-six Comparator run. Those are packaging checks for a new packet, not grounds to rerun all older accepted packets. Compiler-generated dependency-owner names and module scoping are the remaining concrete packaging risk; source token comparison alone cannot certify them. If actual comparison identifies a missing genuine helper owner, retain its exact complete accepted body and re-review the resulting final files rather than adding a hole or relaxing comparison.

The proposed proof files should be copied into a new clean repository root only after parent coordination. The 992 exact proof sources and required attributed licenses/origins should be copied without the development caches, old packet directories, failed experiments or historical logs unless a specific reproducibility artifact is deliberately included. Existing development/snapshots remain preserved in their current workspace. A concise final README, actual checking log/version receipts and `formalization.yaml` should describe only M01–M03 and the actual final packet evidence; the metadata is not fabricated by this proposal.

The draft generator and its static assertions completed successfully. This is AI design/source-fidelity work, not a second independent endorsement of this author's new packaging. Separate non-author review and actual compiled/Comparator evidence are still required. No source theorem was weakened and no GitHub interaction occurred.
