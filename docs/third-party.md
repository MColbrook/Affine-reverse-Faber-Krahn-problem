# Reused proof sources and licences

Original per-file notices are retained. New local formalization code and
documentation use the root Apache-2.0 licence. The following source families
retain their own licences and authorship.

| Source | Selected proof modules | Exact upstream commit | Licence |
| --- | ---: | --- | --- |
| OpenAI, symmetric Mahler development; upstream model authorship retained | 229 | `7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a` | [Apache-2.0](../AffineFK/OpenAIMahler/LICENSE) |
| Djalil Chafaï, Brascamp–Lieb proof | 234 | `a1b2ba84e7dad8ba11b5c49a18b986a762a00a41` | [MIT](../AffineFK/ChafaiBrascampLieb/LICENSE), original copyright retained |
| Adam Benenson, Euclidean Rellich–Kondrachov development | 15 | `70f85d4c1bf99c6e7d61e8be4daa6f3664d08d23` | [Apache-2.0](../AffineFK/BenensonRellich/LICENSE) |
| Jonathan Ho and contributors, Prékopa–Leindler development | 2 | `29768f8beeaf17295cdf3853d37da35d7e2b0a5f` | [Apache-2.0](../licenses/prekopa-leindler-LICENSE) |
| Scott Armstrong and Amélie Loher, Gaussian `L²` closure excerpt | 1 | `5d770d1a6d69fac6dbb63060e8a89861bf3ee330` | [Apache-2.0](../licenses/gaussian-closure-LICENSE) |

The remaining 511 proof modules are local constructions/adaptations, with
individual reuse attribution in their source headers. Mathlib and its
dependencies are separately pinned Lake dependencies with their existing
licences; their caches are not redistributed here. Lean and the independent
kernel tools retain their distribution notices.

`verification/provenance/upstream-source-map.json` maps all 481 selected
originals to their actual ported proof files. It includes original SHA-256
and Git-blob identifiers, ported hashes, exact upstream repositories/commits,
licence locations and complete textual differences. The selected original
snapshots are noncompiled `.txt` documents under `originals/`; complete
original-to-current differences are under `changes/`. The Gaussian closure
reuse is an explicitly attributed generic excerpt; the retained original
full-file snapshot does not become an extra proof import.

The Mahler mathematical bodies are unchanged; imports and visibility were
adapted. Brascamp–Lieb and Rellich compatibility changes are exposed by the
complete per-file differences rather than hidden behind import renaming.
No upstream scripts, executable binaries or upstream checker-disable settings
are used. The package has its own ordinary sandboxed six-kernel check.

The manuscript is by Matthew J. Colbrook and George Stepaniants and retains
their rights. It is included only as the frozen mathematical source for
statement correspondence; the code licence does not relicense it.

Mathematical attribution also includes Pierre Bizeul for information jump,
Max Fathi for higher-order Stein identities, and Michel Ledoux, Ivan Nourdin
and Giovanni Peccati for HSI. Further attributions, including Mathlib
contributors, are retained in source headers and `formalization.yaml`.
No upstream endorsement is implied.
