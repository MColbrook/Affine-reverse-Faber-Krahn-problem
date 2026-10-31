# Main35 canonical packet: independent AI statement and fixed-data review

Reviewer: `/root/claim_inventory`. This is an independent AI review of the canonical Challenge, complete conventional data and helper bodies, selected type, Solution wrapper, configuration and source-copy fidelity. It is not human review or an actual Comparator verdict. I did not author the new root/E main compositions. Some reused C proofs are mine; their non-author root/B/E cross-reviews remain the separate mathematical-review layer. I do not claim to have manually reread all 989 source modules here.

No mathematical, domain, quantifier, constant or statement-fidelity defect was found. The exact reviewed Challenge is `AffineFK/MainTheoremsResults/Challenge.lean`, SHA256 `df39f60ad677d90a70888b136093531a9b9d0a97e2f531ca2865c07f6d653715`; Solution is `124fc778453eb02e30d04d8c097b22931c854b46f3a77628de25dbdbe944ab7e`. Configuration `main-theorems-comparator.json` is `30384fa7351bf0a63beaa92bd3335d5b12f774f33b1104badf065409a9a652be`. The machine-readable report pins these and the exact interface/source manifests.

## Original conclusions and assumptions

I compared the complete selected type against the frozen manuscript, SHA256 `1d30574bf6a09012c0492449d6860884c993b191837c9c0d2a9bd17080a3d0bc`, including its definitions at lines 101–111 and theorems at lines 124–130 and 155–162. The original 141-entry inventory is unchanged.

The first conjunct preserves full **M01**. There exists one real `C > 0` before every natural `n > 0` and every `K : Set (EuclideanSpace ℝ (Fin n))`. Its body hypotheses are exactly compactness, convexity and nonempty interior, the manuscript's definition of a convex body. It returns a literal `Matrix.SpecialLinearGroup (Fin n) ℝ` element `S`, finiteness of the genuine eigenvalue on `interior(S K)`, and

`lambda_1(interior(S K)).toReal * volume(K).toReal^(2/n) ≤ C*n`.

The power has the original real exponent `2/n`. The map is the actual linear action of the determinant-one matrix. No input symmetry, centering, normalization, smooth boundary, Fisher information, covariance, ellipsoid, eigenfunction or desired spectral conclusion is present. Positive dimension is exactly the original integer range. The explicit finiteness conjunct prevents an infinite ENNReal eigenvalue from becoming a misleading zero through `toReal`.

The second conjunct preserves full **M02**, not merely existence of a convenient position or a covariance-conditional estimate. Its separate real `C > 0` precedes all positive dimensions and every original compact convex body with nonempty interior, origin symmetry and volume one, already in maximal Gaussian measure position. The latter is the complete condition that every actual special-linear image has standard Gaussian measure at most that of the original body. Since the identity is included, this is precisely the manuscript's attained maximum statement. The conclusion is the actual eigenvalue bound by `ENNReal.ofReal (C*n)`. This finite upper bound rules out infinity and gives the original real inequality. The two positive constants need not coincide, exactly as in the two original theorems.

The selected statement has no argument supplying the missing main theorem, a replacement geometric result, a chosen ground state, a covariance lower bound or the output inequality. These are derived in the genuine imported proof. Its source counterpart is the exact conjunction in `MainTheorems.lean`; the source M02 proof applies the proved unconditional ellipsoid-intersection theorem to the genuine symmetric spectral reduction. The tuple proof combines actual established M01 and M02 results.

## Complete conventional meanings

I read all 20 complete canonical declarations, their explicit arguments, implicit/typeclass contexts and every namespace/open-scope group. There are no standing `variable` declarations. The 19 nonbenchmark declarations comprise 17 semantic data owners and two genuine theorem helpers. Their full bodies and headers match their source declarations modulo namespace replacement and whitespace. This lexical equality supplements, rather than substitutes for, the manual semantic review and later actual compiled comparison.

| Fixed owner | Meaning preserved |
| --- | --- |
| `SobolevAmbient` | Actual scalar/vector `L²` product with the `WithLp 2` Hilbert norm. |
| `testFunctionGradient` | Actual Fréchet derivative of a compact smooth scalar test, transported through Hilbert duality to its vector gradient. |
| `gaussianPositionSLLinear` | Continuous Euclidean linear equivalence of the literal special-linear matrix; determinant nonvanishing follows from determinant one. |
| `GaussianPositionMaximal` | Standard Gaussian measure comparison under every such actual action. |
| `unweightedTestToL2` | Genuine compact smooth function embedded into Lebesgue `L²`, with finiteness derived from compact support. |
| `unweightedSmoothPair` | The actual value and actual gradient pair in the above ambient space. |
| `unweightedSobolevGraph` | Topological closure of those genuine pairs. |
| `unweightedValue` | Scalar `L²` projection restricted to that graph. |
| `unweightedGradient` | Vector `L²` projection restricted to that graph. |
| `dirichletTestToTop` | The same globally defined test function, retaining its support inside the open domain and then regarded as a test on the whole space. |
| `dirichletTestToH1` | Its actual value/gradient graph element; membership is proved. |
| `dirichletSobolev` | Closure of domain-supported compact smooth tests in the actual H¹ graph, the conventional H⁰¹ completion. |
| `dirichletValue` | The actual scalar `L²` value of this H⁰¹ element. |
| `dirichletGradient` | Its actual vector `L²` weak gradient. |
| `dirichletRayleigh` | Squared gradient norm divided by squared value norm, with no Brownian factor `1/2`. |
| `dirichletEigenvalue` | ENNReal infimum of those quotients over every nonzero value, not an unspecified eigenvalue function. |
| `UniformSymmetricGaussianDirichletBound` | The complete universal M02 body/maximality assumptions and actual spectral conclusion. |

I also read the two complete helper proofs. `gaussianPosition_matrix_det` is the actual determinant identity for the Euclidean matrix action, proved by the canonical orthonormal-coordinate determinant lemmas. `unweighted_smooth_pair_mem` is actual inclusion of the smooth-pair range in its closure. They supply conventional definition bodies rather than assumed main conclusions. Previously proved value injectivity makes the nonzero-value Rayleigh domain the usual nonzero-function domain; compact-test H⁰¹ elements are zero-extended, and the retained source theory identifies the squared norms with the actual integral energies. This packet does not replace the variational Dirichlet eigenvalue with an arbitrary spectral proxy.

The namespace groups preserve each original source context and close before opening the next group. One inherited `maxHeartbeats` option remains immediately before a namespace end; it carries no mathematical hypothesis or data. Its actual syntactic/elaboration outcome belongs to the separately pending packet build, not to this review.

## Canonical boundary, proof reuse and evidence

Challenge imports 191 canonical Mathlib modules only. Its only placeholder is the disclosed selected benchmark theorem. Every fixed data/helper declaration has a genuine complete body. Solution adds the actual `AffineFK.MainTheorems` proof import and directly applies `AffineFKProof.affine_reverse_faber_krahn_main_theorems`; it never imports Challenge. The source theorem has a term assignment. The independent copy check compares its full type up to its own `:=`, rather than truncating only at `:= by` and accidentally losing the term proof/type boundary.

Configuration selects exactly this aggregate theorem, has zero `definition_names` holes and permits only `propext`, `Classical.choice`, `Quot.sound`; no checker-disabling flag is inherited. The source-copy validator checked all 989 current source hashes against the interface manifest and screened their comment-free code for placeholders, custom unproved axioms, unsafe/native-execution support and implementation replacement. It does not treat this lexical screen as a kernel proof. The bundle includes 234 attributed Ginibre/Brascamp–Lieb modules, 15 attributed Rellich modules and 229 attributed OpenAI Mahler modules. Original provenance/licences and separate source-review boundaries remain retained.

The exact source-pin union of accepted Stage33 and Stage34 accounts for 950 unchanged modules; the new remainder is 39. The actual fresh source axiom log contains 213 specified public declarations outside that unchanged union, exits zero and reports only subsets of the permitted three axioms. The actual origin-aware source closure log exits zero with 5,564 project dependencies; its eight `other` entries are the four genuine imported structures and their constructors named in the manifest. The actual source TYPE traversal exits zero with 129 constants. These are distinct from the 20 manual canonical owners and from the forthcoming compiled packet diagnostics; no equal-count inference is made.

Challenge is 280 physical lines/18,614 raw bytes; Solution is 282 lines/18,706 raw bytes. Challenge meets both its 1,000-line and 102,400-byte limits, and every retained source module is within the per-file 10,000-line cap. No Lean source, generator or configuration was edited and no compiler/Comparator/kernel was run by this review.

Actual read-only audit command:

`C:/Users/MatthewColbrook/.cache/codex-runtimes/codex-primary-runtime/dependencies/python/python.exe -X utf8 scripts/review_stage35_packet_source_copy.py`

Actual output: `PASS`, 19 matching nonbenchmark owners, 989 modules, 213 fresh source axiom reports, source TYPE 129 and full source closure 5,564. The resulting `audit/stage35_independent_packet_review.json` has SHA256 `bf4e3d319c54e37fa2d2bf59a0920ce7fee10e151d07b43f96ac395dba9ec647`, `independent_ai_review_complete: true`, and `defects_found: []`. Its exact pin map covers Challenge, Solution, configuration, interface/source manifests, selected original source, conventional-definition sources, actual source logs, original manuscript and inventory, and the separate fidelity/source reviews.

This review is complete for the canonical statement/data/source-copy layer. Actual packet build, compiled type/body/private-closure diagnostics, metadata and official schema still require the separate actual-evidence addendum. Main35's own six-kernel Comparator acceptance has not been claimed here. Establishing both main conclusions does not establish every one of the original 141 intermediate assertions, strict positivity/simplicity or all original alternative proof steps. The separate remaining-obligations inventory retains those boundaries.
