# Independent AI review: supported H1 minimizing limits

Reviewer: `/root/formalization_coverage`, who authored neither new source file. I read all five complete theorem headers and proof bodies in `H1LocalizedCompactness.lean` and `H1SupportedMinimizingLimit.lean`, the relevant actual H0 support, Rellich, Hilbert graph-energy and Rayleigh-variation dependencies, and the delicate primary Mathlib interfaces. No mathematical, domain, normalization, energy-constant or trust defect was found.

This is an AI mathematical/fidelity/clarity review, not human review or a new compiler/Comparator verdict. The reviewer authored some frozen reused unweighted-H1 and weak-compactness foundations; this report is independent for the five new root-authored declarations, not an independent re-review of those older authored foundations. Their existing separate reviews remain applicable.

## Frozen sources and evidence

| Source | SHA256 | New declarations |
| --- | --- | ---: |
| H1LocalizedCompactness.lean | `0a20722101162083373e184fa1c368ecd1e4282421b153e6626f96995aa299db` | 3 theorems |
| H1SupportedMinimizingLimit.lean | `8b0d08491b9671693ef321c62c9bc477aacc5e467c9faf264655fb75c8393cb5` | 2 theorems |

`audit/h1_minimizing_limit_source_manifest.json` has SHA256 `160f045601fd37f3d8f33dee8768daf4a78966d21b4254888b45fc50bfa8e5f3`. The read-only evidence script `audit/review_h1_minimizing_limit.py` completed with exit0, independently checking all 87 pinned source/probe files, the six actual raw logs, final source/manifest pins and precisely five axiom reports. Its JSON is `audit/h1_minimizing_limit_independent_review.json`, SHA256 `b531bdbad341988ef4fa98376113b22b263ddbb36f284fc30f7f60eda3d720e7`.

Actual inspected successful author checks, all using the pinned Lean 4.35.0-rc3 environment, were:

| Actual log in logs/branch_bochner/ | Exit | Seconds |
| --- | ---: | ---: |
| h1-localized-compactness-build-04.txt | 0 | 12.389 |
| h1-supported-minimizing-limit-build-01.txt | 0 | 23.779 |
| h1-minimizing-limit-axioms-01.txt | 0 | 5.016 |

All five fresh reports use only `{propext, Classical.choice, Quot.sound}`. The first three failed compactness attempts remain separately preserved; their historical source hashes are not represented as the final source. The reviewer did not rerun Lean or edit any proof source.

## Mathematical reading of all five proofs

1. **`h1_compact_multiplier_value_isCompact`.** A compact smooth multiplier's topological support is contained in an actual bounded open ball. Its genuine H1 multiplier maps into that ball's actual H0 space by the proved compact-core closure argument. The operator is then factored through the actual compact H0 value map. Compactness is supplied by the attributed Adam Benenson Rellich development and continuous-linear composition; it is not a premise of this theorem. The result covers every finite dimension and permits the zero multiplier.

2. **`supported_l2_limit`.** Strong L2 convergence implies convergence in measure, and a genuine subsequence converges almost everywhere. Combining that event with the countable intersection of the original exterior-zero events forces the same exterior-zero property of the limit, by uniqueness of real limits. The primary Mathlib APIs are `tendstoInMeasure_of_tendsto_Lp` and `TendstoInMeasure.exists_seq_tendsto_ae` in `MeasureTheory.Function.ConvergenceInMeasure` (Rémy Degenne, Kexing Ying). Their use here requires no finite total Lebesgue volume. K need not be measurable for this pure almost-everywhere implication.

3. **`supported_l2_near_h1_subsequence`.** An actual compact cutoff equals one on compact K. The bounded scalar coefficient operator therefore fixes every supported f_k almost everywhere. Its continuous-linear action takes the original errors Value(v_k)-f_k to errors tending to zero. The genuine compact multiplier value operator extracts a strictly increasing subsequence converging strongly in L2; subtraction of the vanishing errors yields strong convergence of f_(s(k)) itself. The compactness APIs are `IsCompactOperator.isCompact_closure_image_closedBall`, `IsCompactOperator.comp_clm` and `IsCompact.tendsto_subseq`. They assert the actual image/closure and actual subsequence conclusions used in the proof.

4. **`supported_h1_normalized_limit_energy`.** Bounded U gives compact closure(U), to which the preceding theorem applies. The original values Value(v_(s(k))) converge to the same strong L2 limit g. The graph-energy theorem is then applied explicitly to **v_(s(k)) and b_(s(k))**, using the original gradient bound and its original limit B. No cutoff sequence or cutoff gradient energy is substituted. The original f subsequence's support passes to g. The proved zero-exterior H1→H0 theorem supplies membership of that same graph element w; psi is precisely the subtype containing w. Its value and gradient therefore remain unchanged. The membership theorem's internal bounded-dilation estimate does not multiply the final energy. Strong L2 convergence preserves the exact squared norm one, with no subsequent rescaling or division loss. Thus the actual H0 element satisfies the exact bound ||Gradient(psi)||²<=B.

5. **`supported_h1_normalized_minimizing_limit`.** Exact normalization makes the value nonzero. The actual Rayleigh-infimum inequality supplies the lower energy bound, while the preceding theorem supplies the matching upper bound with B=lambda_1(U).toReal. Equality follows. Since 0 lies in U, the open domain is nonempty and the separately proved actual eigenvalue is finite; `ENNReal.ofReal_toReal` therefore reconstructs the true extended eigenvalue. The actual Rayleigh-attainment variational theorem then gives the original weak eigen-equation. That equation and attainment are conclusions, not hypotheses. Dimension zero introduces no discarded case or division by a dimension.

The graph-energy dependency itself preserves the original energy by genuine Hilbert/Riesz weak clustering and scalar Cauchy–Schwarz, with strong convergence identifying the actual value. The new code uses that proved theorem with the correct original sequence and bound. The support-to-H0 dependency uses actual inward dilations and value injectivity; this review does not treat an assumed trace theorem as an input.

## Fidelity, clarity and boundaries

The declarations do exactly what the source documentation states: they extract an actual strong L2 subsequence from a supplied supported normalized sequence near bounded global H1 approximants, obtain a genuine H0 limit with the original energy bound, and derive an actual weak minimizer when those original bounds converge to the actual infimum. The hypotheses do not smuggle in a desired limit, desired energy equality, compactness assertion or weak eigen-equation.

Existence of such Gaussian competitors/approximants is a later construction, not proved here. No positivity, log-concavity, simplicity or evenness of the minimizer is asserted. No full killed-kernel spectral identification or full manuscript theorem is certified by this report. No source change is requested. Non-author review is complete for these five declarations; no own Comparator/six-kernel or human-review claim is made.
