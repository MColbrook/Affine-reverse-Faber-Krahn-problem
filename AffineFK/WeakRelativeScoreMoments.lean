module

public import AffineFK.WeakRelativeScoreMomentsCutoff
public import AffineFK.FirstOrderSmoothingComponent

/-!
# Mean and cross moments of an actual weak Gaussian-relative score

Only an L2 field, L2 coordinates and the original compact-vector weak
identity are assumed. Constant and coordinate tests are obtained by
genuine compact cutoff limits. All limiting pairings are L1 by L2
Holder, and the derivative boundary terms have proved uniform bounds.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory TopologicalSpace InnerProductSpace Filter
open scoped Distributions RealInnerProductSpace Topology

theorem weakRelativeScore_component_mean (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (i : Fin n) (r : EuclideanSpace ℝ (Fin n) → ℝ) (hr : MemLp r 2 ν)
    (hxi : MemLp (fun x : EuclideanSpace ℝ (Fin n) => x i) 2 ν)
    (hweak : ∀ φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ),
      (∫ x, r x * φ x ∂ν) = (∫ x, x i * φ x ∂ν) - ∫ x, partialTest n i φ x ∂ν) :
    (∫ x, r x ∂ν) = ∫ x : EuclideanSpace ℝ (Fin n), x i ∂ν := by
  obtain ⟨χ, hχ, hinner, _houter, M, hM0, hM⟩ := exists_smooth_unit_cutoff n
  have hχ0 : χ 0 = 1 := hinner 0 (by simp)
  have hleft := sobolevFisher_cutoff_integral_tendsto n ν r
    (hr.integrable (by norm_num)) χ hχ0 hχ
  have hright := (sobolevFisher_cutoff_integral_tendsto n ν (fun x => x i)
    (hxi.integrable (by norm_num)) χ hχ0 hχ).sub
    (weakRelativeScore_cutoff_derivative_integral_tendsto n i ν χ hχ0 M hM0 hM)
  have hleft' : Tendsto (fun k => (∫ x, x i * cutoffSequence χ k x ∂ν) -
      ∫ x, partialTest n i (cutoffSequence χ k) x ∂ν) atTop (𝓝 (∫ x, r x ∂ν)) := by
    simpa only [hweak] using hleft
  simpa only [sub_zero] using tendsto_nhds_unique hleft' hright

theorem weakRelativeScore_component_cross_moment (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (i j : Fin n) (r : EuclideanSpace ℝ (Fin n) → ℝ) (hr : MemLp r 2 ν)
    (hxi : MemLp (fun x : EuclideanSpace ℝ (Fin n) => x i) 2 ν)
    (hxj : MemLp (fun x : EuclideanSpace ℝ (Fin n) => x j) 2 ν)
    (hweak : ∀ φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ),
      (∫ x, r x * φ x ∂ν) = (∫ x, x i * φ x ∂ν) - ∫ x, partialTest n i φ x ∂ν) :
    Integrable (fun x => r x * x j) ν ∧
    Integrable (fun x : EuclideanSpace ℝ (Fin n) => x i * x j) ν ∧
    (∫ x, r x * x j ∂ν) = (∫ x : EuclideanSpace ℝ (Fin n), x i * x j ∂ν) -
      (if i = j then (1 : ℝ) else 0) := by
  have hrx := hr.integrable_mul hxj
  have hxx := hxi.integrable_mul hxj
  refine ⟨hrx, hxx, ?_⟩
  obtain ⟨χ, hχ, hinner, houter, M, hM0, hM⟩ := exists_smooth_unit_cutoff n
  have hχ0 : χ 0 = 1 := hinner 0 (by simp)
  have heq (k : ℕ) : (∫ x, (r x * x j) * cutoffSequence χ k x ∂ν) =
      (∫ x : EuclideanSpace ℝ (Fin n), (x i * x j) * cutoffSequence χ k x ∂ν) -
        ∫ x, partialTest n i (coordinateCutoff n j χ k) x ∂ν := by
    simpa only [coordinateCutoff_apply, ← mul_assoc] using hweak (coordinateCutoff n j χ k)
  have hleft := sobolevFisher_cutoff_integral_tendsto n ν (fun x => r x * x j)
    hrx χ hχ0 hχ
  have hright := (sobolevFisher_cutoff_integral_tendsto n ν (fun x => x i * x j)
    hxx χ hχ0 hχ).sub
    (weakRelativeScore_coordinateCutoff_derivative_integral_tendsto n i j ν χ hχ0 hχ houter M hM0 hM)
  have hleft' : Tendsto (fun k =>
      (∫ x : EuclideanSpace ℝ (Fin n), (x i * x j) * cutoffSequence χ k x ∂ν) -
        ∫ x, partialTest n i (coordinateCutoff n j χ k) x ∂ν) atTop
      (𝓝 (∫ x, r x * x j ∂ν)) := by
    simpa only [heq] using hleft
  exact tendsto_nhds_unique hleft' hright

theorem weakRelativeScore_moments (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (hxi : ∀ i : Fin n, MemLp (fun x : EuclideanSpace ℝ (Fin n) => x i) 2 ν)
    (r : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (hr : MemLp r 2 ν)
    (hweak : ∀ F : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), EuclideanSpace ℝ (Fin n)),
      (∫ x, ⟪r x, F x⟫ ∂ν) = ∫ x, ⟪x, F x⟫ - vectorDivergence n F x ∂ν) :
    (∀ i : Fin n, Integrable (fun x => r x i) ν ∧
      Integrable (fun x : EuclideanSpace ℝ (Fin n) => x i) ν ∧
      (∫ x, r x i ∂ν) = ∫ x : EuclideanSpace ℝ (Fin n), x i ∂ν) ∧
    (∀ i j : Fin n, Integrable (fun x => r x i * x j) ν ∧
      Integrable (fun x : EuclideanSpace ℝ (Fin n) => x i * x j) ν ∧
      (∫ x, r x i * x j ∂ν) = (∫ x : EuclideanSpace ℝ (Fin n), x i * x j ∂ν) -
        (if i = j then (1 : ℝ) else 0)) := by
  have hcomp (i : Fin n) (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ)) :=
    (firstOrder_source_component_identity n ν hxi r hr hweak i φ).2.2.2
  refine ⟨fun i => ⟨(hr.eval_piLp i).integrable (by norm_num),
    (hxi i).integrable (by norm_num), ?_⟩, ?_⟩
  · exact weakRelativeScore_component_mean n ν i (fun x => r x i) (hr.eval_piLp i) (hxi i) (hcomp i)
  · intro i j
    exact weakRelativeScore_component_cross_moment n ν i j (fun x => r x i)
      (hr.eval_piLp i) (hxi i) (hxi j) (hcomp i)

theorem weakRelativeScore_isotropic_moments (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (hxi : ∀ i : Fin n, MemLp (fun x : EuclideanSpace ℝ (Fin n) => x i) 2 ν)
    (hmean : ∀ i : Fin n, (∫ x : EuclideanSpace ℝ (Fin n), x i ∂ν) = 0)
    (hsecond : ∀ i j : Fin n,
      (∫ x : EuclideanSpace ℝ (Fin n), x i * x j ∂ν) = if i = j then (1 : ℝ) else 0)
    (r : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (hr : MemLp r 2 ν)
    (hweak : ∀ F : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), EuclideanSpace ℝ (Fin n)),
      (∫ x, ⟪r x, F x⟫ ∂ν) = ∫ x, ⟪x, F x⟫ - vectorDivergence n F x ∂ν) :
    (∀ i : Fin n, (∫ x, r x i ∂ν) = 0) ∧
      ∀ i j : Fin n, (∫ x, r x i * x j ∂ν) = 0 := by
  have h := weakRelativeScore_moments n ν hxi r hr hweak
  refine ⟨fun i => (h.1 i).2.2.trans (hmean i), fun i j => ?_⟩
  rw [(h.2 i j).2.2, hsecond, sub_self]

end AffineFKProof
