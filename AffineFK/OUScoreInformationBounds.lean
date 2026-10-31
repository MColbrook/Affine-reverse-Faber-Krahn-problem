module

public import AffineFK.SmoothedRelativeScoreBound
public import AffineFK.FirstOrderOUContraction

/-!
# The two information bounds for the actual OU relative score

Both bounds concern the gradient of the logarithm of the positive smooth
density ratio of the actual smoothed law. The original hypotheses are
genuine weak score and second-order Stein identities. The first bound is
also specialised below to the logarithmic score of a positive smooth
initial Lebesgue density with finite relative information.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory TopologicalSpace
open scoped Distributions RealInnerProductSpace ContDiff

theorem OU_firstOrder_relative_score_information_bound (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (hxi : ∀ i : Fin n, MemLp (fun x : EuclideanSpace ℝ (Fin n) => x i) 2 ν)
    (s : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (hs : MemLp s 2 ν)
    (hweak : ∀ F : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), EuclideanSpace ℝ (Fin n)),
      (∫ x, ⟪s x, F x⟫ ∂ν) = ∫ x, ⟪x, F x⟫ - vectorDivergence n F x ∂ν)
    (t : ℝ) (ht : 0 < t) :
    MemLp (gaussianSmoothingScore n ν (Real.exp (-t)) (Real.sqrt (1 - Real.exp (-2 * t)))) 2
      ((ν.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))).map
        (fun p => Real.exp (-t) • p.1 + Real.sqrt (1 - Real.exp (-2 * t)) • p.2)) ∧
    (∫ x, ‖gaussianSmoothingScore n ν (Real.exp (-t))
      (Real.sqrt (1 - Real.exp (-2 * t))) x‖ ^ 2
      ∂(ν.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))).map
        (fun p => Real.exp (-t) • p.1 + Real.sqrt (1 - Real.exp (-2 * t)) • p.2)) ≤
      Real.exp (-2 * t) * (∫ u, ‖s u‖ ^ 2 ∂ν) := by
  obtain ⟨r, _, hr, _, hbound, hweakr⟩ :=
    firstOrder_OU_conditional_vector_field n ν hxi s hs hweak t ht
  obtain ⟨_, hscore, henergy⟩ := gaussianSmoothingScore_identified_by_weak_identity n ν
    (Real.exp (-t)) (Real.sqrt (1 - Real.exp (-2 * t)))
    (ou_smoothing_scale_domain t ht).2.1 r hr (fun F => (hweakr F).2.2)
  exact ⟨hscore, henergy.trans_le hbound⟩

theorem OU_relative_score_information_bounds (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (hxi : ∀ i : Fin n, MemLp (fun x : EuclideanSpace ℝ (Fin n) => x i) 2 ν)
    (s : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (hs : MemLp s 2 ν)
    (hweak : ∀ F : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), EuclideanSpace ℝ (Fin n)),
      (∫ x, ⟪s x, F x⟫ ∂ν) = ∫ x, ⟪x, F x⟫ - vectorDivergence n F x ∂ν)
    (T : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n × Fin n × Fin n))
    (hT : MemLp T 2 ν)
    (hidentity : ∀ F : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), EuclideanSpace ℝ (Fin n)),
      (∫ x, ⟪x, F x⟫ - vectorDivergence n F x ∂ν) =
        ∫ x, vectorHessianContraction n T F x ∂ν)
    (t : ℝ) (ht : 0 < t) :
    MemLp (gaussianSmoothingScore n ν (Real.exp (-t)) (Real.sqrt (1 - Real.exp (-2 * t)))) 2
      ((ν.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))).map
        (fun p => Real.exp (-t) • p.1 + Real.sqrt (1 - Real.exp (-2 * t)) • p.2)) ∧
    (∫ x, ‖gaussianSmoothingScore n ν (Real.exp (-t))
      (Real.sqrt (1 - Real.exp (-2 * t))) x‖ ^ 2
      ∂(ν.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))).map
        (fun p => Real.exp (-t) • p.1 + Real.sqrt (1 - Real.exp (-2 * t)) • p.2)) ≤
      min (Real.exp (-2 * t) * (∫ u, ‖s u‖ ^ 2 ∂ν))
        ((2 * Real.exp (-6 * t) / (1 - Real.exp (-2 * t)) ^ 2) *
          (∫ u, ‖T u‖ ^ 2 ∂ν)) := by
  have hfirst := OU_firstOrder_relative_score_information_bound n ν hxi s hs hweak t ht
  have hsecond := OU_stein_relative_score_information_bound n ν hxi T hT hidentity t ht
  exact ⟨hfirst.1, le_min hfirst.2 hsecond.2⟩

theorem OU_smooth_initial_relative_score_information_bounds (n : ℕ)
    (ρ : EuclideanSpace ℝ (Fin n) → ℝ) (hρ : ContDiff ℝ ∞ ρ)
    (hρpos : ∀ x, 0 < ρ x) [IsProbabilityMeasure (densityMeasure n ρ)]
    (hxi : ∀ i : Fin n, MemLp (fun x : EuclideanSpace ℝ (Fin n) => x i) 2 (densityMeasure n ρ))
    (hscore : MemLp (fun x => gradient (fun y => Real.log (ρ y / standardGaussianDensity n y)) x)
      2 (densityMeasure n ρ))
    (T : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n × Fin n × Fin n))
    (hT : MemLp T 2 (densityMeasure n ρ))
    (hidentity : ∀ F : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), EuclideanSpace ℝ (Fin n)),
      (∫ x, ⟪x, F x⟫ - vectorDivergence n F x ∂densityMeasure n ρ) =
        ∫ x, vectorHessianContraction n T F x ∂densityMeasure n ρ)
    (t : ℝ) (ht : 0 < t) :
    MemLp (gaussianSmoothingScore n (densityMeasure n ρ) (Real.exp (-t))
      (Real.sqrt (1 - Real.exp (-2 * t)))) 2
      (((densityMeasure n ρ).prod (stdGaussian (EuclideanSpace ℝ (Fin n)))).map
        (fun p => Real.exp (-t) • p.1 + Real.sqrt (1 - Real.exp (-2 * t)) • p.2)) ∧
    (∫ x, ‖gaussianSmoothingScore n (densityMeasure n ρ) (Real.exp (-t))
      (Real.sqrt (1 - Real.exp (-2 * t))) x‖ ^ 2
      ∂((densityMeasure n ρ).prod (stdGaussian (EuclideanSpace ℝ (Fin n)))).map
        (fun p => Real.exp (-t) • p.1 + Real.sqrt (1 - Real.exp (-2 * t)) • p.2)) ≤
      min (Real.exp (-2 * t) *
        (∫ u, ‖gradient (fun y => Real.log (ρ y / standardGaussianDensity n y)) u‖ ^ 2
          ∂densityMeasure n ρ))
        ((2 * Real.exp (-6 * t) / (1 - Real.exp (-2 * t)) ^ 2) *
          (∫ u, ‖T u‖ ^ 2 ∂densityMeasure n ρ)) := by
  simp_rw [gradient_log_gaussian_relative_density n ρ hρ hρpos] at hscore ⊢
  exact (OU_relative_score_information_bounds n (densityMeasure n ρ) hxi
    (gaussianRelativeScore n ρ) hscore
    (fun F => (gaussianRelativeScore_vector_pairing n ρ hρ hρpos F).2.2)
    T hT hidentity t ht)

end AffineFKProof
