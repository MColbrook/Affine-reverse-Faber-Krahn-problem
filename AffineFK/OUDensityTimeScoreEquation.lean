module

public import AffineFK.GaussianEntropyCalculusWeakPDE
public import AffineFK.GaussianSmoothedScore

/-!
# The actual OU density derivative as score flux against compact tests

The score is the gradient of the logarithm of the positive smooth
Gaussian-relative density, not an arbitrary weak-field representative.
Its compact-test pairing is integrable without assuming global Fisher
information. The identity follows from proved density calculus and
spatial integration by parts; entropy cutoff limits remain separate.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory TopologicalSpace
open scoped Distributions RealInnerProductSpace

theorem ou_generator_stein_gradient (n : ℕ)
    (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ))
    (x : EuclideanSpace ℝ (Fin n)) :
    ⟪x, testFunctionGradient φ x⟫ - vectorDivergence n (testFunctionGradient φ) x =
      -ouTestGenerator n φ x := by
  rw [vector_stein_left_sum, ouTestGenerator_apply, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  change x i * partialTest n i φ x - partialTest n i (partialTest n i φ) x =
    -(partialTest n i (partialTest n i φ) x - x i * partialTest n i φ x)
  ring

theorem ou_density_time_derivative_score_flux (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (hU : Integrable (fun u : EuclideanSpace ℝ (Fin n) => u) ν)
    (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ)) (t : ℝ) (ht : 0 < t) :
    let ρ := gaussianSmoothingDensity n ν (Real.exp (-t)) (Real.sqrt (1 - Real.exp (-2 * t)))
    let score := gaussianSmoothingScore n ν (Real.exp (-t)) (Real.sqrt (1 - Real.exp (-2 * t)))
    Integrable (fun x => ⟪score x, gradient φ x⟫) (densityMeasure n ρ) ∧
    (∫ x : EuclideanSpace ℝ (Fin n), φ x * ouDensityTimeDerivative n ν t x) =
      -(∫ x, ⟪score x, gradient φ x⟫ ∂densityMeasure n ρ) := by
  let a := Real.exp (-t)
  let b := Real.sqrt (1 - Real.exp (-2 * t))
  have hb : 0 < b := (ou_smoothing_scale_domain t ht).2.1
  have hlaw := gaussianSmoothingDensity_law n ν a b hb
  letI : IsProbabilityMeasure (densityMeasure n (gaussianSmoothingDensity n ν a b)) := by
    rw [← hlaw]
    infer_instance
  have h := gaussianRelativeScore_vector_pairing n (gaussianSmoothingDensity n ν a b)
    (gaussianSmoothingDensity_smooth n ν a b) (gaussianSmoothingDensity_pos n ν a b hb)
    (testFunctionGradient φ)
  have heq : (∫ x, ⟪gaussianSmoothingScore n ν a b x, gradient φ x⟫
      ∂densityMeasure n (gaussianSmoothingDensity n ν a b)) =
      -(∫ x, ouTestGenerator n φ x ∂densityMeasure n (gaussianSmoothingDensity n ν a b)) := by
    rw [gaussianSmoothingScore_eq_density_score n ν a b hb]
    simp only [testFunctionGradient_apply] at h
    rw [h.2.2]
    simp_rw [← testFunctionGradient_apply φ, ou_generator_stein_gradient]
    exact integral_neg _
  refine ⟨?_, ?_⟩
  · rw [gaussianSmoothingScore_eq_density_score n ν a b hb]
    simpa only [testFunctionGradient_apply] using h.1
  · rw [ou_density_time_derivative_weak_pde n ν hU φ t ht, heq,
      ou_density_test_integral_eq n ν (ouTestGenerator n φ) t ht]
    ring

end AffineFKProof
