module

public import AffineFK.GroundstateGaussianFisherBound

/-!
# Ground-state bounds depend on the law, not a selected Lp representative

A pointwise strongly log-concave density representing the law transfers
the actual Poincare bound. It need not be the arbitrary Lp-based density
used to define the canonical numerical Fisher information. The resulting
moment and Fisher bounds concern the same actual probability measure.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory TopologicalSpace
open scoped ENNReal NNReal

theorem strongLogConcave_representative_poincare_bound (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (ρ : EuclideanSpace ℝ (Fin n) → ℝ) (hρ : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x)
    (hlaw : ν = densityMeasure n ρ)
    (hlc : LogConcaveDensity (fun x => ENNReal.ofReal
      (ρ x * Real.exp ((1 / 2 : ℝ) * ‖x‖ ^ 2)))) :
    poincareConstant n ν ≤ 1 := by
  letI : IsProbabilityMeasure (densityMeasure n ρ) := by rw [← hlaw]; infer_instance
  have h := strongLogConcave_density_poincareConstant_le_one n ρ hρ hρ0 hlc
  rwa [← hlaw] at h

theorem gaussianGroundstateDensity_fisher_bound_of_poincare (n : ℕ)
    (U : Opens (EuclideanSpace ℝ (Fin n))) (ell : ℝ) (ψ : dirichletSobolev n U)
    (hweak : IsDirichletWeakEigenfunction n U ell ψ) (hψ : ψ ≠ 0)
    (hψ0 : ∀ᵐ x ∂volume, 0 ≤ dirichletValue n U ψ x)
    [Measure.IsNegInvariant (densityMeasure n (gaussianGroundstateDensity n U ψ))]
    (hP : poincareConstant n (densityMeasure n (gaussianGroundstateDensity n U ψ)) ≤ 1) :
    (∫ x, ‖x‖ ^ 2 ∂densityMeasure n (gaussianGroundstateDensity n U ψ)) ≤ n ∧
    ordinaryFisherMeasure n (densityMeasure n (gaussianGroundstateDensity n U ψ)) ≠ ∞ ∧
    (ordinaryFisherMeasure n (densityMeasure n (gaussianGroundstateDensity n U ψ))).toReal ≤
      4 * ell + n ∧
    ordinaryFisherMeasure n (densityMeasure n (gaussianGroundstateDensity n U ψ)) ≤
      ENNReal.ofReal (4 * ell + n) := by
  have h := gaussianGroundstateDensity_fisher_real_identity n U ell ψ hweak hψ hψ0
  letI : IsProbabilityMeasure (densityMeasure n (gaussianGroundstateDensity n U ψ)) := h.1
  have hm := poincare_centered_second_moment_bound n
    (densityMeasure n (gaussianGroundstateDensity n U ψ)) h.2.1
    (even_measure_coordinate_mean_zero n _) 1 hP
  simp only [NNReal.coe_one, one_mul] at hm
  have hreal : (ordinaryFisherMeasure n (densityMeasure n (gaussianGroundstateDensity n U ψ))).toReal ≤
      4 * ell + n := by rw [h.2.2.2]; linarith only [hm]
  refine ⟨hm, h.2.2.1, hreal, ?_⟩
  calc
    _ = ENNReal.ofReal (ordinaryFisherMeasure n
        (densityMeasure n (gaussianGroundstateDensity n U ψ))).toReal :=
      (ENNReal.ofReal_toReal h.2.2.1).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal hreal

theorem gaussianGroundstateDensity_fisher_bound_of_representative (n : ℕ)
    (U : Opens (EuclideanSpace ℝ (Fin n))) (ell : ℝ) (ψ : dirichletSobolev n U)
    (hweak : IsDirichletWeakEigenfunction n U ell ψ) (hψ : ψ ≠ 0)
    (hψ0 : ∀ᵐ x ∂volume, 0 ≤ dirichletValue n U ψ x)
    [Measure.IsNegInvariant (densityMeasure n (gaussianGroundstateDensity n U ψ))]
    (ρ : EuclideanSpace ℝ (Fin n) → ℝ) (hρ : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x)
    (hlaw : densityMeasure n (gaussianGroundstateDensity n U ψ) = densityMeasure n ρ)
    (hlc : LogConcaveDensity (fun x => ENNReal.ofReal
      (ρ x * Real.exp ((1 / 2 : ℝ) * ‖x‖ ^ 2)))) :
    poincareConstant n (densityMeasure n (gaussianGroundstateDensity n U ψ)) ≤ 1 ∧
    (∫ x, ‖x‖ ^ 2 ∂densityMeasure n (gaussianGroundstateDensity n U ψ)) ≤ n ∧
    ordinaryFisherMeasure n (densityMeasure n (gaussianGroundstateDensity n U ψ)) ≠ ∞ ∧
    (ordinaryFisherMeasure n (densityMeasure n (gaussianGroundstateDensity n U ψ))).toReal ≤
      4 * ell + n := by
  letI : IsProbabilityMeasure (densityMeasure n (gaussianGroundstateDensity n U ψ)) :=
    gaussianGroundstateDensity_probability n U ψ hψ
  have hP := strongLogConcave_representative_poincare_bound n _ ρ hρ hρ0 hlaw hlc
  have h := gaussianGroundstateDensity_fisher_bound_of_poincare n U ell ψ hweak hψ hψ0 hP
  exact ⟨hP, h.1, h.2.1, h.2.2.1⟩

end AffineFKProof
