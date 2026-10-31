module

public import AffineFK.PoincareCovarianceBound
public import AffineFK.StrongLogConcavePoincareLimit
public import AffineFK.GroundstateGaussianFisherInformation

/-!
# The dimension term in the Gaussian-weighted ground-state Fisher bound

Actual strong log-concavity supplies the Poincare inequality. Reflection
supplies zero means, and genuine linear tests give the second moment.
The eigenfunction's existence, positivity and log-concavity are separate
inputs still to be supplied by the ground-state construction.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory TopologicalSpace
open scoped ENNReal NNReal RealInnerProductSpace

theorem even_measure_coordinate_mean_zero (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [Measure.IsNegInvariant ν]
    (i : Fin n) : (∫ x : EuclideanSpace ℝ (Fin n), x i ∂ν) = 0 := by
  have h := integral_neg_eq_self (fun x : EuclideanSpace ℝ (Fin n) => x i) ν
  simp only [PiLp.neg_apply, integral_neg] at h
  linarith

theorem strongLogConcave_even_density_moment_bound (n : ℕ)
    (ρ : EuclideanSpace ℝ (Fin n) → ℝ) (hρ : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x)
    [IsProbabilityMeasure (densityMeasure n ρ)] [Measure.IsNegInvariant (densityMeasure n ρ)]
    (hsecond : Integrable (fun x : EuclideanSpace ℝ (Fin n) => ‖x‖ ^ 2) (densityMeasure n ρ))
    (hlc : LogConcaveDensity (fun x => ENNReal.ofReal (ρ x * Real.exp ((1 / 2 : ℝ) * ‖x‖ ^ 2)))) :
    poincareConstant n (densityMeasure n ρ) ≤ 1 ∧
    (∀ v : EuclideanSpace ℝ (Fin n),
      (∫ x, (⟪v, x⟫ - ∫ y, ⟪v, y⟫ ∂densityMeasure n ρ) ^ 2 ∂densityMeasure n ρ) ≤ ‖v‖ ^ 2) ∧
    (∫ x, ‖x‖ ^ 2 ∂densityMeasure n ρ) ≤ n := by
  have hP := strongLogConcave_density_poincareConstant_le_one n ρ hρ hρ0 hlc
  refine ⟨hP, ?_, ?_⟩
  · intro v
    simpa only [NNReal.coe_one, one_mul] using
      poincare_linear_variance_bound n (densityMeasure n ρ) hsecond 1 hP v
  · simpa only [NNReal.coe_one, one_mul] using
      poincare_centered_second_moment_bound n (densityMeasure n ρ) hsecond
        (even_measure_coordinate_mean_zero n _) 1 hP

theorem gaussianGroundstateDensity_fisher_bound_of_strongLogConcavity (n : ℕ)
    (U : Opens (EuclideanSpace ℝ (Fin n))) (ell : ℝ) (ψ : dirichletSobolev n U)
    (hweak : IsDirichletWeakEigenfunction n U ell ψ) (hψ : ψ ≠ 0)
    (hψ0 : ∀ᵐ x ∂volume, 0 ≤ dirichletValue n U ψ x)
    [Measure.IsNegInvariant (densityMeasure n (gaussianGroundstateDensity n U ψ))]
    (hlc : LogConcaveDensity (fun x => ENNReal.ofReal
      (gaussianGroundstateDensity n U ψ x * Real.exp ((1 / 2 : ℝ) * ‖x‖ ^ 2)))) :
    poincareConstant n (densityMeasure n (gaussianGroundstateDensity n U ψ)) ≤ 1 ∧
    (∫ x, ‖x‖ ^ 2 ∂densityMeasure n (gaussianGroundstateDensity n U ψ)) ≤ n ∧
    ordinaryFisherMeasure n (densityMeasure n (gaussianGroundstateDensity n U ψ)) ≠ ∞ ∧
    ordinaryFisherMeasure n (densityMeasure n (gaussianGroundstateDensity n U ψ)) ≤
      ENNReal.ofReal (4 * ell + n) := by
  have h := gaussianGroundstateDensity_fisher_identity n U ell ψ hweak hψ hψ0
  let : IsProbabilityMeasure (densityMeasure n (gaussianGroundstateDensity n U ψ)) := h.1
  have hm := strongLogConcave_even_density_moment_bound n (gaussianGroundstateDensity n U ψ)
    (gaussianGroundstateDensity_measurable n U ψ) (gaussianGroundstateDensity_nonneg n U ψ)
    h.2.1 hlc
  refine ⟨hm.1, hm.2.2, ?_, ?_⟩
  · rw [h.2.2]
    exact ENNReal.ofReal_ne_top
  · rw [h.2.2]
    exact ENNReal.ofReal_le_ofReal (by linarith [hm.2.2])

end AffineFKProof
