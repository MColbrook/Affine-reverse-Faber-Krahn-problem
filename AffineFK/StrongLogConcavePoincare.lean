module

public import AffineFK.BrascampLiebPoincare
public import AffineFK.StrongLogConcavePoincareCalculus
public import AffineFK.LogConcaveDensityLog
public import AffineFK.WeightedTestIntegration

/-!
# Poincare bound for smooth strongly log-concave probability densities

The input is the genuine log-concavity of rho times exp(norm squared/2),
not the desired Hessian or variance inequality. Its logarithm gives an
actual strongly convex potential. The global Brascamp--Lieb theorem and
the proved inverse-Hessian bound then give the least Poincare constant.

This file concerns globally positive smooth densities only. A density
supported on a convex body still requires a genuine limiting theorem.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory TopologicalSpace
open scoped ENNReal ContDiff RealInnerProductSpace

theorem strongLogConcave_smooth_potential_poincareConstant_le_one (n : ℕ)
    (W : EuclideanSpace ℝ (Fin n) → ℝ) (hW : ContDiff ℝ ∞ W)
    (hWi : Integrable (fun x => Real.exp (-W x)))
    (hMass : (∫ x, Real.exp (-W x)) = 1)
    (hconv : ConvexOn ℝ Set.univ (fun x => W x - (1 / 2 : ℝ) * ‖x‖ ^ 2)) :
    poincareConstant n (densityMeasure n (fun x => Real.exp (-W x))) ≤ 1 :=
  brascampLieb_unit_curvature_poincareConstant_le_one n W hW hWi hMass
    (strongLogConcave_convex_potential_hessian n W hW hconv)

theorem strongLogConcave_smooth_density_poincareConstant_le_one (n : ℕ)
    (ρ : EuclideanSpace ℝ (Fin n) → ℝ) (hρ : ContDiff ℝ ∞ ρ)
    (hpos : ∀ x, 0 < ρ x) (hi : Integrable ρ) (hMass : (∫ x, ρ x) = 1)
    (hlc : LogConcaveDensity (fun x => ENNReal.ofReal
      (ρ x * Real.exp ((1 / 2 : ℝ) * ‖x‖ ^ 2)))) :
    poincareConstant n (densityMeasure n ρ) ≤ 1 := by
  let W : EuclideanSpace ℝ (Fin n) → ℝ := fun x => -Real.log (ρ x)
  have hW : ContDiff ℝ ∞ W := (hρ.log (fun x => (hpos x).ne')).neg
  have he : (fun x => Real.exp (-W x)) = ρ := by
    funext x
    simp only [W, neg_neg, Real.exp_log (hpos x)]
  have hWi : Integrable (fun x => Real.exp (-W x)) := by rw [he]; exact hi
  have hmass : (∫ x, Real.exp (-W x)) = 1 := by rw [he]; exact hMass
  have hconc := logConcaveDensity_concaveOn_log
    (fun x => ρ x * Real.exp ((1 / 2 : ℝ) * ‖x‖ ^ 2))
    (fun x => mul_pos (hpos x) (Real.exp_pos _)) hlc
  have hconv : ConvexOn ℝ Set.univ (fun x => W x - (1 / 2 : ℝ) * ‖x‖ ^ 2) := by
    apply hconc.neg.congr
    intro x _
    dsimp [W]
    rw [Real.log_mul (hpos x).ne' (Real.exp_pos _).ne', Real.log_exp]
    ring
  have h := strongLogConcave_smooth_potential_poincareConstant_le_one n W hW hWi hmass hconv
  rwa [he] at h

theorem strongLogConcave_smooth_probability_poincareConstant_le_one (n : ℕ)
    (ρ : EuclideanSpace ℝ (Fin n) → ℝ) (hρ : ContDiff ℝ ∞ ρ)
    (hpos : ∀ x, 0 < ρ x) [IsProbabilityMeasure (densityMeasure n ρ)]
    (hlc : LogConcaveDensity (fun x => ENNReal.ofReal
      (ρ x * Real.exp ((1 / 2 : ℝ) * ‖x‖ ^ 2)))) :
    poincareConstant n (densityMeasure n ρ) ≤ 1 := by
  have hmass : (∫⁻ x, ENNReal.ofReal (ρ x) ∂volume) = 1 := by
    have h := measure_univ (μ := densityMeasure n ρ)
    simpa only [densityMeasure, withDensity_apply _ MeasurableSet.univ,
      setLIntegral_univ] using h
  have hi : Integrable ρ (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    (lintegral_ofReal_ne_top_iff_integrable hρ.continuous.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => (hpos x).le)).mp
      (by rw [hmass]; exact ENNReal.one_ne_top)
  have hMass : (∫ x, ρ x) = 1 := by
    have h := density_integral_eq n ρ hρ.continuous (fun x => (hpos x).le) (fun _ => (1 : ℝ))
    simpa only [mul_one, integral_const, probReal_univ, smul_eq_mul, one_mul] using h.symm
  exact strongLogConcave_smooth_density_poincareConstant_le_one n ρ hρ hpos hi hMass hlc

end AffineFKProof
