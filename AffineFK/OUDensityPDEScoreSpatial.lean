module

public import AffineFK.OUDensityPDEMixed
public import AffineFK.OUDensityPDEScore
public import AffineFK.GaussianSmoothedScoreHessianSymmetry

/-!
# Actual temporal score derivatives in spatial Fokker--Planck form

The ordinary score time derivative is the gradient of (L*rho)/rho,
where L*rho is the proved actual spatial density operator. Mixed
derivatives, positivity and the quotient rule are all proved before the
substitution. The Fisher-density statement is pointwise, with no global
space/time integral interchange or dissipation premise.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory TopologicalSpace
open scoped ContDiff RealInnerProductSpace

theorem ouDensitySpatialOperator_smooth (n : ℕ)
    (ρ : EuclideanSpace ℝ (Fin n) → ℝ) (hρ : ContDiff ℝ ∞ ρ) :
    ContDiff ℝ ∞ (ouDensitySpatialOperator n ρ) := by
  apply ContDiff.sum
  intro i _
  have hdi : ContDiff ℝ ∞ (fun x => fderiv ℝ ρ x (EuclideanSpace.basisFun (Fin n) ℝ i)) :=
    (hρ.fderiv_right (by simp)).clm_apply contDiff_const
  have hprod : ContDiff ℝ ∞ (fun x => x i * ρ x) := by
    simpa only [Pi.mul_apply, coordinateFunctional_apply] using (coordinateFunctional n i).contDiff.mul hρ
  exact ((hdi.fderiv_right (by simp)).clm_apply contDiff_const).add
    ((hprod.fderiv_right (by simp)).clm_apply contDiff_const)

theorem gradient_quotient_coordinate (n : ℕ)
    (f g : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hgpos : ∀ x, 0 < g x) (x : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    gradient (fun y => f y / g y) x i =
      (fderiv ℝ f x (EuclideanSpace.basisFun (Fin n) ℝ i) * g x -
        f x * fderiv ℝ g x (EuclideanSpace.basisFun (Fin n) ℝ i)) / (g x) ^ 2 := by
  have hdf := ((hf.differentiable (by simp)).differentiableAt (x := x)).hasFDerivAt
  have hdg := ((hg.differentiable (by simp)).differentiableAt (x := x)).hasFDerivAt
  have hi := (hasFDerivAt_inv (hgpos x).ne').comp x hdg
  have hp := hdf.mul hi
  have hfd := hp.fderiv
  change fderiv ℝ (fun y => f y * (g y)⁻¹) x = _ at hfd
  rw [gradient_coordinate_eq_fderiv]
  have heq : (fun y => f y / g y) = fun y => f y * (g y)⁻¹ := funext fun _ => div_eq_mul_inv _ _
  rw [heq, hfd]
  simp only [add_apply, smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul, Function.comp_apply]
  field_simp [(hgpos x).ne']
  ring

theorem ou_ordinary_score_time_derivative_eq_gradient (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (hU : Integrable (fun u : EuclideanSpace ℝ (Fin n) => u) ν)
    (t : ℝ) (ht : 0 < t) (x : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    let ρ := gaussianSmoothingDensity n ν (Real.exp (-t)) (Real.sqrt (1 - Real.exp (-2 * t)))
    ouOrdinaryScoreTimeDerivative n ν t x i =
      gradient (fun y => ouDensitySpatialOperator n ρ y / ρ y) x i := by
  let ρ := gaussianSmoothingDensity n ν (Real.exp (-t)) (Real.sqrt (1 - Real.exp (-2 * t)))
  have hρ := gaussianSmoothingDensity_smooth n ν (Real.exp (-t)) (Real.sqrt (1 - Real.exp (-2 * t)))
  have hpos := gaussianSmoothingDensity_pos n ν (Real.exp (-t)) (Real.sqrt (1 - Real.exp (-2 * t)))
    (ou_smoothing_scale_domain t ht).2.1
  change ouOrdinaryScoreTimeDerivative n ν t x i =
    gradient (fun y => ouDensitySpatialOperator n ρ y / ρ y) x i
  rw [gradient_quotient_coordinate n _ ρ (ouDensitySpatialOperator_smooth n ρ hρ) hρ hpos]
  dsimp only [ouOrdinaryScoreTimeDerivative]
  rw [ou_density_gradient_time_derivative_eq_spatial_derivative n ν hU t ht x,
    ou_density_time_derivative_eq_spatial_operator n ν hU t ht x]
  dsimp only [ρ]
  ring

theorem ou_ordinary_score_coordinate_hasDerivAt_spatial_operator (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (hU : Integrable (fun u : EuclideanSpace ℝ (Fin n) => u) ν)
    (t : ℝ) (ht : 0 < t) (x : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    let ρ := gaussianSmoothingDensity n ν (Real.exp (-t)) (Real.sqrt (1 - Real.exp (-2 * t)))
    HasDerivAt (fun s : ℝ => gradient (fun y => Real.log
      (gaussianSmoothingDensity n ν (Real.exp (-s)) (Real.sqrt (1 - Real.exp (-2 * s))) y)) x i)
      (gradient (fun y => ouDensitySpatialOperator n ρ y / ρ y) x i) t := by
  dsimp only
  rw [← ou_ordinary_score_time_derivative_eq_gradient n ν hU t ht x i]
  exact ou_ordinary_score_coordinate_hasDerivAt n ν hU t ht x i

theorem ou_ordinary_fisher_density_hasDerivAt_spatial_operator (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (hU : Integrable (fun u : EuclideanSpace ℝ (Fin n) => u) ν)
    (t : ℝ) (ht : 0 < t) (x : EuclideanSpace ℝ (Fin n)) :
    let ρ : ℝ → EuclideanSpace ℝ (Fin n) → ℝ := fun s =>
      gaussianSmoothingDensity n ν (Real.exp (-s)) (Real.sqrt (1 - Real.exp (-2 * s)))
    let score : ℝ → EuclideanSpace ℝ (Fin n) := fun s => gradient (fun y => Real.log (ρ s y)) x
    HasDerivAt (fun s : ℝ => ‖score s‖ ^ 2 * ρ s x)
      (2 * (∑ i : Fin n, score t i * gradient
        (fun y => ouDensitySpatialOperator n (ρ t) y / ρ t y) x i) * ρ t x +
        ‖score t‖ ^ 2 * ouDensitySpatialOperator n (ρ t) x) t := by
  have h := ou_ordinary_fisher_density_hasDerivAt n ν hU t ht x
  simp_rw [ou_ordinary_score_time_derivative_eq_gradient n ν hU t ht x,
    ou_density_time_derivative_eq_spatial_operator n ν hU t ht x] at h
  exact h

end AffineFKProof
