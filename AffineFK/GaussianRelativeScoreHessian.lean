module

public import AffineFK.GaussianHessianL2
public import AffineFK.GaussianRelativeScore
public import AffineFK.VectorPoincareRegression

/-!
# The actual relative-score derivative after Gaussian smoothing

The relative score is the genuine ordinary logarithmic gradient plus x.
Its actual component gradient is the ordinary Hessian row plus the fixed
coordinate vector. Hessian L2 membership is supplied by the independently
constructed second-density-ratio proof, not assumed as a new premise.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory InnerProductSpace
open scoped ContDiff RealInnerProductSpace

theorem gaussianRelativeScore_smooth (n : ℕ)
    (ρ : EuclideanSpace ℝ (Fin n) → ℝ) (hρ : ContDiff ℝ ∞ ρ)
    (hρpos : ∀ x, 0 < ρ x) : ContDiff ℝ ∞ (gaussianRelativeScore n ρ) :=
  (logDensity_ordinaryScore_smooth n ρ hρ hρpos).add contDiff_id

theorem gaussianRelativeScore_component_gradient (n : ℕ)
    (ρ : EuclideanSpace ℝ (Fin n) → ℝ) (hρ : ContDiff ℝ ∞ ρ)
    (hρpos : ∀ x, 0 < ρ x) (i : Fin n) (x : EuclideanSpace ℝ (Fin n)) :
    gradient (fun y => gaussianRelativeScore n ρ y i) x =
      gradient (fun y => gradient (fun z => Real.log (ρ z)) y i) x +
        EuclideanSpace.basisFun (Fin n) ℝ i := by
  let f : EuclideanSpace ℝ (Fin n) → ℝ := fun y => gradient (fun z => Real.log (ρ z)) y i
  have hf : ContDiff ℝ ∞ f := by
    simpa only [Function.comp_def, coordinateFunctional_apply] using
      (coordinateFunctional n i).contDiff.comp (logDensity_ordinaryScore_smooth n ρ hρ hρpos)
  have heq : (fun y => gaussianRelativeScore n ρ y i) =
      fun y => f y + coordinateFunctional n i y := by
    funext y
    simp only [gaussianRelativeScore, PiLp.add_apply, coordinateFunctional_apply, f]
  rw [heq]
  have hd := ((hf.differentiable (by simp)).differentiableAt (x := x)).hasFDerivAt.add
    (coordinateFunctional n i).hasFDerivAt
  change (toDual ℝ (EuclideanSpace ℝ (Fin n))).symm
      (fderiv ℝ (fun y => f y + coordinateFunctional n i y) x) = _
  have hfun : (fun y => f y + coordinateFunctional n i y) =
      f + (coordinateFunctional n i : EuclideanSpace ℝ (Fin n) → ℝ) := rfl
  have hcoord : (toDual ℝ (EuclideanSpace ℝ (Fin n))).symm (coordinateFunctional n i) =
      EuclideanSpace.basisFun (Fin n) ℝ i := by
    simpa only [gradient, (coordinateFunctional n i).fderiv] using coordinateFunctional_gradient n i x
  rw [hfun, hd.fderiv, map_add, hcoord]
  rfl

theorem gaussianSmoothing_relativeScore_component_gradient_memLp (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (a b : ℝ) (hb : 0 < b) (i : Fin n) :
    MemLp (gradient (fun y => gaussianRelativeScore n (gaussianSmoothingDensity n ν a b) y i)) 2
      (densityMeasure n (gaussianSmoothingDensity n ν a b)) := by
  have : IsProbabilityMeasure (densityMeasure n (gaussianSmoothingDensity n ν a b)) := by
    rw [← gaussianSmoothingDensity_law n ν a b hb]
    infer_instance
  have heq := funext (gaussianRelativeScore_component_gradient n _
    (gaussianSmoothingDensity_smooth n ν a b) (gaussianSmoothingDensity_pos n ν a b hb) i)
  rw [heq]
  exact (gaussianSmoothing_logHessian_row_memLp n ν a b hb i).add (memLp_const _)

end AffineFKProof
