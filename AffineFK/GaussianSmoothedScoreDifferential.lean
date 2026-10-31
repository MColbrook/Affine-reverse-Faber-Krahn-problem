module

public import AffineFK.GaussianSmoothingRegularity

/-!
# Smoothness of the actual logarithmic score and its derivative

The only density premises in the generic lemmas are genuine C-infinity
smoothness and strict positivity. Gaussian smoothing supplies both from
an arbitrary probability law. Derivatives are the actual Frechet
derivatives and the actual Euclidean gradient, not assumed score fields.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory TopologicalSpace InnerProductSpace
open scoped ContDiff RealInnerProductSpace

theorem contDiff_gradient_of_contDiff (n : ℕ)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (gradient f) := by
  change ContDiff ℝ ∞ (fun x =>
    (toDual ℝ (EuclideanSpace ℝ (Fin n))).symm (fderiv ℝ f x))
  exact (toDual ℝ (EuclideanSpace ℝ (Fin n))).symm.contDiff.comp
    (hf.fderiv_right (by simp))

theorem logDensity_ordinaryScore_smooth (n : ℕ)
    (ρ : EuclideanSpace ℝ (Fin n) → ℝ) (hρ : ContDiff ℝ ∞ ρ)
    (hρpos : ∀ x, 0 < ρ x) :
    ContDiff ℝ ∞ (gradient (fun x => Real.log (ρ x))) :=
  contDiff_gradient_of_contDiff n _ (hρ.log (fun x => (hρpos x).ne'))

theorem logDensity_ordinaryScore_derivative_smooth (n : ℕ)
    (ρ : EuclideanSpace ℝ (Fin n) → ℝ) (hρ : ContDiff ℝ ∞ ρ)
    (hρpos : ∀ x, 0 < ρ x) :
    ContDiff ℝ ∞ (fderiv ℝ (gradient (fun x => Real.log (ρ x)))) :=
  (logDensity_ordinaryScore_smooth n ρ hρ hρpos).fderiv_right (by simp)

theorem gaussianSmoothing_logDensity_smooth (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (a b : ℝ) (hb : 0 < b) :
    ContDiff ℝ ∞ (fun x => Real.log (gaussianSmoothingDensity n ν a b x)) :=
  (gaussianSmoothingDensity_smooth n ν a b).log
    (fun x => (gaussianSmoothingDensity_pos n ν a b hb x).ne')

theorem gaussianSmoothing_ordinaryScore_smooth (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (a b : ℝ) (hb : 0 < b) :
    ContDiff ℝ ∞ (gradient (fun x => Real.log (gaussianSmoothingDensity n ν a b x))) :=
  logDensity_ordinaryScore_smooth n _ (gaussianSmoothingDensity_smooth n ν a b)
    (gaussianSmoothingDensity_pos n ν a b hb)

theorem gaussianSmoothing_ordinaryScore_derivative_smooth (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (a b : ℝ) (hb : 0 < b) :
    ContDiff ℝ ∞ (fderiv ℝ
      (gradient (fun x => Real.log (gaussianSmoothingDensity n ν a b x)))) :=
  logDensity_ordinaryScore_derivative_smooth n _ (gaussianSmoothingDensity_smooth n ν a b)
    (gaussianSmoothingDensity_pos n ν a b hb)

end AffineFKProof
