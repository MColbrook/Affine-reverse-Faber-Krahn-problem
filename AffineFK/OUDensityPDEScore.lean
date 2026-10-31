module

public import AffineFK.OUDensityPDEGradient
public import AffineFK.OUDensityPDE
public import AffineFK.LogDensityIntegration
public import Mathlib.Analysis.Calculus.Deriv.Add

/-!
# Genuine positive-time derivatives of the ordinary OU score

The quotient rule is applied to the actual density and actual spatial
density derivative, whose ordinary time derivatives were proved from
the Gaussian kernel. The final statement differentiates the pointwise
Fisher density only. It makes no interchange with a global space integral.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory Filter
open scoped Topology RealInnerProductSpace

def ouOrdinaryScoreTimeDerivative (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) (t : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) (i : Fin n) : ℝ :=
  let ρ := gaussianSmoothingDensity n ν (Real.exp (-t)) (Real.sqrt (1 - Real.exp (-2 * t)))
  ((ouDensityGradientTimeDerivative n ν t x) (EuclideanSpace.basisFun (Fin n) ℝ i) * ρ x -
    fderiv ℝ ρ x (EuclideanSpace.basisFun (Fin n) ℝ i) * ouDensityTimeDerivative n ν t x) / (ρ x) ^ 2

theorem ou_ordinary_score_coordinate_hasDerivAt (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (hU : Integrable (fun u : EuclideanSpace ℝ (Fin n) => u) ν)
    (t : ℝ) (ht : 0 < t) (x : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    HasDerivAt (fun s : ℝ => gradient (fun y => Real.log
      (gaussianSmoothingDensity n ν (Real.exp (-s)) (Real.sqrt (1 - Real.exp (-2 * s))) y)) x i)
      (ouOrdinaryScoreTimeDerivative n ν t x i) t := by
  let ρ : ℝ → EuclideanSpace ℝ (Fin n) → ℝ := fun s =>
    gaussianSmoothingDensity n ν (Real.exp (-s)) (Real.sqrt (1 - Real.exp (-2 * s)))
  have hρt := ou_density_time_derivative_hasDerivAt n ν hU x t ht
  have hDt := ou_density_fderiv_hasDerivAt n ν hU t ht x
  have hcoord := (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.basisFun (Fin n) ℝ i)).hasFDerivAt.comp_hasDerivAt t hDt
  have hpos : 0 < ρ t x := gaussianSmoothingDensity_pos n ν _ _ (ou_smoothing_scale_domain t ht).2.1 x
  have hdiv := hcoord.div hρt hpos.ne'
  change HasDerivAt (fun s : ℝ => fderiv ℝ (ρ s) x (EuclideanSpace.basisFun (Fin n) ℝ i) / ρ s x)
    (ouOrdinaryScoreTimeDerivative n ν t x i) t at hdiv
  apply hdiv.congr_of_eventuallyEq
  filter_upwards [lt_mem_nhds ht] with s hs
  rw [log_density_gradient_coordinate n (ρ s) (gaussianSmoothingDensity_smooth n ν _ _)
    (gaussianSmoothingDensity_pos n ν _ _ (ou_smoothing_scale_domain s hs).2.1) x i]
  exact mul_comm _ _

theorem ou_ordinary_fisher_density_hasDerivAt (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (hU : Integrable (fun u : EuclideanSpace ℝ (Fin n) => u) ν)
    (t : ℝ) (ht : 0 < t) (x : EuclideanSpace ℝ (Fin n)) :
    let ρ : ℝ → EuclideanSpace ℝ (Fin n) → ℝ := fun s =>
      gaussianSmoothingDensity n ν (Real.exp (-s)) (Real.sqrt (1 - Real.exp (-2 * s)))
    let score : ℝ → EuclideanSpace ℝ (Fin n) := fun s => gradient (fun y => Real.log (ρ s y)) x
    HasDerivAt (fun s : ℝ => ‖score s‖ ^ 2 * ρ s x)
      (2 * (∑ i : Fin n, score t i * ouOrdinaryScoreTimeDerivative n ν t x i) * ρ t x +
        ‖score t‖ ^ 2 * ouDensityTimeDerivative n ν t x) t := by
  let ρ : ℝ → EuclideanSpace ℝ (Fin n) → ℝ := fun s =>
    gaussianSmoothingDensity n ν (Real.exp (-s)) (Real.sqrt (1 - Real.exp (-2 * s)))
  let score : ℝ → EuclideanSpace ℝ (Fin n) := fun s => gradient (fun y => Real.log (ρ s y)) x
  have hs (i : Fin n) := ou_ordinary_score_coordinate_hasDerivAt n ν hU t ht x i
  have hsum := HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => (hs i).pow 2)
  have heq : (fun s : ℝ => ‖score s‖ ^ 2) = fun s : ℝ => ∑ i : Fin n, (score s i) ^ 2 :=
    funext fun s => EuclideanSpace.real_norm_sq_eq (score s)
  have hnorm : HasDerivAt (fun s : ℝ => ‖score s‖ ^ 2)
      (2 * ∑ i : Fin n, score t i * ouOrdinaryScoreTimeDerivative n ν t x i) t := by
    rw [heq]
    convert hsum using 1
    simp only [Nat.cast_ofNat, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hp := hnorm.mul (ou_density_time_derivative_hasDerivAt n ν hU x t ht)
  convert hp using 1

end AffineFKProof
