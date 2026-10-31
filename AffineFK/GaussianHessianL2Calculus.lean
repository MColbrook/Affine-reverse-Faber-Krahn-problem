module

public import AffineFK.GaussianSecondDensityRatioCalculus
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Data.Matrix.Basic
public import Mathlib.MeasureTheory.SpecificCodomains.WithLp

/-!
# The actual logarithmic Hessian and the second-density ratio

The entry (i,j) differentiates component i of the genuine logarithmic
gradient in coordinate j. The formula is proved by the Frechet inverse
and product rules, reused from Mathlib (Jeremy Avigad, Sebastien Gouezel
and Yury Kudryashov). No Hessian formula or Hessian integrability is a
premise.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory InnerProductSpace
open scoped RealInnerProductSpace ContDiff ENNReal

def densityLogHessian (n : ℕ) (ρ : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => gradient (fun y => gradient (fun z => Real.log (ρ z)) y i) x j

theorem densityLogHessian_eq_secondDensityRatio_sub_score_product (n : ℕ)
    (ρ : EuclideanSpace ℝ (Fin n) → ℝ) (hρ : ContDiff ℝ ∞ ρ)
    (hρpos : ∀ x, 0 < ρ x) (x : EuclideanSpace ℝ (Fin n)) (i j : Fin n) :
    densityLogHessian n ρ x i j = secondDensityRatio n ρ i j x -
      gradient (fun y => Real.log (ρ y)) x i * gradient (fun y => Real.log (ρ y)) x j := by
  let fi : EuclideanSpace ℝ (Fin n) → ℝ :=
    fun y => fderiv ℝ ρ y (EuclideanSpace.basisFun (Fin n) ℝ i)
  have hfi : ContDiff ℝ ∞ fi := (hρ.fderiv_right (by simp)).clm_apply contDiff_const
  have hdρ : HasFDerivAt ρ (fderiv ℝ ρ x) x :=
    ((hρ.differentiable (by simp)).differentiableAt (x := x)).hasFDerivAt
  have hdi : HasFDerivAt fi (fderiv ℝ fi x) x :=
    ((hfi.differentiable (by simp)).differentiableAt (x := x)).hasFDerivAt
  have hdInv := (hasFDerivAt_inv (hρpos x).ne').comp x hdρ
  have hdProd := hdInv.mul hdi
  have heq : (fun y => gradient (fun z => Real.log (ρ z)) y i) =
      fun y => (ρ y)⁻¹ * fi y := funext fun y => log_density_gradient_coordinate n ρ hρ hρpos y i
  have hentry : densityLogHessian n ρ x i j =
      fderiv ℝ (fun y => (ρ y)⁻¹ * fi y) x (EuclideanSpace.basisFun (Fin n) ℝ j) := by
    change gradient (fun y => gradient (fun z => Real.log (ρ z)) y i) x j = _
    calc
      _ = ⟪gradient (fun y => gradient (fun z => Real.log (ρ z)) y i) x,
          EuclideanSpace.basisFun (Fin n) ℝ j⟫ := by
        rw [real_inner_comm, EuclideanSpace.basisFun_inner]
      _ = _ := by rw [inner_gradient_left, heq]
  have hdf := hdProd.fderiv
  change fderiv ℝ (fun y => (ρ y)⁻¹ * fi y) x = _ at hdf
  rw [hentry, hdf]
  simp only [Function.comp_apply, add_apply, smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul]
  rw [log_density_gradient_coordinate n ρ hρ hρpos x i,
    log_density_gradient_coordinate n ρ hρ hρpos x j]
  dsimp only [secondDensityRatio, fi]
  field_simp [(hρpos x).ne']
  ring

theorem densityLogHessian_entry_memLp_of_secondRatio_and_score
    (n : ℕ) (ρ : EuclideanSpace ℝ (Fin n) → ℝ) (hρ : ContDiff ℝ ∞ ρ)
    (hρpos : ∀ x, 0 < ρ x) (μ : Measure (EuclideanSpace ℝ (Fin n)))
    (i j : Fin n) (hq : MemLp (secondDensityRatio n ρ i j) 2 μ)
    (hs : MemLp (gradient (fun x => Real.log (ρ x))) 4 μ) :
    MemLp (fun x => densityLogHessian n ρ x i j) 2 μ := by
  have : ENNReal.HolderTriple 4 4 2 := ⟨by
    rw [show (4 : ℝ≥0∞) = 2 * 2 by norm_num, ENNReal.mul_inv,
      ← mul_add, ENNReal.inv_two_add_inv_two, mul_one]
    all_goals norm_num⟩
  have hp : MemLp (fun x => gradient (fun y => Real.log (ρ y)) x i *
      gradient (fun y => Real.log (ρ y)) x j) 2 μ :=
    (hs.eval_piLp i).mul (hs.eval_piLp j)
  have heq : (fun x => densityLogHessian n ρ x i j) = fun x =>
      secondDensityRatio n ρ i j x - gradient (fun y => Real.log (ρ y)) x i *
        gradient (fun y => Real.log (ρ y)) x j :=
    funext fun x => densityLogHessian_eq_secondDensityRatio_sub_score_product n ρ hρ hρpos x i j
  rw [heq]
  exact hq.sub hp

end AffineFKProof
