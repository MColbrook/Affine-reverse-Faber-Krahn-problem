module

public import AffineFK.BridgeCoefficientL2
public import Mathlib.Probability.Independence.Integration

/-!
# Exact covariance and orthonormality of the actual scalar coefficients

Cross-level/position independence comes from the actual countable product
measure, and within-vector covariance is the actual standard Euclidean
Gaussian covariance. These are not assumptions on a surrogate sequence.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Pointwise BigOperators Topology RealInnerProductSpace

theorem bridgeGaussian_coordinate_mean (n : ℕ) (i : Fin n) :
    (∫ x : EuclideanSpace ℝ (Fin n), x i ∂stdGaussian (EuclideanSpace ℝ (Fin n))) = 0 := by
  simpa only [coordinateFunctional_apply] using integral_strongDual_stdGaussian (coordinateFunctional n i)

theorem bridgeGaussian_coordinate_cross_moment (n : ℕ) (i l : Fin n) :
    (∫ x : EuclideanSpace ℝ (Fin n), x i * x l ∂stdGaussian (EuclideanSpace ℝ (Fin n))) =
      if i = l then 1 else 0 := by
  have hG : MemLp (id : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) 2
      (stdGaussian (EuclideanSpace ℝ (Fin n))) := IsGaussian.hasGaussianLaw_id.memLp_two
  have hcov := (covarianceBilin_apply_eq_cov (μ := stdGaussian (EuclideanSpace ℝ (Fin n)))
    hG (EuclideanSpace.basisFun (Fin n) ℝ i)
      (EuclideanSpace.basisFun (Fin n) ℝ l)).symm
  rw [covarianceBilin_stdGaussian] at hcov
  simp only [EuclideanSpace.basisFun_inner, innerSL_apply_apply] at hcov
  have hi : MemLp (fun x : EuclideanSpace ℝ (Fin n) => x i) 2
      (stdGaussian (EuclideanSpace ℝ (Fin n))) := by simpa only [id_eq] using hG.eval_piLp i
  have hl : MemLp (fun x : EuclideanSpace ℝ (Fin n) => x l) 2
      (stdGaussian (EuclideanSpace ℝ (Fin n))) := by simpa only [id_eq] using hG.eval_piLp l
  rw [covariance_eq_sub hi hl, bridgeGaussian_coordinate_mean,
    bridgeGaussian_coordinate_mean, zero_mul, sub_zero] at hcov
  have hr : ((innerSL ℝ) (EuclideanSpace.basisFun (Fin n) ℝ i))
      (EuclideanSpace.basisFun (Fin n) ℝ l) = if i = l then 1 else 0 := by
    change ⟪EuclideanSpace.basisFun (Fin n) ℝ i, EuclideanSpace.basisFun (Fin n) ℝ l⟫ = _
    exact (orthonormal_iff_ite.mp (EuclideanSpace.basisFun (Fin n) ℝ).orthonormal) i l
  rw [hr] at hcov
  exact hcov

theorem bridgeScalarCoefficient_mean (n j : ℕ) (k : Fin (2 ^ j)) (i : Fin n) :
    (∫ ω, ω j k i ∂bridgeCoefficientMeasure n) = 0 := by
  calc
    _ = ∫ x : EuclideanSpace ℝ (Fin n), x i ∂stdGaussian (EuclideanSpace ℝ (Fin n)) :=
      (bridgeCoefficientMeasure_hasLaw n j k).integral_comp
        (f := fun x : EuclideanSpace ℝ (Fin n) => x i) (by fun_prop)
    _ = 0 := bridgeGaussian_coordinate_mean n i

theorem bridgeScalarCoefficientL2_mean (n j : ℕ) (k : Fin (2 ^ j)) (i : Fin n) :
    (∫ ω, bridgeScalarCoefficientL2 n j k i ω ∂bridgeCoefficientMeasure n) = 0 := by
  rw [integral_congr_ae (bridgeScalarCoefficientL2_coe n j k i)]
  exact bridgeScalarCoefficient_mean n j k i

theorem bridgeScalarCoefficientL2_inner (n : ℕ)
    (s t : Σ j : ℕ, Fin (2 ^ j)) (i l : Fin n) :
    ⟪bridgeScalarCoefficientL2 n s.1 s.2 i, bridgeScalarCoefficientL2 n t.1 t.2 l⟫ =
      if s = t then (if i = l then 1 else 0) else 0 := by
  classical
  rw [L2.inner_def]
  have heq : (∫ ω, ⟪bridgeScalarCoefficientL2 n s.1 s.2 i ω,
      bridgeScalarCoefficientL2 n t.1 t.2 l ω⟫ ∂bridgeCoefficientMeasure n) =
        ∫ ω, ω s.1 s.2 i * ω t.1 t.2 l ∂bridgeCoefficientMeasure n := by
    apply integral_congr_ae
    filter_upwards [bridgeScalarCoefficientL2_coe n s.1 s.2 i,
      bridgeScalarCoefficientL2_coe n t.1 t.2 l] with ω hs ht
    simp [hs, ht, mul_comm]
  rw [heq]
  by_cases hst : s = t
  · subst t
    rw [if_pos rfl]
    calc
      _ = ∫ x : EuclideanSpace ℝ (Fin n), x i * x l
          ∂stdGaussian (EuclideanSpace ℝ (Fin n)) :=
        (bridgeCoefficientMeasure_hasLaw n s.1 s.2).integral_comp
          (f := fun x : EuclideanSpace ℝ (Fin n) => x i * x l) (by fun_prop)
      _ = _ := bridgeGaussian_coordinate_cross_moment n i l
  · rw [if_neg hst]
    have hi := (bridgeCoefficientMeasure_independent n).indepFun hst
    have hscalar : IndepFun
        (fun ω : ∀ j : ℕ, Fin (2 ^ j) → EuclideanSpace ℝ (Fin n) => ω s.1 s.2 i)
        (fun ω : ∀ j : ℕ, Fin (2 ^ j) → EuclideanSpace ℝ (Fin n) => ω t.1 t.2 l)
        (bridgeCoefficientMeasure n) := by
      simpa only [coordinateFunctional_apply, Function.comp_def] using hi.comp
        (coordinateFunctional n i).continuous.measurable (coordinateFunctional n l).continuous.measurable
    rw [hscalar.integral_fun_mul_eq_mul_integral
      (bridgeScalarCoefficient_gaussian n s.1 s.2 i).memLp_two.aestronglyMeasurable
      (bridgeScalarCoefficient_gaussian n t.1 t.2 l).memLp_two.aestronglyMeasurable,
      bridgeScalarCoefficient_mean, bridgeScalarCoefficient_mean, zero_mul]

theorem bridgeScalarCoefficientL2_orthonormal (n : ℕ) :
    Orthonormal ℝ (fun p : (Σ j : ℕ, Fin (2 ^ j)) × Fin n =>
      bridgeScalarCoefficientL2 n p.1.1 p.1.2 p.2) := by
  classical
  rw [orthonormal_iff_ite]
  intro s t
  rw [bridgeScalarCoefficientL2_inner]
  by_cases hst : s.1 = t.1 <;> by_cases hil : s.2 = t.2 <;>
    simp [hst, hil, Prod.ext_iff]

end AffineFKProof
