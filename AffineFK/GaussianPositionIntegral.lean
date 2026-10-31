module

public import AffineFK.GaussianKernelDerivativeBounds
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Differentiating the actual Gaussian integral over a linear image

The fixed-domain Gaussian functional is differentiated on the genuine
space of continuous linear maps. Its derivative bound is derived from
the proved global Gaussian derivative bounds, with the compact-domain
integrable majorant C norm(x). No first-variation formula is assumed.
Mathlib's dominated parameter differentiation is due to Patrick Massot;
the higher Gaussian derivative interfaces retain their earlier attribution.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ContDiff RealInnerProductSpace

def gaussianPositionIntegral (n : ℕ) (K : Set (EuclideanSpace ℝ (Fin n)))
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) : ℝ :=
  ∫ x in K, standardGaussianDensity n (A x)

def gaussianPositionDerivativeIntegrand (n : ℕ)
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (x : EuclideanSpace ℝ (Fin n)) :
    (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) →L[ℝ] ℝ :=
  (fderiv ℝ (standardGaussianDensity n) (A x)).comp
    (ContinuousLinearMap.apply ℝ (EuclideanSpace ℝ (Fin n)) x)

theorem gaussianPositionDerivativeIntegrand_continuous (n : ℕ)
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) :
    Continuous (gaussianPositionDerivativeIntegrand n A) := by
  exact (((standardGaussianDensity_smooth n).continuous_fderiv (by simp)).comp A.continuous).clm_comp
    (ContinuousLinearMap.apply ℝ (EuclideanSpace ℝ (Fin n))).continuous

theorem gaussianPositionIntegral_hasFDerivAt (n : ℕ)
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsCompact K)
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) :
    HasFDerivAt (gaussianPositionIntegral n K)
      (∫ x in K, gaussianPositionDerivativeIntegrand n A x) A := by
  let E := EuclideanSpace ℝ (Fin n)
  obtain ⟨C, hC, hbound⟩ := standardGaussianDensity_iteratedFDeriv_bound n 1
  have hD (x : E) : ‖fderiv ℝ (standardGaussianDensity n) x‖ ≤ C := by
    simpa only [norm_iteratedFDeriv_one] using hbound x
  have hEval (x : E) : ‖ContinuousLinearMap.apply ℝ E x‖ ≤ ‖x‖ := by
    apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro B
    simpa only [ContinuousLinearMap.apply_apply, mul_comm] using B.le_opNorm x
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le
    (s := Set.univ) (bound := fun x : E => C * ‖x‖) Filter.univ_mem
  · exact Eventually.of_forall fun B =>
      ((standardGaussianDensity_smooth n).continuous.comp B.continuous).aestronglyMeasurable
  · exact ContinuousOn.integrableOn_compact hK
      ((standardGaussianDensity_smooth n).continuous.comp A.continuous).continuousOn
  · exact (gaussianPositionDerivativeIntegrand_continuous n A).aestronglyMeasurable
  · exact Eventually.of_forall fun x B _ =>
      (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul (hD (B x)) (hEval x) (norm_nonneg _) hC)
  · exact ContinuousOn.integrableOn_compact hK (continuous_const.mul continuous_norm).continuousOn
  · exact Eventually.of_forall fun x B _ => by
      change HasFDerivAt (fun L : E →L[ℝ] E => standardGaussianDensity n (L x))
        ((fderiv ℝ (standardGaussianDensity n) (B x)).comp (ContinuousLinearMap.apply ℝ E x)) B
      exact (((standardGaussianDensity_smooth n).differentiable (by simp)).differentiableAt
        (x := B x)).hasFDerivAt.comp B (ContinuousLinearMap.apply ℝ E x).hasFDerivAt

theorem gaussianPositionIntegral_first_variation (n : ℕ)
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsCompact K)
    (L : ℝ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (B : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hL : HasDerivAt L B 0) (hLzero : L 0 = ContinuousLinearMap.id ℝ _) :
    HasDerivAt (fun t => gaussianPositionIntegral n K (L t))
      (-(∫ x in K, ⟪B x, x⟫ * standardGaussianDensity n x)) 0 := by
  have houter := gaussianPositionIntegral_hasFDerivAt n K hK (L 0)
  have h := houter.comp_hasDerivAt 0 hL
  have heq : (∫ x in K, gaussianPositionDerivativeIntegrand n (L 0) x) B =
      -(∫ x in K, ⟪B x, x⟫ * standardGaussianDensity n x) := by
    rw [ContinuousLinearMap.integral_apply (by
      exact ContinuousOn.integrableOn_compact hK
        (gaussianPositionDerivativeIntegrand_continuous n (L 0)).continuousOn), ← integral_neg]
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      simp only [gaussianPositionDerivativeIntegrand, hLzero, ContinuousLinearMap.id_apply,
        fderiv_standardGaussianDensity, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.apply_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
        InnerProductSpace.toDual_apply_apply, inner_neg_left, real_inner_comm]
      ring
  rwa [heq] at h

end AffineFKProof
