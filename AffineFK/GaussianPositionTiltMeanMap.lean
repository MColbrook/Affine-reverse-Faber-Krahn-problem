module

public import AffineFK.GaussianPositionTiltPositiveHessian
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Convex.Integral

/-!
# Injectivity and the actual image of the tilted mean map

Strict positivity of the proved Hessian makes its scalar derivative along
every nonconstant affine line strictly positive. The genuine real mean
value theorem then gives global injectivity of the actual gradient map.
The actual probability law is supported on K, so its mean belongs to K
when K is compact and convex. No injectivity, image or Jacobian integral
is assumed. The change-of-variables argument is a separate development.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory Set
open scoped RealInnerProductSpace

theorem gaussianPositionTiltLaw_ae_mem (n : ℕ)
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : MeasurableSet K)
    (y : EuclideanSpace ℝ (Fin n)) : ∀ᵐ x ∂gaussianPositionTiltLaw n K y, x ∈ K :=
  (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem hK)

theorem gaussianPositionLogLaplace_gradient_mem (n : ℕ)
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsCompact K)
    (hconv : Convex ℝ K) (hvol : 0 < volume K) (y : EuclideanSpace ℝ (Fin n)) :
    gradient (gaussianPositionLogLaplace n K) y ∈ K := by
  let : IsProbabilityMeasure (gaussianPositionTiltLaw n K y) :=
    gaussianPositionTiltLaw_isProbabilityMeasure n K hK hvol y
  rw [gaussianPositionLogLaplace_gradient_mean n K hK hvol y]
  exact hconv.integral_mem hK.isClosed (gaussianPositionTiltLaw_ae_mem n K hK.measurableSet y)
    (gaussianPositionTiltLaw_continuous_integrable n K hK hvol y id continuous_id)

theorem gaussianPositionLogLaplace_gradient_derivative_covariance (n : ℕ)
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsCompact K) (hvol : 0 < volume K)
    (y u v : EuclideanSpace ℝ (Fin n)) :
    ⟪(fderiv ℝ (gradient (gaussianPositionLogLaplace n K)) y) v, u⟫ =
      (∫ x, ⟪x, u⟫ * ⟪x, v⟫ ∂gaussianPositionTiltLaw n K y) -
        (∫ x, ⟪x, u⟫ ∂gaussianPositionTiltLaw n K y) *
          (∫ x, ⟪x, v⟫ ∂gaussianPositionTiltLaw n K y) := by
  let E := EuclideanSpace ℝ (Fin n)
  have hd := (InnerProductSpace.toDual ℝ E).hasFDerivAt.comp y
    (gaussianPositionLogLaplace_gradient_differentiableAt n K hK hvol y).hasFDerivAt
  have heq : (fun z => (InnerProductSpace.toDual ℝ E)
      (gradient (gaussianPositionLogLaplace n K) z)) =
      fderiv ℝ (gaussianPositionLogLaplace n K) :=
    funext fun z => toDual_gradient (𝕜 := ℝ)
  simp only [Function.comp_def] at hd
  rw [heq] at hd
  calc
    _ = ((fderiv ℝ (fderiv ℝ (gaussianPositionLogLaplace n K)) y) v) u := by
      rw [hd.fderiv]
      rfl
    _ = _ := gaussianPositionLogLaplace_hessian_covariance n K hK hvol y u v

theorem gaussianPositionLogLaplace_gradient_injective (n : ℕ)
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsCompact K) (hvol : 0 < volume K) :
    Function.Injective (gradient (gaussianPositionLogLaplace n K)) := by
  intro x y hxy
  by_contra hne
  let v := y - x
  have hv : v ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
  let f : ℝ → ℝ := fun t => (fderiv ℝ (gaussianPositionLogLaplace n K) (x + t • v)) v
  have hf (t : ℝ) : HasDerivAt f
      (((fderiv ℝ (fderiv ℝ (gaussianPositionLogLaplace n K)) (x + t • v)) v) v) t := by
    have hd := (gaussianPositionLogLaplace_fderiv_differentiableAt n K hK hvol
      (x + t • v)).hasFDerivAt.clm_apply (hasFDerivAt_const v (x + t • v))
    have hp : HasDerivAt (fun s : ℝ => x + s • v) v t := by
      simpa only [one_smul, id_eq] using ((hasDerivAt_id t).smul_const v).const_add x
    have h := hd.comp_hasDerivAt t hp
    simpa only [Function.comp_def, ContinuousLinearMap.comp_apply, add_apply, zero_apply,
      map_zero, zero_add, ContinuousLinearMap.flip_apply, f] using h
  have hmono : StrictMono f := strictMono_of_hasDerivAt_pos hf
    (fun t => gaussianPositionLogLaplace_hessian_positive n K hK hvol (x + t • v) v hv)
  have hlt := hmono (by norm_num : (0 : ℝ) < 1)
  have hzero : f 0 = ⟪gradient (gaussianPositionLogLaplace n K) x, v⟫ := by
    simp only [f, zero_smul, add_zero]
    exact (inner_gradient_left (𝕜 := ℝ)).symm
  have hone : f 1 = ⟪gradient (gaussianPositionLogLaplace n K) y, v⟫ := by
    simp only [f, one_smul, v, add_sub_cancel]
    exact (inner_gradient_left (𝕜 := ℝ)).symm
  rw [hzero, hone, hxy] at hlt
  exact lt_irrefl _ hlt

end AffineFKProof
