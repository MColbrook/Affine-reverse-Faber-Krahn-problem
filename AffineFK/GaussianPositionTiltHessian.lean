module

public import AffineFK.GaussianPositionTiltMoments
public import Mathlib.Analysis.Calculus.FDeriv.Prod
public import Mathlib.Analysis.Calculus.FDeriv.CompCLM

/-!
# The actual Frechet Hessian of the logarithmic Laplace transform

The derivative of the genuine gradient is obtained from its finitely many
actual component expectations. The resulting full second Frechet derivative
is the covariance form of the already constructed tilted probability law.
No differentiability or covariance identity is supplied as a premise.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory Set
open scoped RealInnerProductSpace

theorem gaussianPositionLogLaplace_gradient_differentiableAt (n : ℕ)
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsCompact K) (hvol : 0 < volume K)
    (y : EuclideanSpace ℝ (Fin n)) :
    DifferentiableAt ℝ (gradient (gaussianPositionLogLaplace n K)) y := by
  let E := EuclideanSpace ℝ (Fin n)
  let F := gradient (gaussianPositionLogLaplace n K)
  have hi (i : Fin n) : DifferentiableAt ℝ (fun z => F z i) y := by
    have heq : (fun z => F z i) =
        (fun z => ∫ x, ⟪x, EuclideanSpace.basisFun (Fin n) ℝ i⟫
          ∂gaussianPositionTiltLaw n K z) := by
      funext z
      rw [← EuclideanSpace.inner_basisFun_real]
      exact (inner_gradient_left (𝕜 := ℝ)).trans
        (gaussianPositionLogLaplace_derivative_apply n K hK hvol z _)
    rw [heq]
    exact (gaussianPositionTiltLaw_expectation_hasFDerivAt n K hK hvol
      (fun x => ⟪x, EuclideanSpace.basisFun (Fin n) ℝ i⟫)
      (continuous_id.inner continuous_const) y).differentiableAt
  have hpi : DifferentiableAt ℝ (fun z i => F z i) y := differentiableAt_pi.mpr hi
  let L : E ≃L[ℝ] (Fin n → ℝ) := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)
  have h := L.symm.differentiableAt.comp y hpi
  convert h using 1
  funext z
  exact (L.symm_apply_apply (F z)).symm

theorem gaussianPositionLogLaplace_fderiv_differentiableAt (n : ℕ)
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsCompact K) (hvol : 0 < volume K)
    (y : EuclideanSpace ℝ (Fin n)) :
    DifferentiableAt ℝ (fderiv ℝ (gaussianPositionLogLaplace n K)) y := by
  let E := EuclideanSpace ℝ (Fin n)
  have heq : fderiv ℝ (gaussianPositionLogLaplace n K) =
      (fun z => (InnerProductSpace.toDual ℝ E) (gradient (gaussianPositionLogLaplace n K) z)) :=
    funext fun z => (toDual_gradient (𝕜 := ℝ)).symm
  rw [heq]
  exact (InnerProductSpace.toDual ℝ E).differentiableAt.comp y
    (gaussianPositionLogLaplace_gradient_differentiableAt n K hK hvol y)

theorem gaussianPositionLogLaplace_hessian_covariance (n : ℕ)
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsCompact K) (hvol : 0 < volume K)
    (y u v : EuclideanSpace ℝ (Fin n)) :
    ((fderiv ℝ (fderiv ℝ (gaussianPositionLogLaplace n K)) y) v) u =
      (∫ x, ⟪x, u⟫ * ⟪x, v⟫ ∂gaussianPositionTiltLaw n K y) -
        (∫ x, ⟪x, u⟫ ∂gaussianPositionTiltLaw n K y) *
          (∫ x, ⟪x, v⟫ ∂gaussianPositionTiltLaw n K y) := by
  have hd := gaussianPositionLogLaplace_fderiv_differentiableAt n K hK hvol y
  have heval := hd.hasFDerivAt.clm_apply (hasFDerivAt_const u y)
  have heq : (fderiv ℝ (fun z => (fderiv ℝ (gaussianPositionLogLaplace n K) z) u) y) v =
      ((fderiv ℝ (fderiv ℝ (gaussianPositionLogLaplace n K)) y) v) u := by
    rw [heval.fderiv]
    simp
  rw [← heq]
  exact gaussianPositionLogLaplace_second_derivative_covariance n K hK hvol y u v

theorem gaussianPositionLogLaplace_hessian_components (n : ℕ)
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsCompact K) (hvol : 0 < volume K)
    (y : EuclideanSpace ℝ (Fin n)) (i j : Fin n) :
    ((fderiv ℝ (fderiv ℝ (gaussianPositionLogLaplace n K)) y)
        (EuclideanSpace.basisFun (Fin n) ℝ j)) (EuclideanSpace.basisFun (Fin n) ℝ i) =
      (∫ x, x i * x j ∂gaussianPositionTiltLaw n K y) -
        (∫ x, x i ∂gaussianPositionTiltLaw n K y) *
          (∫ x, x j ∂gaussianPositionTiltLaw n K y) := by
  simpa only [EuclideanSpace.inner_basisFun_real] using
    gaussianPositionLogLaplace_hessian_covariance n K hK hvol y
      (EuclideanSpace.basisFun (Fin n) ℝ i) (EuclideanSpace.basisFun (Fin n) ℝ j)

end AffineFKProof
