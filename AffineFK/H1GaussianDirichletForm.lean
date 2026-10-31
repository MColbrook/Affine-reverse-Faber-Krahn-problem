module

public import AffineFK.BridgeGaussianL2Average
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Exact Dirichlet form of the genuine Gaussian L2 average

No H1 or positivity premise is needed for the Hilbert-space difference
identity. The Gaussian average is the actual Bochner average of actual
Lebesgue L2 translation isometries.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory InnerProductSpace
open scoped RealInnerProductSpace

def h1GaussianDirichletForm (n : ℕ) (h : ℝ)
    (f : Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) : ℝ :=
  (2 / h) * (‖f‖^2 - ⟪f, bridgeGaussianL2Average n (Real.sqrt h) f⟫)

theorem gaussianL2Average_difference_sq_identity (n : ℕ) (b : ℝ)
    (f : Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    Integrable (fun u => ‖bridgeL2Translate n (b • u) f - f‖^2)
      (stdGaussian (EuclideanSpace ℝ (Fin n))) ∧
      (∫ u, ‖bridgeL2Translate n (b • u) f - f‖^2
        ∂stdGaussian (EuclideanSpace ℝ (Fin n))) =
        2 * (‖f‖^2 - ⟪f, bridgeGaussianL2Average n b f⟫) := by
  let E := EuclideanSpace ℝ (Fin n)
  let γ := stdGaussian E
  have hiV := bridgeGaussianL2Average_integrable n b f
  have hi : Integrable (fun u => ⟪f, bridgeL2Translate n (b • u) f⟫) γ :=
    (innerSL ℝ f).integrable_comp hiV
  have heq (u : E) : ‖bridgeL2Translate n (b • u) f - f‖^2 =
      2 * ‖f‖^2 - 2 * ⟪f, bridgeL2Translate n (b • u) f⟫ := by
    rw [norm_sub_sq_real, bridgeL2Translate_norm, real_inner_comm]
    ring
  have hR : Integrable (fun u => 2 * ‖f‖^2 -
      2 * ⟪f, bridgeL2Translate n (b • u) f⟫) γ :=
    (integrable_const _).sub (hi.const_mul 2)
  have hD := hR.congr (Filter.Eventually.of_forall fun u => (heq u).symm)
  have hinner : (∫ u, ⟪f, bridgeL2Translate n (b • u) f⟫ ∂γ) =
      ⟪f, bridgeGaussianL2Average n b f⟫ :=
    (innerSL ℝ f).integral_comp_comm hiV
  refine ⟨hD, ?_⟩
  calc
    _ = ∫ u, (2 * ‖f‖^2 - 2 * ⟪f, bridgeL2Translate n (b • u) f⟫) ∂γ :=
      integral_congr_ae (Filter.Eventually.of_forall heq)
    _ = _ := by
      rw [integral_sub (integrable_const _) (hi.const_mul 2)]
      rw [integral_const_mul]
      rw [integral_const_mul, hinner]
      simp only [integral_const, probReal_univ, one_smul]
      ring

theorem h1GaussianDirichletForm_eq_translation_integral (n : ℕ) (h : ℝ)
    (f : Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    h1GaussianDirichletForm n h f =
      h⁻¹ * (∫ u, ‖bridgeL2Translate n (Real.sqrt h • u) f - f‖^2
        ∂stdGaussian (EuclideanSpace ℝ (Fin n))) := by
  rw [(gaussianL2Average_difference_sq_identity n (Real.sqrt h) f).2]
  unfold h1GaussianDirichletForm
  ring

end AffineFKProof
