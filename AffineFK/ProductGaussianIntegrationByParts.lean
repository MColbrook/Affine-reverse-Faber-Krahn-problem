module

public import AffineFK.GaussianCoordinateTests
public import Mathlib.MeasureTheory.Integral.Pi

/-!
# Integration by parts for a finite product of standard real Gaussians

All integrands are integrable under the actual product measure before
Fubini is applied. The coordinate split is Mathlib's measure-preserving
piFinSuccAbove equivalence. This uses the finite-product integral theory
of Xavier Roblot and Mathlib's measure construction contributors.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory TopologicalSpace
open scoped Distributions

theorem productGaussian_integration_by_parts (n : ℕ) (j : Fin n)
    (φ : 𝓓((⊤ : Opens (Fin n → ℝ)), ℝ)) :
    Integrable (fun x : Fin n → ℝ => x j * φ x) (Measure.pi fun _ => gaussianReal 0 1) ∧
    Integrable (piPartialTest n j φ) (Measure.pi fun _ => gaussianReal 0 1) ∧
      (∫ x, x j * φ x ∂Measure.pi (fun _ => gaussianReal 0 1)) =
        ∫ x, piPartialTest n j φ x ∂Measure.pi (fun _ => gaussianReal 0 1) := by
  have hleft : Integrable (fun x : Fin n → ℝ => x j * φ x)
      (Measure.pi fun _ => gaussianReal 0 1) :=
    ((continuous_apply j).mul φ.continuous).integrable_of_hasCompactSupport
      φ.hasCompactSupport.mul_left
  have hright : Integrable (piPartialTest n j φ) (Measure.pi fun _ => gaussianReal 0 1) :=
    (piPartialTest n j φ).continuous.integrable_of_hasCompactSupport
      (piPartialTest n j φ).hasCompactSupport
  refine ⟨hleft, hright, ?_⟩
  cases n with
  | zero => exact Fin.elim0 j
  | succ k =>
    let e := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 1) => ℝ) j).symm
    have he := (measurePreserving_piFinSuccAbove (fun _ : Fin (k + 1) => gaussianReal 0 1) j).symm
    have hleftProd : Integrable (fun p : ℝ × (Fin k → ℝ) => (e p) j * φ (e p))
        ((gaussianReal 0 1).prod (Measure.pi fun _ : Fin k => gaussianReal 0 1)) :=
      (he.integrable_comp_emb e.measurableEmbedding).2 hleft
    have hrightProd : Integrable (fun p : ℝ × (Fin k → ℝ) => piPartialTest (k + 1) j φ (e p))
        ((gaussianReal 0 1).prod (Measure.pi fun _ : Fin k => gaussianReal 0 1)) :=
      (he.integrable_comp_emb e.measurableEmbedding).2 hright
    calc
      _ = ∫ p : ℝ × (Fin k → ℝ), (e p) j * φ (e p)
          ∂((gaussianReal 0 1).prod (Measure.pi fun _ : Fin k => gaussianReal 0 1)) :=
        (he.integral_comp' _).symm
      _ = ∫ y : Fin k → ℝ, ∫ s : ℝ, (e (s, y)) j * φ (e (s, y))
          ∂gaussianReal 0 1 ∂Measure.pi (fun _ => gaussianReal 0 1) :=
        integral_prod_symm _ hleftProd
      _ = ∫ y : Fin k → ℝ, ∫ s : ℝ, piPartialTest (k + 1) j φ (e (s, y))
          ∂gaussianReal 0 1 ∂Measure.pi (fun _ => gaussianReal 0 1) := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun y => by
          have h := (gaussianReal_standard_integration_by_parts
            (coordinateSliceTest (k + 1) j (j.insertNth 0 y) φ)).2.2
          simp_rw [realDerivativeTest_coordinateSlice, Fin.update_insertNth] at h
          simpa [coordinateSliceTest, e, MeasurableEquiv.piFinSuccAbove_symm_apply,
            Fin.insertNthEquiv] using h
      _ = ∫ p : ℝ × (Fin k → ℝ), piPartialTest (k + 1) j φ (e p)
          ∂((gaussianReal 0 1).prod (Measure.pi fun _ : Fin k => gaussianReal 0 1)) :=
        (integral_prod_symm _ hrightProd).symm
      _ = _ := he.integral_comp' _

end AffineFKProof
