module

public import AffineFK.LogDensityIntegration
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-!
# Ordered second derivatives divided by a positive density

The ratio uses the actual Frechet derivatives of the density. Compact
Lebesgue integration by parts is applied twice before any global L2
claim about the ratio. Mathlib's Haar integration-by-parts and compact
distributional uniqueness results are due to Sebastien Gouezel.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory TopologicalSpace
open scoped Distributions RealInnerProductSpace ContDiff

/-- The derivative first in coordinate i and then in coordinate j, divided
by the actual density. -/
def secondDensityRatio (n : ℕ) (ρ : EuclideanSpace ℝ (Fin n) → ℝ)
    (i j : Fin n) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  fderiv ℝ (fun y => fderiv ℝ ρ y (EuclideanSpace.basisFun (Fin n) ℝ i)) x
    (EuclideanSpace.basisFun (Fin n) ℝ j) / ρ x

theorem smooth_partial_test_integration_by_parts (n : ℕ)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ContDiff ℝ ∞ f)
    (i : Fin n) (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ)) :
    Integrable (fun x => fderiv ℝ f x (EuclideanSpace.basisFun (Fin n) ℝ i) * φ x) ∧
    Integrable (fun x => f x * partialTest n i φ x) ∧
    (∫ x, fderiv ℝ f x (EuclideanSpace.basisFun (Fin n) ℝ i) * φ x) =
      -(∫ x, f x * partialTest n i φ x) := by
  have hd : Continuous (fun x => fderiv ℝ f x (EuclideanSpace.basisFun (Fin n) ℝ i)) :=
    (hf.continuous_fderiv (by simp)).clm_apply continuous_const
  have hL : Integrable (fun x => fderiv ℝ f x (EuclideanSpace.basisFun (Fin n) ℝ i) * φ x) :=
    (hd.mul φ.continuous).integrable_of_hasCompactSupport φ.hasCompactSupport.mul_left
  have hR : Integrable (fun x => f x * partialTest n i φ x) :=
    (hf.continuous.mul (partialTest n i φ).continuous).integrable_of_hasCompactSupport
      (partialTest n i φ).hasCompactSupport.mul_left
  have hP : Integrable (fun x => f x * φ x) :=
    (hf.continuous.mul φ.continuous).integrable_of_hasCompactSupport φ.hasCompactSupport.mul_left
  have hR' : Integrable (fun x => f x *
      fderiv ℝ φ x (EuclideanSpace.basisFun (Fin n) ℝ i)) := by
    simpa only [← partialTest_fderiv n i φ] using hR
  have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable hL hR' hP
    (fun x _ => (hf.differentiable (by simp)).differentiableAt)
    (fun x _ => (φ.contDiff.differentiable (by simp)).differentiableAt)
  refine ⟨hL, hR, ?_⟩
  simp_rw [← partialTest_fderiv n i φ] at h
  linarith

theorem secondDensityRatio_continuous (n : ℕ)
    (ρ : EuclideanSpace ℝ (Fin n) → ℝ) (hρ : ContDiff ℝ ∞ ρ)
    (hρpos : ∀ x, 0 < ρ x) (i j : Fin n) :
    Continuous (secondDensityRatio n ρ i j) := by
  have hi : ContDiff ℝ ∞ (fun x => fderiv ℝ ρ x (EuclideanSpace.basisFun (Fin n) ℝ i)) :=
    (hρ.fderiv_right (by simp)).clm_apply contDiff_const
  exact ((hi.continuous_fderiv (by simp)).clm_apply continuous_const).div
    hρ.continuous (fun x => (hρpos x).ne')

theorem secondDensityRatio_test_identity (n : ℕ)
    (ρ : EuclideanSpace ℝ (Fin n) → ℝ) (hρ : ContDiff ℝ ∞ ρ)
    (hρpos : ∀ x, 0 < ρ x) [IsProbabilityMeasure (densityMeasure n ρ)]
    (i j : Fin n) (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ)) :
    Integrable (fun x => secondDensityRatio n ρ i j x * φ x) (densityMeasure n ρ) ∧
    Integrable (partialTest n i (partialTest n j φ)) (densityMeasure n ρ) ∧
    (∫ x, secondDensityRatio n ρ i j x * φ x ∂densityMeasure n ρ) =
      ∫ x, partialTest n i (partialTest n j φ) x ∂densityMeasure n ρ := by
  have hi : ContDiff ℝ ∞ (fun x => fderiv ℝ ρ x (EuclideanSpace.basisFun (Fin n) ℝ i)) :=
    (hρ.fderiv_right (by simp)).clm_apply contDiff_const
  have h1 := smooth_partial_test_integration_by_parts n _ hi j φ
  have h2 := smooth_partial_test_integration_by_parts n ρ hρ i (partialTest n j φ)
  refine ⟨((secondDensityRatio_continuous n ρ hρ hρpos i j).mul φ.continuous).integrable_of_hasCompactSupport
      φ.hasCompactSupport.mul_left,
    (partialTest n i (partialTest n j φ)).continuous.integrable_of_hasCompactSupport
      (partialTest n i (partialTest n j φ)).hasCompactSupport, ?_⟩
  calc
    _ = ∫ x, fderiv ℝ (fun y => fderiv ℝ ρ y
        (EuclideanSpace.basisFun (Fin n) ℝ i)) x
        (EuclideanSpace.basisFun (Fin n) ℝ j) * φ x := by
      rw [density_integral_eq n ρ hρ.continuous (fun x => (hρpos x).le)]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by
        dsimp only [secondDensityRatio]
        field_simp [(hρpos x).ne']
    _ = -(∫ x, fderiv ℝ ρ x (EuclideanSpace.basisFun (Fin n) ℝ i) *
        partialTest n j φ x) := h1.2.2
    _ = ∫ x, ρ x * partialTest n i (partialTest n j φ) x := by linarith [h2.2.2]
    _ = _ := (density_integral_eq n ρ hρ.continuous (fun x => (hρpos x).le) _).symm

theorem secondDensityRatio_identified_by_test_identity (n : ℕ)
    (ρ : EuclideanSpace ℝ (Fin n) → ℝ) (hρ : ContDiff ℝ ∞ ρ)
    (hρpos : ∀ x, 0 < ρ x) [IsProbabilityMeasure (densityMeasure n ρ)]
    (i j : Fin n) (q : EuclideanSpace ℝ (Fin n) → ℝ)
    (hq : MemLp q 2 (densityMeasure n ρ))
    (hweak : ∀ φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ),
      (∫ x, q x * φ x ∂densityMeasure n ρ) =
        ∫ x, partialTest n i (partialTest n j φ) x ∂densityMeasure n ρ) :
    q =ᵐ[densityMeasure n ρ] secondDensityRatio n ρ i j ∧
    MemLp (secondDensityRatio n ρ i j) 2 (densityMeasure n ρ) ∧
    (∫ x, (secondDensityRatio n ρ i j x) ^ 2 ∂densityMeasure n ρ) =
      ∫ x, (q x) ^ 2 ∂densityMeasure n ρ := by
  have heq : q =ᵐ[densityMeasure n ρ] secondDensityRatio n ρ i j := by
    apply ae_eq_of_integral_contDiff_smul_eq
      (hq.integrable (by norm_num)).locallyIntegrable
      (secondDensityRatio_continuous n ρ hρ hρpos i j).locallyIntegrable
    intro ψ hψ hcompact
    let φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ) :=
      ⟨ψ, hψ, hcompact, Set.subset_univ _⟩
    have h := (hweak φ).trans (secondDensityRatio_test_identity n ρ hρ hρpos i j φ).2.2.symm
    change (∫ x, q x * ψ x ∂densityMeasure n ρ) =
      ∫ x, secondDensityRatio n ρ i j x * ψ x ∂densityMeasure n ρ at h
    simpa only [smul_eq_mul, mul_comm] using h
  refine ⟨heq, hq.ae_eq heq, ?_⟩
  exact integral_congr_ae (heq.symm.fun_comp fun z => z ^ 2)

end AffineFKProof
