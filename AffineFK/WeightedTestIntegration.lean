module

public import AffineFK.SteinTestIdentities
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.Tactic.FieldSimp

/-!
# Integration by parts for the positive smooth weight

The measure is literally rho times Lebesgue volume. Its weighted directional
divergence on a scalar test is rho^{-1} partial_j(rho phi). The functions used
here are actual smooth compact tests, so the integration-by-parts products
are integrable. The ambient Haar integration-by-parts theorem is reused from
Sebastien Gouezel's Mathlib LineDeriv.IntegrationByParts development.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory TopologicalSpace
open scoped Distributions RealInnerProductSpace ContDiff

def densityMeasure (n : ℕ) (ρ : EuclideanSpace ℝ (Fin n) → ℝ) :
    Measure (EuclideanSpace ℝ (Fin n)) :=
  volume.withDensity (fun x => ENNReal.ofReal (ρ x))

theorem density_integral_eq
    (n : ℕ) (ρ : EuclideanSpace ℝ (Fin n) → ℝ) (hρ : Continuous ρ)
    (hρnonneg : ∀ x, 0 ≤ ρ x) (f : EuclideanSpace ℝ (Fin n) → ℝ) :
    (∫ x, f x ∂densityMeasure n ρ) = ∫ x, ρ x * f x := by
  rw [densityMeasure, integral_withDensity_eq_integral_toReal_smul
    hρ.measurable.ennreal_ofReal (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [ENNReal.toReal_ofReal (hρnonneg x)]
  rfl

def densityMulTest
    (n : ℕ) (ρ : EuclideanSpace ℝ (Fin n) → ℝ) (hρ : ContDiff ℝ ∞ ρ)
    (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ)) :
    𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ) :=
  ⟨ρ * (φ : EuclideanSpace ℝ (Fin n) → ℝ), hρ.mul φ.contDiff,
    φ.hasCompactSupport.mul_left, Set.subset_univ _⟩

theorem densityMulTest_apply
    (n : ℕ) (ρ : EuclideanSpace ℝ (Fin n) → ℝ) (hρ : ContDiff ℝ ∞ ρ)
    (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ)) (x : EuclideanSpace ℝ (Fin n)) :
    densityMulTest n ρ hρ φ x = ρ x * φ x := by rfl

def densityDivergenceTest
    (n : ℕ) (ρ : EuclideanSpace ℝ (Fin n) → ℝ) (hρ : ContDiff ℝ ∞ ρ)
    (hρpos : ∀ x, 0 < ρ x) (j : Fin n)
    (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ)) :
    𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ) :=
  let ψ := partialTest n j (densityMulTest n ρ hρ φ)
  ⟨(ψ : EuclideanSpace ℝ (Fin n) → ℝ) * (fun x => (ρ x)⁻¹),
    ψ.contDiff.mul (hρ.inv (fun x => (hρpos x).ne')),
    ψ.hasCompactSupport.mul_right, Set.subset_univ _⟩

theorem densityDivergenceTest_apply
    (n : ℕ) (ρ : EuclideanSpace ℝ (Fin n) → ℝ) (hρ : ContDiff ℝ ∞ ρ)
    (hρpos : ∀ x, 0 < ρ x) (j : Fin n)
    (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ)) (x : EuclideanSpace ℝ (Fin n)) :
    densityDivergenceTest n ρ hρ hρpos j φ x =
      partialTest n j (densityMulTest n ρ hρ φ) x / ρ x := by
  change partialTest n j (densityMulTest n ρ hρ φ) x * (ρ x)⁻¹ = _
  rw [div_eq_mul_inv]

theorem test_partial_integration_by_parts
    (n : ℕ) (j : Fin n)
    (f φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ)) :
    (∫ x, partialTest n j f x * φ x) = -(∫ x, f x * partialTest n j φ x) := by
  have hleft : Integrable (fun x => fderiv ℝ f x (EuclideanSpace.basisFun (Fin n) ℝ j) * φ x) := by
    simp_rw [← partialTest_fderiv n j f]
    exact ((partialTest n j f).continuous.mul φ.continuous).integrable_of_hasCompactSupport
      (partialTest n j f).hasCompactSupport.mul_right
  have hright : Integrable (fun x => f x * fderiv ℝ φ x (EuclideanSpace.basisFun (Fin n) ℝ j)) := by
    simp_rw [← partialTest_fderiv n j φ]
    exact (f.continuous.mul (partialTest n j φ).continuous).integrable_of_hasCompactSupport
      f.hasCompactSupport.mul_right
  have hproduct : Integrable (fun x => f x * φ x) :=
    (f.continuous.mul φ.continuous).integrable_of_hasCompactSupport f.hasCompactSupport.mul_right
  have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable hleft hright hproduct
    (fun x _hx => (f.contDiff.differentiable (by simp)).differentiableAt)
    (fun x _hx => (φ.contDiff.differentiable (by simp)).differentiableAt)
  simp_rw [← partialTest_fderiv n j f, ← partialTest_fderiv n j φ] at h
  linarith

theorem weighted_test_integration_by_parts
    (n : ℕ) (ρ : EuclideanSpace ℝ (Fin n) → ℝ) (hρ : ContDiff ℝ ∞ ρ)
    (hρpos : ∀ x, 0 < ρ x) (j : Fin n)
    (f φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ)) :
    (∫ x, partialTest n j f x * φ x ∂densityMeasure n ρ) =
      -(∫ x, f x * densityDivergenceTest n ρ hρ hρpos j φ x ∂densityMeasure n ρ) := by
  calc
    _ = ∫ x, partialTest n j f x * densityMulTest n ρ hρ φ x := by
      rw [density_integral_eq n ρ hρ.continuous (fun x => (hρpos x).le)]
      apply integral_congr_ae
      filter_upwards [] with x
      rw [densityMulTest_apply]
      ring
    _ = -(∫ x, f x * partialTest n j (densityMulTest n ρ hρ φ) x) :=
      test_partial_integration_by_parts n j f (densityMulTest n ρ hρ φ)
    _ = _ := by
      rw [density_integral_eq n ρ hρ.continuous (fun x => (hρpos x).le)]
      congr 1
      apply integral_congr_ae
      filter_upwards [] with x
      rw [densityDivergenceTest_apply]
      field_simp [(hρpos x).ne']

end AffineFKProof
