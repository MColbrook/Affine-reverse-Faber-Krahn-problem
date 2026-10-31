module

public import AffineFK.ConvolutionDensityProduct
public import AffineFK.ConvolutionScoreField
public import AffineFK.GaussianHessianL2Calculus

/-!
# The actual second-ratio combination of two independent density inputs

The combination contains the two genuine input second-density ratios and
the two mixed products of their actual ordinary scores. Its L2 entries
follow from input L4 scores and L2 ratios. The proved first/second/mixed
compact product identities give its exact normalized output test identity.
No identity or integrability of an output density ratio is assumed.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory TopologicalSpace
open scoped Distributions ContDiff ENNReal

def convolutionSecondRatioCombination (n : ℕ)
    (ρ₁ ρ₂ : EuclideanSpace ℝ (Fin n) → ℝ) (a b : ℝ)
    (p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => a ^ 2 * secondDensityRatio n ρ₁ i j p.1 + b ^ 2 * secondDensityRatio n ρ₂ i j p.2 +
    (a * b) * (gradient (fun x => Real.log (ρ₁ x)) p.1 i * gradient (fun x => Real.log (ρ₂ x)) p.2 j +
      gradient (fun x => Real.log (ρ₁ x)) p.1 j * gradient (fun x => Real.log (ρ₂ x)) p.2 i)

theorem convolutionSecondRatioCombination_entry_memLp (n : ℕ)
    (ρ₁ ρ₂ : EuclideanSpace ℝ (Fin n) → ℝ)
    [IsProbabilityMeasure (densityMeasure n ρ₁)] [IsProbabilityMeasure (densityMeasure n ρ₂)]
    (hs₁ : MemLp (gradient (fun x => Real.log (ρ₁ x))) 4 (densityMeasure n ρ₁))
    (hs₂ : MemLp (gradient (fun x => Real.log (ρ₂ x))) 4 (densityMeasure n ρ₂))
    (hq₁ : ∀ i j : Fin n, MemLp (secondDensityRatio n ρ₁ i j) 2 (densityMeasure n ρ₁))
    (hq₂ : ∀ i j : Fin n, MemLp (secondDensityRatio n ρ₂ i j) 2 (densityMeasure n ρ₂))
    (a b : ℝ) (i j : Fin n) :
    MemLp (fun p => convolutionSecondRatioCombination n ρ₁ ρ₂ a b p i j) 2
      ((densityMeasure n ρ₁).prod (densityMeasure n ρ₂)) := by
  let : ENNReal.HolderTriple 4 4 2 := ⟨by
    rw [show (4 : ℝ≥0∞) = 2 * 2 by norm_num, ENNReal.mul_inv,
      ← mul_add, ENNReal.inv_two_add_inv_two, mul_one]
    all_goals norm_num⟩
  have hsi := hs₁.comp_fst (densityMeasure n ρ₂)
  have hsj := hs₂.comp_snd (densityMeasure n ρ₁)
  exact ((((hq₁ i j).comp_fst _).const_mul (a ^ 2)).add
    (((hq₂ i j).comp_snd _).const_mul (b ^ 2))).add
      ((((hsi.eval_piLp i).mul (hsj.eval_piLp j)).add
        ((hsi.eval_piLp j).mul (hsj.eval_piLp i))).const_mul (a * b))

theorem convolutionSecondRatioCombination_test_identity (n : ℕ)
    (ρ₁ ρ₂ : EuclideanSpace ℝ (Fin n) → ℝ)
    (hρ₁ : ContDiff ℝ ∞ ρ₁) (hpos₁ : ∀ x, 0 < ρ₁ x)
    (hρ₂ : ContDiff ℝ ∞ ρ₂) (hpos₂ : ∀ x, 0 < ρ₂ x)
    [IsProbabilityMeasure (densityMeasure n ρ₁)] [IsProbabilityMeasure (densityMeasure n ρ₂)]
    (hs₁ : MemLp (gradient (fun x => Real.log (ρ₁ x))) 4 (densityMeasure n ρ₁))
    (hs₂ : MemLp (gradient (fun x => Real.log (ρ₂ x))) 4 (densityMeasure n ρ₂))
    (hq₁ : ∀ i j : Fin n, MemLp (secondDensityRatio n ρ₁ i j) 2 (densityMeasure n ρ₁))
    (hq₂ : ∀ i j : Fin n, MemLp (secondDensityRatio n ρ₂ i j) 2 (densityMeasure n ρ₂))
    (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ^ 2 + b ^ 2 = 1)
    (i j : Fin n) (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ)) :
    (∫ p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n),
      convolutionSecondRatioCombination n ρ₁ ρ₂ a b p i j * φ (a • p.1 + b • p.2)
      ∂(densityMeasure n ρ₁).prod (densityMeasure n ρ₂)) =
      ∫ p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n),
        partialTest n i (partialTest n j φ) (a • p.1 + b • p.2)
          ∂(densityMeasure n ρ₁).prod (densityMeasure n ρ₂) := by
  let E := EuclideanSpace ℝ (Fin n)
  let ν := densityMeasure n ρ₁
  let η := densityMeasure n ρ₂
  let μ := ν.prod η
  let W : E × E → E := fun p => a • p.1 + b • p.2
  let s₁ := gradient (fun x => Real.log (ρ₁ x))
  let s₂ := gradient (fun x => Real.log (ρ₂ x))
  let f₁ : E × E → ℝ := fun p => secondDensityRatio n ρ₁ i j p.1 * φ (W p)
  let f₂ : E × E → ℝ := fun p => secondDensityRatio n ρ₂ i j p.2 * φ (W p)
  let f₁₂ : E × E → ℝ := fun p => (s₁ p.1 i * s₂ p.2 j) * φ (W p)
  let f₂₁ : E × E → ℝ := fun p => (s₁ p.1 j * s₂ p.2 i) * φ (W p)
  let D : ℝ := ∫ p, partialTest n i (partialTest n j φ) (W p) ∂μ
  have hW : Continuous W := by dsimp [W]; fun_prop
  have h₁ : Integrable f₁ μ := integrable_fst_mul_test_comp n ν η _ ((hq₁ i j).integrable (by norm_num)) W hW φ
  have h₂ : Integrable f₂ μ := integrable_snd_mul_test_comp n ν η _ ((hq₂ i j).integrable (by norm_num)) W hW φ
  have h₁₂ : Integrable f₁₂ μ := integrable_product_mul_test_comp n ν η _ _
    ((hs₁.eval_piLp i).integrable (by norm_num)) ((hs₂.eval_piLp j).integrable (by norm_num)) W hW φ
  have h₂₁ : Integrable f₂₁ μ := integrable_product_mul_test_comp n ν η _ _
    ((hs₁.eval_piLp j).integrable (by norm_num)) ((hs₂.eval_piLp i).integrable (by norm_num)) W hW φ
  have hs₁₂ : MemLp s₁ 2 ν := hs₁.mono_exponent (by norm_num)
  have hs₂₂ : MemLp s₂ 2 η := hs₂.mono_exponent (by norm_num)
  have hfirst : (∫ p, f₁ p ∂μ) = a ^ 2 * D := smooth_density_convolution_second_fst n ρ₁ hρ₁ hpos₁ η i j (hq₁ i j) a b ha φ
  have hsecond : (∫ p, f₂ p ∂μ) = b ^ 2 * D := smooth_density_convolution_second_snd n ν ρ₂ hρ₂ hpos₂ i j (hq₂ i j) a b hb φ
  have hcross₁₂ : (∫ p, f₁₂ p ∂μ) = (a * b) * D :=
    smooth_density_convolution_cross_identity n ρ₁ ρ₂ hρ₁ hpos₁ hρ₂ hpos₂ hs₁₂ hs₂₂ i j a b ha hb φ
  have hcross₂₁ : (∫ p, f₂₁ p ∂μ) = (a * b) * D := by
    have h := smooth_density_convolution_cross_identity n ρ₁ ρ₂ hρ₁ hpos₁ hρ₂ hpos₂ hs₁₂ hs₂₂ j i a b ha hb φ
    have heq : partialTest n j (partialTest n i φ) = partialTest n i (partialTest n j φ) := by
      ext x
      exact partialTest_commute n j i φ x
    rw [heq] at h
    exact h
  calc
    _ = ∫ p, a ^ 2 * f₁ p + b ^ 2 * f₂ p + (a * b) * (f₁₂ p + f₂₁ p) ∂μ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun p => by
        dsimp only [convolutionSecondRatioCombination, f₁, f₂, f₁₂, f₂₁, s₁, s₂, W]
        ring
    _ = a ^ 2 * (∫ p, f₁ p ∂μ) + b ^ 2 * (∫ p, f₂ p ∂μ) +
        (a * b) * ((∫ p, f₁₂ p ∂μ) + (∫ p, f₂₁ p ∂μ)) := by
      rw [integral_add (f := fun p => a ^ 2 * f₁ p + b ^ 2 * f₂ p)
        (g := fun p => (a * b) * (f₁₂ p + f₂₁ p))
          ((h₁.const_mul _).add (h₂.const_mul _)) ((h₁₂.add h₂₁).const_mul _),
        integral_add (f := fun p => a ^ 2 * f₁ p) (g := fun p => b ^ 2 * f₂ p)
          (h₁.const_mul _) (h₂.const_mul _), integral_const_mul, integral_const_mul, integral_const_mul,
        integral_add h₁₂ h₂₁]
    _ = (a ^ 2 + b ^ 2) ^ 2 * D := by rw [hfirst, hsecond, hcross₁₂, hcross₂₁]; ring
    _ = _ := by rw [hab, one_pow, one_mul]

end AffineFKProof
