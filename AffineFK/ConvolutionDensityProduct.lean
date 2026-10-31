module

public import AffineFK.ConvolutionSteinProduct
public import AffineFK.GaussianSecondDensityRatioCalculus

/-!
# Actual smooth-density score identities for an independent affine sum

The input weak identities are derived here from genuine compact
integration by parts for the actual logarithmic gradient and the actual
second-density ratio. The product identities include their proved
joint-L1 guards in the imported construction. No score, density ratio,
or Hessian identity of the output law is assumed.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory TopologicalSpace
open scoped Distributions ContDiff

theorem smooth_density_convolution_first_fst (n : ℕ)
    (ρ : EuclideanSpace ℝ (Fin n) → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hpos : ∀ x, 0 < ρ x)
    [IsProbabilityMeasure (densityMeasure n ρ)]
    (η : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure η]
    (hs : MemLp (gradient (fun x => Real.log (ρ x))) 2 (densityMeasure n ρ))
    (i : Fin n) (a b : ℝ) (ha : a ≠ 0)
    (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ)) :
    (∫ p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n),
      gradient (fun x => Real.log (ρ x)) p.1 i * φ (a • p.1 + b • p.2)
      ∂(densityMeasure n ρ).prod η) =
      -a * (∫ p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n),
        partialTest n i φ (a • p.1 + b • p.2) ∂(densityMeasure n ρ).prod η) := by
  exact (convolution_product_first_fst n (densityMeasure n ρ) η
    (fun x => gradient (fun y => Real.log (ρ y)) x i) ((hs.eval_piLp i).integrable (by norm_num)) i
    (fun ψ => (log_density_gradient_test_integration_by_parts n ρ hρ hpos i ψ).2.2) a ha b φ).2.2

theorem smooth_density_convolution_first_snd (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (ρ : EuclideanSpace ℝ (Fin n) → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hpos : ∀ x, 0 < ρ x)
    [IsProbabilityMeasure (densityMeasure n ρ)]
    (hs : MemLp (gradient (fun x => Real.log (ρ x))) 2 (densityMeasure n ρ))
    (i : Fin n) (a b : ℝ) (hb : b ≠ 0)
    (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ)) :
    (∫ p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n),
      gradient (fun x => Real.log (ρ x)) p.2 i * φ (a • p.1 + b • p.2)
      ∂ν.prod (densityMeasure n ρ)) =
      -b * (∫ p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n),
        partialTest n i φ (a • p.1 + b • p.2) ∂ν.prod (densityMeasure n ρ)) := by
  exact (convolution_product_first_snd n ν (densityMeasure n ρ)
    (fun x => gradient (fun y => Real.log (ρ y)) x i) ((hs.eval_piLp i).integrable (by norm_num)) i
    (fun ψ => (log_density_gradient_test_integration_by_parts n ρ hρ hpos i ψ).2.2) a b hb φ).2.2

theorem smooth_density_convolution_second_fst (n : ℕ)
    (ρ : EuclideanSpace ℝ (Fin n) → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hpos : ∀ x, 0 < ρ x)
    [IsProbabilityMeasure (densityMeasure n ρ)]
    (η : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure η]
    (i j : Fin n) (hq : MemLp (secondDensityRatio n ρ i j) 2 (densityMeasure n ρ))
    (a b : ℝ) (ha : a ≠ 0)
    (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ)) :
    (∫ p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n),
      secondDensityRatio n ρ i j p.1 * φ (a • p.1 + b • p.2)
      ∂(densityMeasure n ρ).prod η) =
      a ^ 2 * (∫ p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n),
        partialTest n i (partialTest n j φ) (a • p.1 + b • p.2) ∂(densityMeasure n ρ).prod η) := by
  exact (convolution_product_second_fst n (densityMeasure n ρ) η (secondDensityRatio n ρ i j)
    (hq.integrable (by norm_num)) i j
    (fun ψ => (secondDensityRatio_test_identity n ρ hρ hpos i j ψ).2.2) a ha b φ).2.2

theorem smooth_density_convolution_second_snd (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (ρ : EuclideanSpace ℝ (Fin n) → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hpos : ∀ x, 0 < ρ x)
    [IsProbabilityMeasure (densityMeasure n ρ)]
    (i j : Fin n) (hq : MemLp (secondDensityRatio n ρ i j) 2 (densityMeasure n ρ))
    (a b : ℝ) (hb : b ≠ 0)
    (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ)) :
    (∫ p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n),
      secondDensityRatio n ρ i j p.2 * φ (a • p.1 + b • p.2)
      ∂ν.prod (densityMeasure n ρ)) =
      b ^ 2 * (∫ p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n),
        partialTest n i (partialTest n j φ) (a • p.1 + b • p.2) ∂ν.prod (densityMeasure n ρ)) := by
  exact (convolution_product_second_snd n ν (densityMeasure n ρ) (secondDensityRatio n ρ i j)
    (hq.integrable (by norm_num)) i j
    (fun ψ => (secondDensityRatio_test_identity n ρ hρ hpos i j ψ).2.2) a b hb φ).2.2

theorem smooth_density_convolution_cross_identity (n : ℕ)
    (ρ₁ ρ₂ : EuclideanSpace ℝ (Fin n) → ℝ)
    (hρ₁ : ContDiff ℝ ∞ ρ₁) (hpos₁ : ∀ x, 0 < ρ₁ x)
    (hρ₂ : ContDiff ℝ ∞ ρ₂) (hpos₂ : ∀ x, 0 < ρ₂ x)
    [IsProbabilityMeasure (densityMeasure n ρ₁)] [IsProbabilityMeasure (densityMeasure n ρ₂)]
    (hs₁ : MemLp (gradient (fun x => Real.log (ρ₁ x))) 2 (densityMeasure n ρ₁))
    (hs₂ : MemLp (gradient (fun x => Real.log (ρ₂ x))) 2 (densityMeasure n ρ₂))
    (i j : Fin n) (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0)
    (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ)) :
    (∫ p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n),
      (gradient (fun x => Real.log (ρ₁ x)) p.1 i * gradient (fun y => Real.log (ρ₂ y)) p.2 j) *
        φ (a • p.1 + b • p.2) ∂(densityMeasure n ρ₁).prod (densityMeasure n ρ₂)) =
      (a * b) * (∫ p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n),
        partialTest n i (partialTest n j φ) (a • p.1 + b • p.2)
          ∂(densityMeasure n ρ₁).prod (densityMeasure n ρ₂)) := by
  exact (convolution_product_cross_identity n (densityMeasure n ρ₁) (densityMeasure n ρ₂)
    (fun x => gradient (fun z => Real.log (ρ₁ z)) x i)
    (fun y => gradient (fun z => Real.log (ρ₂ z)) y j)
    ((hs₁.eval_piLp i).integrable (by norm_num)) ((hs₂.eval_piLp j).integrable (by norm_num)) i j
    (fun ψ => (log_density_gradient_test_integration_by_parts n ρ₁ hρ₁ hpos₁ i ψ).2.2)
    (fun ψ => (log_density_gradient_test_integration_by_parts n ρ₂ hρ₂ hpos₂ j ψ).2.2)
    a b ha hb φ).2.2

end AffineFKProof
