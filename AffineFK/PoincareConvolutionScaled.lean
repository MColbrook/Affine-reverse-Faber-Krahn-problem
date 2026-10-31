module

public import AffineFK.PoincareConvolution
public import AffineFK.PoincareLinearMapScalar

/-! Exact weighted Poincare inheritance for two independent product inputs. -/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory TopologicalSpace InnerProductSpace
open scoped Distributions RealInnerProductSpace

theorem poincareConvolution_scaled (n : ℕ)
    (ν η : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν] [IsProbabilityMeasure η]
    (P Q : ℝ) (hP0 : 0 ≤ P) (hQ0 : 0 ≤ Q)
    (hP : ∀ f : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ),
      (∫ x, (f x - ∫ y, f y ∂ν) ^ 2 ∂ν) ≤ P * (∫ x, ‖gradient f x‖ ^ 2 ∂ν))
    (hQ : ∀ f : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ),
      (∫ x, (f x - ∫ y, f y ∂η) ^ 2 ∂η) ≤ Q * (∫ x, ‖gradient f x‖ ^ 2 ∂η))
    (a b : ℝ) (f : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ)) :
    (∫ x, (f x - ∫ y, f y ∂(ν.prod η).map (fun p => a • p.1 + b • p.2)) ^ 2
      ∂(ν.prod η).map (fun p => a • p.1 + b • p.2)) ≤
      (a ^ 2 * P + b ^ 2 * Q) *
        (∫ x, ‖gradient f x‖ ^ 2 ∂(ν.prod η).map (fun p => a • p.1 + b • p.2)) := by
  have h := poincareConvolution n (ν.map (fun x => a • x)) (η.map (fun x => b • x))
    (a ^ 2 * P) (b ^ 2 * Q) (mul_nonneg (sq_nonneg _) hP0) (mul_nonneg (sq_nonneg _) hQ0)
    (poincareLinearMap_scalar n ν P hP0 hP a) (poincareLinearMap_scalar n η Q hQ0 hQ b) f
  have hlaw : ((ν.map (fun x => a • x)).prod (η.map (fun x => b • x))).map
      (fun p => p.1 + p.2) = (ν.prod η).map (fun p => a • p.1 + b • p.2) := by
    rw [Measure.map_prod_map ν η (by fun_prop) (by fun_prop), Measure.map_map (by fun_prop) (by fun_prop)]
    rfl
  rwa [hlaw] at h

end AffineFKProof
