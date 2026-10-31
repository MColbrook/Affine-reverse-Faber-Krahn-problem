module

public import AffineFK.DensityApproximationL1Average

/-!
# Actual L1 approximation by probability averages of translations

Fubini and the actual translated-kernel L1 bounds prove the average is
integrable. Its L1 distance to the input is bounded by the averaged
translation error, whose proved limit is zero. The probability law may
have no moments. These are actual integrals, not an assumed semigroup
continuity or density approximation premise.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory Filter
open scoped Topology

def densityApproximationAverage (n : ℕ)
    (η : Measure (EuclideanSpace ℝ (Fin n)))
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (b : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ∫ g, f (x - b • g) ∂η

theorem densityApproximationAverage_integrable (n : ℕ)
    (η : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure η]
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hm : Measurable f)
    (hf : Integrable f (volume : Measure (EuclideanSpace ℝ (Fin n)))) (b : ℝ) :
    Integrable (densityApproximationAverage n η f b) volume := by
  have h := (densityApproximation_average_kernel_integrable n η f hm hf b).swap.integral_prod_left
  exact h

theorem densityApproximationAverage_L1_error_le (n : ℕ)
    (η : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure η]
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hm : Measurable f)
    (hf : Integrable f (volume : Measure (EuclideanSpace ℝ (Fin n)))) (b : ℝ) :
    (∫ x, ‖densityApproximationAverage n η f b x - f x‖) ≤
      ∫ g, (∫ x, ‖f (x - b • g) - f x‖) ∂η := by
  have hkernel : Integrable
      (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) => f (p.1 - b • p.2))
      (volume.prod η) := (densityApproximation_average_kernel_integrable n η f hm hf b).swap
  have hdiff : Integrable
      (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) => f (p.1 - b • p.2) - f p.1)
      (volume.prod η) := hkernel.sub (hf.comp_fst η)
  calc
    _ ≤ ∫ x, (∫ g, ‖f (x - b • g) - f x‖ ∂η) := by
      apply integral_mono_ae ((densityApproximationAverage_integrable n η f hm hf b).sub hf).norm
        hdiff.integral_norm_prod_left
      filter_upwards [hkernel.prod_right_ae] with x hx
      simp only [Pi.sub_apply]
      have heq : (∫ g, f (x - b • g) - f x ∂η) = densityApproximationAverage n η f b x - f x := by
        rw [integral_sub hx (integrable_const (f x)), integral_const]
        simp only [probReal_univ, one_smul]
        rfl
      rw [← heq]
      exact norm_integral_le_integral_norm _
    _ = _ := integral_integral_swap hdiff.norm

theorem densityApproximationAverage_L1_tendsto (n : ℕ)
    (η : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure η]
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hm : Measurable f)
    (hf : Integrable f (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    Tendsto (fun b : ℝ => ∫ x, ‖densityApproximationAverage n η f b x - f x‖)
      (𝓝 0) (𝓝 0) := by
  apply squeeze_zero (fun b => integral_nonneg fun x => norm_nonneg _)
    (fun b => densityApproximationAverage_L1_error_le n η f hm hf b)
  exact densityApproximation_averaged_translation_L1_tendsto n η f hm hf

end AffineFKProof
