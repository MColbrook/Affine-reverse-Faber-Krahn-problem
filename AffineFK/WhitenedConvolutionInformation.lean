module

public import AffineFK.WhitenedConvolutionIsotropy
public import AffineFK.FisherInformationMeasureIdentity

/-!
# The numerical relative-information bound after whitening

The ordinary-information inequality concerns the actual independent sum
and its invertible linear image. Its finite upper bound establishes
finiteness before any conversion to real numbers. Actual identity
covariance then gives the source's exact relative--ordinary relation.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory
open scoped ENNReal

theorem whitenedSumLaw_relativeFisher_bound (n : ℕ)
    (ν η : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν] [IsProbabilityMeasure η]
    (hX : MemLp (id : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) 2 ν)
    (hY : MemLp (id : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) 2 η)
    (hmeanX : ∀ i : Fin n, (∫ x : EuclideanSpace ℝ (Fin n), x i ∂ν) = 0)
    (hmeanY : ∀ i : Fin n, (∫ x : EuclideanSpace ℝ (Fin n), x i ∂η) = 0)
    (hPν : poincareConstant n ν ≤ 1) (hPη : poincareConstant n η ≤ 1)
    (α : ℝ) (hα : 0 < α) (hαone : α ≤ 1)
    (hcovX : ∀ i j : Fin n, (∫ x : EuclideanSpace ℝ (Fin n), x i * x j ∂ν) =
      if i = j then α else 0)
    (ell : ℝ) (hJη : ordinaryFisherMeasure n η ≠ ∞)
    (hJηbound : (ordinaryFisherMeasure n η).toReal ≤ 4 * ell + n) :
    ordinaryFisherMeasure n (whitenedSumLaw n ν η α) ≠ ∞ ∧
      (ordinaryFisherMeasure n (whitenedSumLaw n ν η α)).toReal ≤ 8 * ell + 2 * n ∧
      relativeFisherMeasure n (whitenedSumLaw n ν η α) ≠ ∞ ∧
      (relativeFisherMeasure n (whitenedSumLaw n ν η α)).toReal ≤ 8 * ell + n ∧
      relativeFisherMeasure n (whitenedSumLaw n ν η α) ≤ ENNReal.ofReal (8 * ell + n) := by
  let ζ := whitenedSumLaw n ν η α
  let : IsProbabilityMeasure ζ := whitenedSumLaw_isProbabilityMeasure n ν η α
  have hiso := whitenedSumLaw_isotropic n ν η hX hY hmeanX hmeanY hPη α hα hαone hcovX
  have hJ0 : 0 ≤ 4 * ell + n := ENNReal.toReal_nonneg.trans hJηbound
  have hJηenn : ordinaryFisherMeasure n η ≤ ENNReal.ofReal (4 * ell + n) := by
    rw [← ENNReal.ofReal_toReal hJη]
    exact ENNReal.ofReal_le_ofReal hJηbound
  have hJbound : ordinaryFisherMeasure n ζ ≤ ENNReal.ofReal (8 * ell + 2 * n) := by
    calc
      _ ≤ 2 * ordinaryFisherMeasure n η :=
        (whitenedSumLaw_poincare_fisher_bounds n ν η hY hmeanY hPν hPη α hα hαone).2
      _ ≤ 2 * ENNReal.ofReal (4 * ell + n) := mul_le_mul' le_rfl hJηenn
      _ = ENNReal.ofReal (8 * ell + 2 * n) := by
        rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by norm_num,
          ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
        congr 1
        ring
  have hJfin : ordinaryFisherMeasure n ζ ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hJbound
  have hJreal : (ordinaryFisherMeasure n ζ).toReal ≤ 8 * ell + 2 * n := by
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hJbound
    rw [ENNReal.toReal_ofReal (by linarith : 0 ≤ 8 * ell + 2 * n)] at h
    exact h
  have hsecond : Integrable (fun x : EuclideanSpace ℝ (Fin n) => ‖x‖ ^ 2) ζ :=
    (memLp_two_iff_integrable_sq_norm aestronglyMeasurable_id).mp hiso.1
  have hmoment : (∫ x : EuclideanSpace ℝ (Fin n), ‖x‖ ^ 2 ∂ζ) = n := by
    simp_rw [EuclideanSpace.real_norm_sq_eq]
    have hsqi (i : Fin n) : Integrable (fun x : EuclideanSpace ℝ (Fin n) => (x i) ^ 2) ζ :=
      (hiso.1.eval_piLp i).integrable_sq
    rw [integral_finsetSum Finset.univ fun i _ => hsqi i]
    have hi (i : Fin n) : (∫ x : EuclideanSpace ℝ (Fin n), (x i) ^ 2 ∂ζ) = 1 := by
      simpa only [pow_two, ite_true] using hiso.2.2 i i
    simp only [hi, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  have hI := fisherMeasure_unit_second_moment_identity n ζ hJfin hsecond hmoment
  have hIreal : (relativeFisherMeasure n ζ).toReal ≤ 8 * ell + n := by linarith [hI.2]
  refine ⟨hJfin, hJreal, hI.1, hIreal, ?_⟩
  rw [← ENNReal.ofReal_toReal hI.1]
  exact ENNReal.ofReal_le_ofReal hIreal

end AffineFKProof
