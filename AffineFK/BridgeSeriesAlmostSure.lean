module

public import AffineFK.BridgeSeriesSurvival
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
public import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli

/-!
# Almost-sure convergence of the actual Gaussian Schauder series

Gaussian eighth moments and the first Borel–Cantelli lemma control all
coefficients in each dyadic level. This is intended to identify the
already constructed continuous series law; no Brownian-law equality or
desired covariance is assumed. Moment existence and Markov/Borel–Cantelli
are reused from Mathlib (Mathlib contributors, Apache-2.0).
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Pointwise BigOperators Topology

def bridgeGaussianEighthMoment (n : ℕ) : ℝ≥0∞ :=
  ∫⁻ x : EuclideanSpace ℝ (Fin n), (ENNReal.ofReal ‖x‖) ^ 8
    ∂stdGaussian (EuclideanSpace ℝ (Fin n))

theorem bridgeGaussianEighthMoment_ne_top (n : ℕ) : bridgeGaussianEighthMoment n ≠ ∞ := by
  have hLp : MemLp (id : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) 8
      (stdGaussian (EuclideanSpace ℝ (Fin n))) :=
    IsGaussian.hasGaussianLaw_id.memLp (by norm_num)
  have hint : Integrable (fun x : EuclideanSpace ℝ (Fin n) => ‖x‖ ^ 8)
      (stdGaussian (EuclideanSpace ℝ (Fin n))) := hLp.integrable_norm_pow'
  unfold bridgeGaussianEighthMoment
  simp_rw [← ENNReal.ofReal_pow (norm_nonneg _) 8]
  rw [← ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun x => by positivity)]
  exact ENNReal.ofReal_ne_top

def bridgeCoefficientMomentBad (n j : ℕ) (k : Fin (2 ^ j)) :
    Set (∀ j : ℕ, Fin (2 ^ j) → EuclideanSpace ℝ (Fin n)) :=
  {ω | ENNReal.ofReal ((2 : ℝ) ^ (2 * j)) ≤ (ENNReal.ofReal ‖ω j k‖) ^ 8}

theorem bridgeCoefficientMomentBad_bound (n j : ℕ) (k : Fin (2 ^ j)) :
    bridgeCoefficientMeasure n (bridgeCoefficientMomentBad n j k) ≤
      bridgeGaussianEighthMoment n / ENNReal.ofReal ((2 : ℝ) ^ (2 * j)) := by
  have hm : AEMeasurable
      (fun ω : ∀ j : ℕ, Fin (2 ^ j) → EuclideanSpace ℝ (Fin n) =>
        (ENNReal.ofReal ‖ω j k‖) ^ 8) (bridgeCoefficientMeasure n) :=
    (show Measurable (fun ω : ∀ j : ℕ, Fin (2 ^ j) → EuclideanSpace ℝ (Fin n) =>
      (ENNReal.ofReal ‖ω j k‖) ^ 8) by fun_prop).aemeasurable
  have h := meas_ge_le_lintegral_div hm
    (show ENNReal.ofReal ((2 : ℝ) ^ (2 * j)) ≠ 0 by positivity)
    (show ENNReal.ofReal ((2 : ℝ) ^ (2 * j)) ≠ ∞ by finiteness)
  have hlaw := (bridgeCoefficientMeasure_hasLaw n j k).lintegral_comp
    (f := fun x : EuclideanSpace ℝ (Fin n) => (ENNReal.ofReal ‖x‖) ^ 8) (by fun_prop)
  simpa only [bridgeCoefficientMomentBad, hlaw, bridgeGaussianEighthMoment] using h

def bridgeLevelMomentBad (n j : ℕ) :
    Set (∀ j : ℕ, Fin (2 ^ j) → EuclideanSpace ℝ (Fin n)) :=
  ⋃ k : Fin (2 ^ j), bridgeCoefficientMomentBad n j k

theorem bridgeMoment_geometric_factor (j : ℕ) :
    (2 : ℝ) ^ j / (2 : ℝ) ^ (2 * j) = (1 / 2 : ℝ) ^ j := by
  rw [Nat.mul_comm 2 j, pow_mul, one_div_pow]
  field_simp

theorem bridgeLevelMomentBad_bound (n j : ℕ) :
    bridgeCoefficientMeasure n (bridgeLevelMomentBad n j) ≤
      ENNReal.ofReal ((1 / 2 : ℝ) ^ j) * bridgeGaussianEighthMoment n := by
  calc
    _ ≤ ∑' k : Fin (2 ^ j), bridgeCoefficientMeasure n (bridgeCoefficientMomentBad n j k) :=
      measure_iUnion_le _
    _ ≤ ∑' _k : Fin (2 ^ j), bridgeGaussianEighthMoment n /
        ENNReal.ofReal ((2 : ℝ) ^ (2 * j)) :=
      ENNReal.tsum_le_tsum (fun k => bridgeCoefficientMomentBad_bound n j k)
    _ = ((2 ^ j : ℕ) : ℝ≥0∞) * (bridgeGaussianEighthMoment n /
        ENNReal.ofReal ((2 : ℝ) ^ (2 * j))) := by
      simp [tsum_fintype, nsmul_eq_mul]
    _ = (ENNReal.ofReal ((2 : ℝ) ^ j) / ENNReal.ofReal ((2 : ℝ) ^ (2 * j))) *
        bridgeGaussianEighthMoment n := by
      simp [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc, ENNReal.ofReal_pow]
    _ = ENNReal.ofReal ((1 / 2 : ℝ) ^ j) * bridgeGaussianEighthMoment n := by
      rw [← ENNReal.ofReal_div_of_pos (by positivity), bridgeMoment_geometric_factor]

theorem bridgeLevelMomentBad_summable_measure (n : ℕ) :
    (∑' j, bridgeCoefficientMeasure n (bridgeLevelMomentBad n j)) ≠ ∞ := by
  apply ne_top_of_le_ne_top _ (ENNReal.tsum_le_tsum (fun j => bridgeLevelMomentBad_bound n j))
  simp_rw [ENNReal.ofReal_pow (by norm_num : 0 ≤ (1 / 2 : ℝ))]
  rw [ENNReal.tsum_mul_right, ENNReal.tsum_geometric]
  have hhalf : ENNReal.ofReal (1 / 2 : ℝ) < 1 := by
    exact ENNReal.ofReal_lt_one.mpr (by norm_num)
  have hsub : 1 - ENNReal.ofReal (1 / 2 : ℝ) ≠ 0 := (tsub_pos_iff_lt.mpr hhalf).ne'
  exact ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr hsub) (bridgeGaussianEighthMoment_ne_top n)

end AffineFKProof
