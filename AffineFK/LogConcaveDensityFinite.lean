module

public import AffineFK.EuclideanLogConcavity
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Pointwise finiteness of an integrable log-concave density

A measurable log-concave extended density of strictly positive finite mass
is finite everywhere. The midpoint affine map preserves null sets by
Mathlib's Haar translation and nonzero-dilation theorems. This is the
additional step needed before taking the real representative of a
log-concave convolution; almost-everywhere finiteness alone would not
justify pointwise log-concavity of that representative.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory
open scoped ENNReal

theorem logConcaveDensity_ne_top_of_finite_mass (n : ℕ)
    (f : EuclideanSpace ℝ (Fin n) → ℝ≥0∞) (hf : Measurable f)
    (hlc : LogConcaveDensity f) (hpos : (∫⁻ x, f x) ≠ 0)
    (hfinite : (∫⁻ x, f x) ≠ ∞) (x : EuclideanSpace ℝ (Fin n)) :
    f x ≠ ∞ := by
  intro hx
  have hAE := ae_lt_top hf hfinite
  have hmid : ∀ᵐ y ∂volume, f ((1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y) < ∞ := by
    exact ((quasiMeasurePreserving_add_left volume ((1 / 2 : ℝ) • x)).comp
      (Measure.quasiMeasurePreserving_smul volume (by norm_num : (1 / 2 : ℝ) ≠ 0))).ae hAE
  have hz : f =ᵐ[volume] 0 := by
    filter_upwards [hmid] with y hy
    by_contra hy0
    have hb := hlc (1 / 2) (by norm_num) (by norm_num) x y
    have hpow : f y ^ (1 / 2 : ℝ) ≠ 0 := by
      exact mt (ENNReal.rpow_eq_zero_iff_of_pos (by norm_num)).mp hy0
    have htop : (∞ : ℝ≥0∞) ≤ f ((1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y) := by
      simpa only [hx, show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num,
        ENNReal.top_rpow_of_pos (by norm_num : (0 : ℝ) < 1 / 2),
        ENNReal.top_mul hpow] using hb
    exact (not_le_of_gt hy) htop
  exact hpos (by rw [lintegral_congr_ae hz]; simp)

end AffineFKProof
