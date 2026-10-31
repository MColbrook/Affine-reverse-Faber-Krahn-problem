module

public import AffineFK.BrownianBridgeCoefficients
public import AffineFK.StandardGaussianDensity
public import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# From the literal logarithmic Gaussian profile to the coefficient event

The real logarithm at zero is never used to infer positive mass.
Positivity follows instead from the actual positive Gaussian density and
the nonempty interior of the body. This file proves the exact probability
estimate for the actual independent coefficient space; it does not yet
identify its Schauder series with a Brownian bridge or a killed heat kernel.
The measure equivalence reuses Mathlib's with-density absolute-continuity
theorem (Mathlib contributors, Apache-2.0).
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Pointwise

theorem volume_absolutelyContinuous_stdGaussian (n : ℕ) :
    (volume : Measure (EuclideanSpace ℝ (Fin n))) ≪
      stdGaussian (EuclideanSpace ℝ (Fin n)) := by
  rw [stdGaussian_eq_densityMeasure]
  exact withDensity_absolutelyContinuous'
    (standardGaussianDensity_smooth n).continuous.measurable.ennreal_ofReal.aemeasurable
    (Eventually.of_forall fun x => ne_of_gt (ENNReal.ofReal_pos.mpr (standardGaussianDensity_pos n x)))

theorem stdGaussian_pos_of_nonempty_interior (n : ℕ)
    (D : Set (EuclideanSpace ℝ (Fin n))) (hD : (interior D).Nonempty) :
    0 < stdGaussian (EuclideanSpace ℝ (Fin n)) D := by
  exact bot_lt_iff_ne_bot.mpr (fun h =>
    (Measure.measure_pos_of_nonempty_interior volume hD).ne'
      (volume_absolutelyContinuous_stdGaussian n h))

theorem gaussian_profile_exp_of_log (n : ℕ)
    (D : Set (EuclideanSpace ℝ (Fin n))) (hD : (interior D).Nonempty)
    (p A t : ℝ) (ht : 0 < t)
    (hlog : -Real.log ((stdGaussian (EuclideanSpace ℝ (Fin n))) (t • D)).toReal ≤
      A * t ^ (-p)) :
    ENNReal.ofReal (Real.exp (-A * t ^ (-p))) ≤
      stdGaussian (EuclideanSpace ℝ (Fin n)) (t • D) := by
  have hinterior : (interior (t • D)).Nonempty := by
    rw [interior_smul₀ (ne_of_gt ht)]
    exact hD.smul_set
  have hm := stdGaussian_pos_of_nonempty_interior n (t • D) hinterior
  have hmr : 0 < ((stdGaussian (EuclideanSpace ℝ (Fin n))) (t • D)).toReal :=
    ENNReal.toReal_pos hm.ne' (measure_ne_top _ _)
  have hreal : Real.exp (-A * t ^ (-p)) ≤
      ((stdGaussian (EuclideanSpace ℝ (Fin n))) (t • D)).toReal := by
    rw [← Real.exp_log hmr]
    apply Real.exp_le_exp.mpr
    linarith
  exact (ENNReal.ofReal_le_ofReal hreal).trans ENNReal.ofReal_toReal_le

/-- Exact source-facing coefficient probability bound, with the logarithmic
profile as stated in the manuscript and no assumed positivity of its mass. -/
theorem bridgeCoefficientEvent_probability_lower_of_log
    (n : ℕ) (D : Set (EuclideanSpace ℝ (Fin n))) (hD : MeasurableSet D)
    (hinterior : (interior D).Nonempty)
    (p a A : ℝ) (hp : 2 < p) (ha : 1 / p < a) (hupper : a < 1 / 2) (hA : 0 ≤ A)
    (hprofile : ∀ t : ℝ, 1 ≤ t →
      -Real.log ((stdGaussian (EuclideanSpace ℝ (Fin n))) (t • D)).toReal ≤ A * t ^ (-p)) :
    ENNReal.ofReal (Real.exp (-A / (1 - (2 : ℝ) ^ (1 - a * p)))) ≤
      bridgeCoefficientMeasure n (bridgeCoefficientEvent n D a) := by
  apply bridgeCoefficientEvent_probability_lower n D hD p a A hp ha hupper hA
  intro t ht
  exact gaussian_profile_exp_of_log n D hinterior p A t (by linarith) (hprofile t ht)

end AffineFKProof
