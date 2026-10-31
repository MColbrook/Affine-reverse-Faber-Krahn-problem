module

public import AffineFK.FisherInformationMeasure
public import AffineFK.OUDensityEntropyInitialLimit

/-!
# Actual Lebesgue-density L1 convergence at the OU initial endpoint

Changing between equivalent positive Gaussian and Lebesgue reference
measures preserves the L1 distance of the actual Radon--Nikodym densities.
The proved Gaussian-reference endpoint therefore gives the actual
Lebesgue-density endpoint. No continuity of the original density is used.
Mathlib's Radon--Nikodym chain rule retains its original attribution.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory Filter
open scoped Topology ENNReal

theorem gaussian_rnDeriv_eq_canonical_density_div (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsFiniteMeasure ν] :
    (fun x => (ν.rnDeriv (stdGaussian (EuclideanSpace ℝ (Fin n))) x).toReal) =ᵐ[volume]
      fun x => canonicalLebesgueDensity n ν x / standardGaussianDensity n x := by
  have h := Measure.rnDeriv_withDensity_right ν volume
    (f := fun x => ENNReal.ofReal (standardGaussianDensity n x))
    (standardGaussianDensity_smooth n).continuous.measurable.ennreal_ofReal.aemeasurable
    (Eventually.of_forall fun x => (ENNReal.ofReal_pos.mpr (standardGaussianDensity_pos n x)).ne')
    (Eventually.of_forall fun _ => ENNReal.ofReal_ne_top)
  rw [show volume.withDensity (fun x => ENNReal.ofReal (standardGaussianDensity n x)) =
    stdGaussian (EuclideanSpace ℝ (Fin n)) from (stdGaussian_eq_densityMeasure n).symm] at h
  filter_upwards [h] with x hx
  rw [hx, ENNReal.toReal_mul, ENNReal.toReal_inv,
    ENNReal.toReal_ofReal (standardGaussianDensity_pos n x).le]
  change (standardGaussianDensity n x)⁻¹ * canonicalLebesgueDensity n ν x = _
  ring

theorem canonical_density_L1_eq_gaussian_RN (n : ℕ)
    (ν η : Measure (EuclideanSpace ℝ (Fin n))) [IsFiniteMeasure ν] [IsFiniteMeasure η] :
    (∫ x, ‖canonicalLebesgueDensity n ν x - canonicalLebesgueDensity n η x‖) =
      ∫ x, ‖(ν.rnDeriv (stdGaussian (EuclideanSpace ℝ (Fin n))) x).toReal -
        (η.rnDeriv (stdGaussian (EuclideanSpace ℝ (Fin n))) x).toReal‖
        ∂stdGaussian (EuclideanSpace ℝ (Fin n)) := by
  rw [stdGaussian_eq_densityMeasure n,
    density_integral_eq n (standardGaussianDensity n) (standardGaussianDensity_smooth n).continuous
      (fun x => (standardGaussianDensity_pos n x).le)]
  apply integral_congr_ae
  have hν := gaussian_rnDeriv_eq_canonical_density_div n ν
  have hη := gaussian_rnDeriv_eq_canonical_density_div n η
  rw [stdGaussian_eq_densityMeasure n] at hν hη
  filter_upwards [hν, hη] with x hx hy
  rw [hx, hy, ← sub_div, norm_div]
  simp only [Real.norm_eq_abs, abs_of_pos (standardGaussianDensity_pos n x)]
  field_simp [(standardGaussianDensity_pos n x).ne']

theorem ouInitial_clamped_canonical_density_L1_tendsto (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (hac : ν ≪ volume) :
    Tendsto (fun t : ℝ => ∫ x,
      ‖canonicalLebesgueDensity n (ouInitialLaw n ν (max t 0)) x - canonicalLebesgueDensity n ν x‖)
      (𝓝 0) (𝓝 0) := by
  simpa only [canonical_density_L1_eq_gaussian_RN] using
    ouInitial_clamped_RN_L1_tendsto n ν
      (hac.trans (ouInitial_volume_absolutelyContinuous_stdGaussian n))

theorem ouInitial_canonical_density_L1_tendsto (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (hac : ν ≪ volume) :
    Tendsto (fun t : ℝ => ∫ x,
      ‖canonicalLebesgueDensity n (ouInitialLaw n ν t) x - canonicalLebesgueDensity n ν x‖)
      (𝓝[>] 0) (𝓝 0) := by
  apply ((ouInitial_clamped_canonical_density_L1_tendsto n ν hac).mono_left nhdsWithin_le_nhds).congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  rw [max_eq_left (le_of_lt ht)]

end AffineFKProof
