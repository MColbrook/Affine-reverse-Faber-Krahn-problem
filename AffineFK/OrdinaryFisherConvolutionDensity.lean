module

public import AffineFK.DensityRatio
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Group.LIntegral

/-!
# The actual density after convolution with an arbitrary probability law

An extended nonnegative kernel is used first, so that singular original
laws and possible infinite pointwise values are retained. Its total mass
is one. It is therefore finite almost everywhere, and its real version is
the genuine Bochner convolution integral almost everywhere. No pointwise
integrability or boundedness of the input density is assumed.

Tonelli and product integration are Mathlib results of Floris van Doorn;
the translation substitution is Mathlib's Haar-invariance theorem.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory
open scoped ENNReal

def ordinaryFisherConvolutionDensityENNReal (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n)))
    (ρ : EuclideanSpace ℝ (Fin n) → ℝ) (z : EuclideanSpace ℝ (Fin n)) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal (ρ (z - x)) ∂ν

def ordinaryFisherConvolutionDensity (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n)))
    (ρ : EuclideanSpace ℝ (Fin n) → ℝ) (z : EuclideanSpace ℝ (Fin n)) : ℝ :=
  (ordinaryFisherConvolutionDensityENNReal n ν ρ z).toReal

theorem ordinaryFisherConvolutionDensityENNReal_measurable (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [SFinite ν]
    (ρ : EuclideanSpace ℝ (Fin n) → ℝ) (hρ : Measurable ρ) :
    Measurable (ordinaryFisherConvolutionDensityENNReal n ν ρ) := by
  apply Measurable.lintegral_prod_right
  exact (hρ.comp (measurable_fst.sub measurable_snd)).ennreal_ofReal

theorem ordinaryFisherConvolutionDensityENNReal_law (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (ρ : EuclideanSpace ℝ (Fin n) → ℝ) (hρ : Measurable ρ)
    [IsProbabilityMeasure (densityMeasure n ρ)] :
    (ν.prod (densityMeasure n ρ)).map (fun p => p.1 + p.2) =
      volume.withDensity (ordinaryFisherConvolutionDensityENNReal n ν ρ) := by
  apply Measure.ext_of_lintegral
  intro f hf
  let K : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) → ℝ≥0∞ :=
    fun p => ENNReal.ofReal (ρ (p.2 - p.1)) * f p.2
  have hK : Measurable K :=
    (hρ.comp (measurable_snd.sub measurable_fst)).ennreal_ofReal.mul (hf.comp measurable_snd)
  rw [lintegral_map hf (by fun_prop),
    lintegral_prod (fun p => f (p.1 + p.2))
      (hf.comp (measurable_fst.add measurable_snd)).aemeasurable]
  calc
    _ = ∫⁻ x, ∫⁻ z, K (x, z) ∂volume ∂ν := by
      apply lintegral_congr
      intro x
      rw [densityMeasure, lintegral_withDensity_eq_lintegral_mul _ hρ.ennreal_ofReal
        (g := fun y => f (x + y)) (hf.comp (measurable_const.add measurable_id))]
      calc
        _ = ∫⁻ y, K (x, x + y) := by
          apply lintegral_congr
          intro y
          simp only [K, add_sub_cancel_left, Pi.mul_apply]
        _ = _ := lintegral_add_left_eq_self (fun z => K (x, z)) x
    _ = ∫⁻ z, ∫⁻ x, K (x, z) ∂ν ∂volume := lintegral_lintegral_swap hK.aemeasurable
    _ = ∫⁻ z, ordinaryFisherConvolutionDensityENNReal n ν ρ z * f z := by
      apply lintegral_congr
      intro z
      change (∫⁻ x, ENNReal.ofReal (ρ (z - x)) * f z ∂ν) =
        (∫⁻ x, ENNReal.ofReal (ρ (z - x)) ∂ν) * f z
      exact lintegral_mul_const _ ((hρ.comp (measurable_const.sub measurable_id)).ennreal_ofReal)
    _ = _ := (lintegral_withDensity_eq_lintegral_mul _
      (ordinaryFisherConvolutionDensityENNReal_measurable n ν ρ hρ) hf).symm

theorem ordinaryFisherConvolutionDensity_mass_finite (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (ρ : EuclideanSpace ℝ (Fin n) → ℝ) (hρ : Measurable ρ)
    [IsProbabilityMeasure (densityMeasure n ρ)] :
    (∫⁻ z, ordinaryFisherConvolutionDensityENNReal n ν ρ z) = 1 ∧
    (∀ᵐ z ∂volume, ordinaryFisherConvolutionDensityENNReal n ν ρ z < ∞) := by
  have hlaw := ordinaryFisherConvolutionDensityENNReal_law n ν ρ hρ
  have hm : (∫⁻ z, ordinaryFisherConvolutionDensityENNReal n ν ρ z) = 1 := by
    have hmass := congrArg (fun μ : Measure (EuclideanSpace ℝ (Fin n)) => μ Set.univ) hlaw
    simpa only [measure_univ, withDensity_apply _ MeasurableSet.univ, setLIntegral_univ] using hmass.symm
  exact ⟨hm, ae_lt_top (ordinaryFisherConvolutionDensityENNReal_measurable n ν ρ hρ)
    (by rw [hm]; exact ENNReal.one_ne_top)⟩

theorem ordinaryFisherConvolutionDensity_law (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (ρ : EuclideanSpace ℝ (Fin n) → ℝ) (hρ : Measurable ρ)
    [IsProbabilityMeasure (densityMeasure n ρ)] :
    (ν.prod (densityMeasure n ρ)).map (fun p => p.1 + p.2) =
      densityMeasure n (ordinaryFisherConvolutionDensity n ν ρ) := by
  rw [ordinaryFisherConvolutionDensityENNReal_law n ν ρ hρ, densityMeasure]
  apply withDensity_congr_ae
  filter_upwards [(ordinaryFisherConvolutionDensity_mass_finite n ν ρ hρ).2] with z hz
  exact (ENNReal.ofReal_toReal hz.ne).symm

theorem ordinaryFisherConvolutionDensity_integral_ae (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (ρ : EuclideanSpace ℝ (Fin n) → ℝ) (hρ : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x)
    [IsProbabilityMeasure (densityMeasure n ρ)] :
    ∀ᵐ z ∂volume, Integrable (fun x => ρ (z - x)) ν ∧
      ordinaryFisherConvolutionDensity n ν ρ z = ∫ x, ρ (z - x) ∂ν := by
  filter_upwards [(ordinaryFisherConvolutionDensity_mass_finite n ν ρ hρ).2] with z hz
  have hi : Integrable (fun x => ρ (z - x)) ν :=
    (lintegral_ofReal_ne_top_iff_integrable
      (hρ.comp (measurable_const.sub measurable_id)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => hρ0 (z - x))).mp hz.ne
  refine ⟨hi, ?_⟩
  have heq := ofReal_integral_eq_lintegral_ofReal hi
    (Filter.Eventually.of_forall fun x => hρ0 (z - x))
  change (∫⁻ x, ENNReal.ofReal (ρ (z - x)) ∂ν).toReal = _
  rw [← heq, ENNReal.toReal_ofReal (integral_nonneg fun x => hρ0 (z - x))]

end AffineFKProof
