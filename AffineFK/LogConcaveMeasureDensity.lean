module

public import AffineFK.LogConcaveMeasureBalls
public import AffineFK.LogConcaveDensityFinite
public import AffineFK.FisherInformationMeasure
public import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# An actual log-concave density for an absolutely continuous probability

Closed-ball differentiation reuses Sébastien Gouëzel's Besicovitch development
in Mathlib. Its Radon--Nikodym reconstruction is due to Kexing Ying, Rémy
Degenne and contributors. The chosen density is the real value of the liminf
of the actual normalized ball masses. Positive finite total mass ensures that
this log-concave liminf is finite at every point, rather than merely almost
everywhere. No bounds on the masses of the approximating functions are used.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory Filter Metric Set
open scoped ENNReal Topology

theorem logConcaveBallDensity_ae_tendsto_rnDeriv (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsFiniteMeasure ν] :
    ∀ᵐ x ∂volume,
      Tendsto (fun k : ℕ => logConcaveBallDensity n ν (1 / ((k : ℝ) + 1)) x)
        atTop (𝓝 (ν.rnDeriv volume x)) := by
  have hr : Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) atTop (𝓝[>] (0 : ℝ)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨tendsto_one_div_add_atTop_nhds_zero_nat, ?_⟩
    exact Eventually.of_forall (fun k => by simp only [mem_Ioi]; positivity)
  exact (Besicovitch.ae_tendsto_rnDeriv ν volume).mono (fun _ hx => hx.comp hr)

theorem logConcaveMeasure_exists_density (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (hν : IsLogConcaveMeasure n ν) (hac : ν ≪ volume) :
    ∃ ρ : EuclideanSpace ℝ (Fin n) → ℝ,
      Measurable ρ ∧ (∀ x, 0 ≤ ρ x) ∧ ν = densityMeasure n ρ ∧
        LogConcaveDensity (fun x => ENNReal.ofReal (ρ x)) ∧
        ρ =ᵐ[volume] canonicalLebesgueDensity n ν := by
  let f (k : ℕ) := logConcaveBallDensity n ν (1 / ((k : ℝ) + 1))
  let g : EuclideanSpace ℝ (Fin n) → ℝ≥0∞ := fun x => liminf (fun k => f k x) atTop
  have hf (k : ℕ) : Measurable (f k) := logConcaveBallDensity_measurable n ν _
  have hflc (k : ℕ) : LogConcaveDensity (f k) :=
    logConcaveBallDensity_logConcave n ν hν (by positivity)
  have hg : Measurable g := measurable_logConcave_liminf f hf
  have hglc : LogConcaveDensity g := logConcaveDensity_liminf f hflc
  have hAE : g =ᵐ[volume] ν.rnDeriv volume :=
    logConcave_liminf_ae_eq_of_ae_tendsto volume f _
      (logConcaveBallDensity_ae_tendsto_rnDeriv n ν)
  have hmass : (∫⁻ x, g x) = 1 := by
    rw [lintegral_congr_ae hAE, Measure.lintegral_rnDeriv hac, measure_univ]
  have hfinite (x) : g x ≠ ∞ := logConcaveDensity_ne_top_of_finite_mass n g hg hglc
    (by rw [hmass]; exact one_ne_zero) (by rw [hmass]; exact ENNReal.one_ne_top) x
  let ρ : EuclideanSpace ℝ (Fin n) → ℝ := fun x => (g x).toReal
  have hrep : (fun x => ENNReal.ofReal (ρ x)) = g :=
    funext fun x => ENNReal.ofReal_toReal (hfinite x)
  refine ⟨ρ, hg.ennreal_toReal, fun _ => ENNReal.toReal_nonneg, ?_, ?_, ?_⟩
  · symm
    calc
      densityMeasure n ρ = volume.withDensity (ν.rnDeriv volume) := by
        apply withDensity_congr_ae
        rw [hrep]
        exact hAE
      _ = ν := Measure.withDensity_rnDeriv_eq ν volume hac
  · rwa [hrep]
  · exact hAE.mono fun _ hx => congrArg ENNReal.toReal hx

theorem finite_relativeFisher_logConcaveMeasure_exists_density (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (hν : IsLogConcaveMeasure n ν) (hI : relativeFisherMeasure n ν ≠ ∞) :
    ∃ ρ : EuclideanSpace ℝ (Fin n) → ℝ,
      Measurable ρ ∧ (∀ x, 0 ≤ ρ x) ∧ ν = densityMeasure n ρ ∧
        LogConcaveDensity (fun x => ENNReal.ofReal (ρ x)) ∧
        ρ =ᵐ[volume] canonicalLebesgueDensity n ν := by
  have hac : ν ≪ volume := by
    by_contra h
    exact hI (by simp only [relativeFisherMeasure, h, ↓reduceIte])
  exact logConcaveMeasure_exists_density n ν hν hac

end AffineFKProof
