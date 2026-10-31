module

public import AffineFK.FisherInformationDensityCongruence
public import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym

/-!
# Fisher information as a function of the actual probability law

The canonical density is the real Radon--Nikodym derivative with respect
to Lebesgue volume. The measure informations are infinity off absolute
continuity and otherwise use the already defined Sobolev informations.
Reconstruction and almost-everywhere density congruence prove that these
are independent of a chosen measurable nonnegative density representative.

The Radon--Nikodym proofs reuse Mathlib's developments by Kexing Ying,
Remy Degenne and contributors (Apache-2.0).
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory
open scoped ENNReal Classical

/-- The real Radon--Nikodym density of the actual law relative to volume. -/
def canonicalLebesgueDensity (n : ℕ) (ν : Measure (EuclideanSpace ℝ (Fin n)))
    (x : EuclideanSpace ℝ (Fin n)) : ℝ := (ν.rnDeriv volume x).toReal

/-- Ordinary Sobolev Fisher information of a law; infinity if it has no density. -/
def ordinaryFisherMeasure (n : ℕ) (ν : Measure (EuclideanSpace ℝ (Fin n))) : ℝ≥0∞ :=
  if ν ≪ volume then fisherInformation n (canonicalLebesgueDensity n ν) else ∞

/-- Gaussian-relative Sobolev information of a law on the finite-moment domain. -/
def relativeFisherMeasure (n : ℕ) (ν : Measure (EuclideanSpace ℝ (Fin n))) : ℝ≥0∞ :=
  if ν ≪ volume then relativeFisherInformation n (canonicalLebesgueDensity n ν) else ∞

theorem canonicalLebesgueDensity_measurable (n : ℕ) (ν : Measure (EuclideanSpace ℝ (Fin n))) :
    Measurable (canonicalLebesgueDensity n ν) := (Measure.measurable_rnDeriv ν volume).ennreal_toReal

theorem canonicalLebesgueDensity_nonneg (n : ℕ) (ν : Measure (EuclideanSpace ℝ (Fin n)))
    (x : EuclideanSpace ℝ (Fin n)) : 0 ≤ canonicalLebesgueDensity n ν x := ENNReal.toReal_nonneg

theorem canonicalLebesgueDensity_reconstruct (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [SigmaFinite ν] (hac : ν ≪ volume) :
    densityMeasure n (canonicalLebesgueDensity n ν) = ν := by
  calc
    _ = volume.withDensity (ν.rnDeriv volume) := by
      apply withDensity_congr_ae
      filter_upwards [ν.rnDeriv_ne_top volume] with x hx
      exact ENNReal.ofReal_toReal hx
    _ = ν := Measure.withDensity_rnDeriv_eq ν volume hac

theorem canonicalLebesgueDensity_of_density (n : ℕ)
    (ρ : EuclideanSpace ℝ (Fin n) → ℝ) (hρ : Measurable ρ)
    (hρ0 : ∀ᵐ x ∂volume, 0 ≤ ρ x) :
    canonicalLebesgueDensity n (densityMeasure n ρ) =ᵐ[volume] ρ := by
  have h := Measure.rnDeriv_withDensity (volume : Measure (EuclideanSpace ℝ (Fin n))) hρ.ennreal_ofReal
  filter_upwards [h, hρ0] with x hx h0
  change (densityMeasure n ρ).rnDeriv volume x = ENNReal.ofReal (ρ x) at hx
  change ((densityMeasure n ρ).rnDeriv volume x).toReal = ρ x
  rw [hx, ENNReal.toReal_ofReal h0]

theorem ordinaryFisherMeasure_density (n : ℕ)
    (ρ : EuclideanSpace ℝ (Fin n) → ℝ) (hρ : Measurable ρ)
    (hρ0 : ∀ᵐ x ∂volume, 0 ≤ ρ x) :
    ordinaryFisherMeasure n (densityMeasure n ρ) = fisherInformation n ρ := by
  rw [ordinaryFisherMeasure, ite_eq_left (show densityMeasure n ρ ≪ volume from withDensity_absolutelyContinuous _ _)]
  exact fisherInformation_congr_ae n _ _ (canonicalLebesgueDensity_of_density n ρ hρ hρ0)

theorem relativeFisherMeasure_density (n : ℕ)
    (ρ : EuclideanSpace ℝ (Fin n) → ℝ) (hρ : Measurable ρ)
    (hρ0 : ∀ᵐ x ∂volume, 0 ≤ ρ x) :
    relativeFisherMeasure n (densityMeasure n ρ) = relativeFisherInformation n ρ := by
  rw [relativeFisherMeasure, ite_eq_left (show densityMeasure n ρ ≪ volume from withDensity_absolutelyContinuous _ _)]
  exact relativeFisherInformation_congr_ae n _ _ (canonicalLebesgueDensity_of_density n ρ hρ hρ0)

end AffineFKProof
