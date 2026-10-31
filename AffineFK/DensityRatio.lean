module

public import AffineFK.LogDensityIntegration
public import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym

/-!
# The smooth density-ratio representative

For positive continuous reference density k, rho/k is an actual
Radon--Nikodym representative. Derivatives below apply to that smooth
representative; no derivative of an arbitrary almost-everywhere version
of Mathlib's rnDeriv is asserted.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory
open scoped ContDiff

theorem densityMeasure_withDensity_ratio
    (n : ℕ) (ρ k : EuclideanSpace ℝ (Fin n) → ℝ)
    (hρ : Continuous ρ) (hk : Continuous k) (hkpos : ∀ x, 0 < k x) :
    (densityMeasure n k).withDensity (fun x => ENNReal.ofReal (ρ x / k x)) = densityMeasure n ρ := by
  unfold densityMeasure
  change ((volume.withDensity fun x => ENNReal.ofReal (k x)).withDensity
    (fun x => ENNReal.ofReal ((ρ / k) x))) = _
  rw [← withDensity_mul volume hk.measurable.ennreal_ofReal
    (hρ.div hk (fun x => (hkpos x).ne')).measurable.ennreal_ofReal]
  apply withDensity_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    change ENNReal.ofReal (k x) * ENNReal.ofReal (ρ x / k x) = ENNReal.ofReal (ρ x)
    rw [← ENNReal.ofReal_mul (hkpos x).le]
    congr 1
    field_simp [(hkpos x).ne']

theorem densityMeasure_ratio_rnDeriv
    (n : ℕ) (ρ k : EuclideanSpace ℝ (Fin n) → ℝ)
    (hρ : Continuous ρ) (hk : Continuous k) (hkpos : ∀ x, 0 < k x)
    [IsProbabilityMeasure (densityMeasure n k)] :
    (densityMeasure n ρ).rnDeriv (densityMeasure n k) =ᵐ[densityMeasure n k]
      (fun x => ENNReal.ofReal (ρ x / k x)) := by
  have h := Measure.rnDeriv_withDensity (densityMeasure n k)
    (hρ.div hk (fun x => (hkpos x).ne')).measurable.ennreal_ofReal
  simp only [Pi.div_apply] at h
  rw [densityMeasure_withDensity_ratio n ρ k hρ hk hkpos] at h
  exact h

theorem gradient_log_density_ratio
    (n : ℕ) (ρ k : EuclideanSpace ℝ (Fin n) → ℝ)
    (hρ : ContDiff ℝ ∞ ρ) (hk : ContDiff ℝ ∞ k)
    (hρpos : ∀ x, 0 < ρ x) (hkpos : ∀ x, 0 < k x)
    (x : EuclideanSpace ℝ (Fin n)) :
    gradient (fun y => Real.log (ρ y / k y)) x =
      gradient (fun y => Real.log (ρ y)) x - gradient (fun y => Real.log (k y)) x := by
  have heq : (fun y => Real.log (ρ y / k y)) = (fun y => Real.log (ρ y) - Real.log (k y)) :=
    funext fun y => Real.log_div (hρpos y).ne' (hkpos y).ne'
  rw [heq]
  unfold gradient
  change (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm
    (fderiv ℝ ((fun y => Real.log (ρ y)) - (fun y => Real.log (k y))) x) = _
  rw [fderiv_sub ((hρ.log (fun y => (hρpos y).ne')).differentiable (by simp)).differentiableAt
    ((hk.log (fun y => (hkpos y).ne')).differentiable (by simp)).differentiableAt, map_sub]

end AffineFKProof
