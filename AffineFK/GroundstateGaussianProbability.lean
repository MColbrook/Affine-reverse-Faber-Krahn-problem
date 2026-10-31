module

public import AffineFK.GroundstateGaussianEnergy

/-!
# The actual normalised Gaussian-weighted Dirichlet density

The mass is positive for every nonzero original H0^1 element because the
Gaussian multiplier is strictly positive. The resulting square density is
an actual probability measure, and its second moment is finite without
any moment or regularity assumption on the open set.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory TopologicalSpace
open scoped ENNReal

def gaussianGroundstateMass (n : ℕ) (U : Opens (EuclideanSpace ℝ (Fin n)))
    (ψ : dirichletSobolev n U) : ℝ :=
  ∫ x, (dirichletValue n U (gaussianDirichletFactor n U ψ) x) ^ 2

def gaussianGroundstateDensity (n : ℕ) (U : Opens (EuclideanSpace ℝ (Fin n)))
    (ψ : dirichletSobolev n U) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  (dirichletValue n U (gaussianDirichletFactor n U ψ) x) ^ 2 / gaussianGroundstateMass n U ψ

theorem gaussianDirichletFactor_injective (n : ℕ) (U : Opens (EuclideanSpace ℝ (Fin n))) :
    Function.Injective (gaussianDirichletFactor n U) := by
  intro ψ φ h
  apply dirichletValue_injective n U
  apply Lp.ext
  have hψ := gaussianDirichletFactor_value n U ψ
  have hφ := gaussianDirichletFactor_value n U φ
  rw [h] at hψ
  filter_upwards [hψ, hφ] with x hx hy
  exact mul_left_cancel₀ (groundstateGaussianFactor_pos n x).ne' (hx.symm.trans hy)

theorem gaussianGroundstateMass_pos (n : ℕ) (U : Opens (EuclideanSpace ℝ (Fin n)))
    (ψ : dirichletSobolev n U) (hψ : ψ ≠ 0) : 0 < gaussianGroundstateMass n U ψ := by
  have hv : gaussianDirichletFactor n U ψ ≠ 0 := by
    intro h
    apply hψ
    apply gaussianDirichletFactor_injective n U
    simpa only [map_zero] using h
  have hvalue : dirichletValue n U (gaussianDirichletFactor n U ψ) ≠ 0 := by
    intro h
    apply hv
    apply dirichletValue_injective n U
    simpa only [map_zero] using h
  have hnorm := sq_pos_of_pos (norm_pos_iff.mpr hvalue)
  simpa only [gaussianGroundstateMass, l2_norm_sq_integral, Real.norm_eq_abs, sq_abs] using hnorm

theorem gaussianGroundstateDensity_measurable (n : ℕ) (U : Opens (EuclideanSpace ℝ (Fin n)))
    (ψ : dirichletSobolev n U) : Measurable (gaussianGroundstateDensity n U ψ) :=
  ((Lp.stronglyMeasurable (dirichletValue n U (gaussianDirichletFactor n U ψ))).measurable.pow_const 2).div_const _

theorem gaussianGroundstateDensity_nonneg (n : ℕ) (U : Opens (EuclideanSpace ℝ (Fin n)))
    (ψ : dirichletSobolev n U) (x : EuclideanSpace ℝ (Fin n)) :
    0 ≤ gaussianGroundstateDensity n U ψ x := by
  unfold gaussianGroundstateDensity gaussianGroundstateMass
  exact div_nonneg (sq_nonneg _) (integral_nonneg fun _ => sq_nonneg _)

theorem gaussianGroundstateDensity_integrable (n : ℕ) (U : Opens (EuclideanSpace ℝ (Fin n)))
    (ψ : dirichletSobolev n U) : Integrable (gaussianGroundstateDensity n U ψ) := by
  have hf := Lp.memLp (dirichletValue n U (gaussianDirichletFactor n U ψ))
  have hi : Integrable (fun x => (dirichletValue n U (gaussianDirichletFactor n U ψ) x) ^ 2) := by
    simpa only [Real.norm_eq_abs, sq_abs] using
      (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mp hf
  exact hi.div_const _

theorem gaussianGroundstateDensity_integral (n : ℕ) (U : Opens (EuclideanSpace ℝ (Fin n)))
    (ψ : dirichletSobolev n U) (hψ : ψ ≠ 0) :
    (∫ x, gaussianGroundstateDensity n U ψ x) = 1 := by
  change (∫ x, (dirichletValue n U (gaussianDirichletFactor n U ψ) x) ^ 2 /
    gaussianGroundstateMass n U ψ) = 1
  rw [integral_div]
  exact div_self (gaussianGroundstateMass_pos n U ψ hψ).ne'

theorem gaussianGroundstateDensity_probability (n : ℕ) (U : Opens (EuclideanSpace ℝ (Fin n)))
    (ψ : dirichletSobolev n U) (hψ : ψ ≠ 0) :
    IsProbabilityMeasure (densityMeasure n (gaussianGroundstateDensity n U ψ)) := by
  refine ⟨?_⟩
  rw [densityMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (gaussianGroundstateDensity_integrable n U ψ)
      (ae_of_all volume (gaussianGroundstateDensity_nonneg n U ψ)),
    gaussianGroundstateDensity_integral n U ψ hψ, ENNReal.ofReal_one]

set_option maxHeartbeats 600000 in
theorem gaussianGroundstateDensity_second_moment (n : ℕ) (U : Opens (EuclideanSpace ℝ (Fin n)))
    (ψ : dirichletSobolev n U) :
    Integrable (fun x : EuclideanSpace ℝ (Fin n) => ‖x‖ ^ 2)
      (densityMeasure n (gaussianGroundstateDensity n U ψ)) ∧
    (∫ x, ‖x‖ ^ 2 ∂densityMeasure n (gaussianGroundstateDensity n U ψ)) =
      (∫ x, ‖x‖ ^ 2 * (dirichletValue n U (gaussianDirichletFactor n U ψ) x) ^ 2) /
        gaussianGroundstateMass n U ψ := by
  have hm0 := groundstate_gaussian_moment_integrable n volume (dirichletValue n U ψ)
    (Lp.memLp (dirichletValue n U ψ))
  have hm : Integrable (fun x => ‖x‖ ^ 2 * (dirichletValue n U (gaussianDirichletFactor n U ψ) x) ^ 2) := by
    apply hm0.congr
    filter_upwards [gaussianDirichletFactor_value n U ψ] with x hx
    rw [hx]
  have hq := (gaussianGroundstateDensity_measurable n U ψ).ennreal_ofReal
  have hfinite : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      ENNReal.ofReal (gaussianGroundstateDensity n U ψ x) < ∞ := ae_of_all volume fun _ => ENNReal.ofReal_lt_top
  have hprod : Integrable (fun x => gaussianGroundstateDensity n U ψ x * ‖x‖ ^ 2) := by
    have hi := hm.div_const (gaussianGroundstateMass n U ψ)
    convert hi using 1
    funext x
    dsimp [gaussianGroundstateDensity]
    ring
  constructor
  · rw [densityMeasure, integrable_withDensity_iff_integrable_smul' hq hfinite]
    simpa only [ENNReal.toReal_ofReal (gaussianGroundstateDensity_nonneg n U ψ _), smul_eq_mul] using hprod
  · calc
      _ = ∫ x, (ENNReal.ofReal (gaussianGroundstateDensity n U ψ x)).toReal • ‖x‖ ^ 2 :=
        integral_withDensity_eq_integral_toReal_smul hq hfinite
          (fun x : EuclideanSpace ℝ (Fin n) => ‖x‖ ^ 2)
      _ = ∫ x, (‖x‖ ^ 2 * (dirichletValue n U (gaussianDirichletFactor n U ψ) x) ^ 2) /
          gaussianGroundstateMass n U ψ := by
        apply integral_congr_ae
        exact ae_of_all volume fun x => by
          dsimp only
          change (ENNReal.ofReal (gaussianGroundstateDensity n U ψ x)).toReal * ‖x‖ ^ 2 = _
          calc
            _ = gaussianGroundstateDensity n U ψ x * ‖x‖ ^ 2 :=
              congrArg (fun p : ℝ => p * ‖x‖ ^ 2)
                (ENNReal.toReal_ofReal (gaussianGroundstateDensity_nonneg n U ψ x))
            _ = _ := by dsimp [gaussianGroundstateDensity]; ring
      _ = _ := integral_div _ _

end AffineFKProof
