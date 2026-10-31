module

public import AffineFK.DirichletGaussianIterationLiminf
public import AffineFK.LogConcaveDensityFinite

/-!
# A genuine finite-valued log-concave representative of an AE limit

The actual pointwise liminf is log-concave. Its square has the same
positive finite mass as the normalized AE limit, so the previously
proved finite-mass log-concavity theorem excludes infinity everywhere.
Taking its real value therefore preserves pointwise log-concavity and
agrees with the original real limit almost everywhere. No set-based
log-concave-measure equivalence or pointwise property of an arbitrary
Lp representative is assumed. All statements include dimension zero.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory Filter
open scoped ENNReal Topology

def logConcaveLiminfRepresentative {E : Type*}
    (f : ℕ → E → ℝ≥0∞) (x : E) : ℝ :=
  (liminf (fun k => f k x) atTop).toReal

theorem logConcaveDensity_ne_top_of_finite_square_mass (n : ℕ)
    (g : EuclideanSpace ℝ (Fin n) → ℝ≥0∞) (hg : Measurable g)
    (hlc : LogConcaveDensity g) (hpos : (∫⁻ x, g x ^ 2) ≠ 0)
    (hfinite : (∫⁻ x, g x ^ 2) ≠ ∞) (x : EuclideanSpace ℝ (Fin n)) :
    g x ≠ ∞ := by
  have hlc2 : LogConcaveDensity (fun y => g y ^ 2) := by
    simpa only [pow_two] using logConcaveDensity_mul g g hlc hlc
  have h2 := logConcaveDensity_ne_top_of_finite_mass n (fun y => g y ^ 2)
    (hg.pow_const 2) hlc2 hpos hfinite x
  intro hx
  exact h2 (by simp [hx])

theorem logConcave_real_representative_of_ae_tendsto (n : ℕ)
    (f : ℕ → EuclideanSpace ℝ (Fin n) → ℝ≥0∞)
    (hf : ∀ k, Measurable (f k)) (hlc : ∀ k, LogConcaveDensity (f k))
    (ψ : EuclideanSpace ℝ (Fin n) → ℝ)
    (hψnonneg : ∀ᵐ x ∂volume, 0 ≤ ψ x)
    (hψmass : (∫⁻ x, (ENNReal.ofReal (ψ x)) ^ 2) = 1)
    (hlim : ∀ᵐ x ∂volume,
      Tendsto (fun k => f k x) atTop (𝓝 (ENNReal.ofReal (ψ x)))) :
    Measurable (logConcaveLiminfRepresentative f) ∧
      (∀ x, 0 ≤ logConcaveLiminfRepresentative f x) ∧
      LogConcaveDensity (fun x => ENNReal.ofReal (logConcaveLiminfRepresentative f x)) ∧
      logConcaveLiminfRepresentative f =ᵐ[volume] ψ := by
  let g : EuclideanSpace ℝ (Fin n) → ℝ≥0∞ :=
    fun x => liminf (fun k => f k x) atTop
  have hg : Measurable g := measurable_logConcave_liminf f hf
  have hgLC : LogConcaveDensity g := logConcaveDensity_liminf f hlc
  have hAE : g =ᵐ[volume] fun x => ENNReal.ofReal (ψ x) :=
    logConcave_liminf_ae_eq_of_ae_tendsto volume f _ hlim
  have hmass : (∫⁻ x, g x ^ 2) = 1 := by
    apply (lintegral_congr_ae ?_).trans hψmass
    filter_upwards [hAE] with x hx
    exact congrArg (fun a : ℝ≥0∞ => a ^ 2) hx
  have hfinite (x) : g x ≠ ∞ :=
    logConcaveDensity_ne_top_of_finite_square_mass n g hg hgLC
      (by rw [hmass]; exact one_ne_zero) (by rw [hmass]; exact ENNReal.one_ne_top) x
  have hrep (x) : ENNReal.ofReal (logConcaveLiminfRepresentative f x) = g x :=
    ENNReal.ofReal_toReal (hfinite x)
  refine ⟨hg.ennreal_toReal, fun _ => ENNReal.toReal_nonneg, ?_, ?_⟩
  · have heq : (fun x => ENNReal.ofReal (logConcaveLiminfRepresentative f x)) = g :=
      funext hrep
    rw [heq]
    exact hgLC
  · filter_upwards [hAE, hψnonneg] with x hx hpos
    calc
      logConcaveLiminfRepresentative f x =
          (ENNReal.ofReal (logConcaveLiminfRepresentative f x)).toReal :=
        (ENNReal.toReal_ofReal ENNReal.toReal_nonneg).symm
      _ = (ENNReal.ofReal (ψ x)).toReal := congrArg ENNReal.toReal ((hrep x).trans hx)
      _ = ψ x := ENNReal.toReal_ofReal hpos

theorem logConcaveLiminfRepresentative_even {E : Type*} [Neg E]
    (f : ℕ → E → ℝ≥0∞) (heven : ∀ k x, f k (-x) = f k x) (x : E) :
    logConcaveLiminfRepresentative f (-x) = logConcaveLiminfRepresentative f x := by
  have heq : (fun k => f k (-x)) = (fun k => f k x) := funext fun k => heven k x
  simp only [logConcaveLiminfRepresentative, heq]

end AffineFKProof
