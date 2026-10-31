module

public import AffineFK.PrekopaLeindlerStandard

/-!
# Prékopa--Leindler at the endpoints and log-concave marginals

The strict-weight inequality reuses Jonathan Ho's attributed proof through
PrekopaLeindlerStandard. The endpoint arguments and the marginal application
below retain extended nonnegative integrals, including zero and infinity.
Log-concavity is the usual pointwise weighted geometric-mean inequality.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory
open scoped ENNReal

theorem prekopa_leindler_weighted (d : ℕ) (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (f g h : (Fin (d + 1) → ℝ) → ℝ≥0∞)
    (hf : Measurable f) (hg : Measurable g) (hh : Measurable h)
    (hfg : ∀ x y, f x ^ (1 - t) * g y ^ t ≤ h ((1 - t) • x + t • y)) :
    (∫⁻ x, f x) ^ (1 - t) * (∫⁻ x, g x) ^ t ≤ ∫⁻ x, h x := by
  rcases ht.eq_or_lt with hzero | hpos
  · subst t
    simpa using lintegral_mono (fun x => by simpa using hfg x 0)
  rcases ht1.eq_or_lt with hone | hlt
  · subst t
    simpa using lintegral_mono (fun y => by simpa using hfg 0 y)
  exact prekopa_leindler_weighted_pos d t hpos hlt f g h hf hg hh hfg

theorem prekopa_leindler_weighted_all (n : ℕ) (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (f g h : (Fin n → ℝ) → ℝ≥0∞)
    (hf : Measurable f) (hg : Measurable g) (hh : Measurable h)
    (hfg : ∀ x y, f x ^ (1 - t) * g y ^ t ≤ h ((1 - t) • x + t • y)) :
    (∫⁻ x, f x) ^ (1 - t) * (∫⁻ x, g x) ^ t ≤ ∫⁻ x, h x := by
  cases n with
  | zero =>
    rw [Measure.volume_pi_eq_dirac (0 : Fin 0 → ℝ)]
    simpa only [lintegral_dirac,
      smul_zero, add_zero] using hfg 0 0
  | succ d => exact prekopa_leindler_weighted d t ht ht1 f g h hf hg hh hfg

/-- The pointwise definition of log-concavity for an extended nonnegative density. -/
def LogConcaveDensity {E : Type*} [AddCommMonoid E] [Module ℝ E]
    (f : E → ℝ≥0∞) : Prop :=
  ∀ (t : ℝ), 0 ≤ t → t ≤ 1 → ∀ x y,
    f x ^ (1 - t) * f y ^ t ≤ f ((1 - t) • x + t • y)

theorem logConcaveDensity_marginal {E : Type*} [AddCommMonoid E] [Module ℝ E]
    (d : ℕ) (f : E × (Fin (d + 1) → ℝ) → ℝ≥0∞)
    (hf : ∀ x, Measurable (fun y => f (x, y))) (hlc : LogConcaveDensity f) :
    LogConcaveDensity (fun x => ∫⁻ y, f (x, y)) := by
  intro t ht ht1 x y
  apply prekopa_leindler_weighted d t ht ht1
    (fun z => f (x, z)) (fun z => f (y, z))
    (fun z => f ((1 - t) • x + t • y, z))
    (hf x) (hf y) (hf ((1 - t) • x + t • y))
  intro u v
  exact hlc t ht ht1 (x, u) (y, v)

theorem logConcaveDensity_marginal_all {E : Type*} [AddCommMonoid E] [Module ℝ E]
    (n : ℕ) (f : E × (Fin n → ℝ) → ℝ≥0∞)
    (hf : ∀ x, Measurable (fun y => f (x, y))) (hlc : LogConcaveDensity f) :
    LogConcaveDensity (fun x => ∫⁻ y, f (x, y)) := by
  intro t ht ht1 x y
  apply prekopa_leindler_weighted_all n t ht ht1
    (fun z => f (x, z)) (fun z => f (y, z))
    (fun z => f ((1 - t) • x + t • y, z))
    (hf x) (hf y) (hf ((1 - t) • x + t • y))
  intro u v
  exact hlc t ht ht1 (x, u) (y, v)

end AffineFKProof
