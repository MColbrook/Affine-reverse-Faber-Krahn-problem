module

public import AffineFK.GaussianLogConcavity

/-!
# Log-concave marginals and convolution in Euclidean space

The actual Lebesgue integrals are transported through Mathlib's
volume-preserving PiLp equivalence (Xavier Roblot, Sebastien Gouezel
and contributors, Apache-2.0). No surrogate measure is introduced.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory WithLp
open scoped ENNReal

theorem logConcaveDensity_marginal_euclidean {E : Type*}
    [AddCommMonoid E] [Module ℝ E] (n : ℕ)
    (f : E × EuclideanSpace ℝ (Fin n) → ℝ≥0∞)
    (hf : ∀ x, Measurable (fun y => f (x, y))) (hlc : LogConcaveDensity f) :
    LogConcaveDensity (fun x => ∫⁻ y, f (x, y)) := by
  let F : E × (Fin n → ℝ) → ℝ≥0∞ := fun p => f (p.1, toLp 2 p.2)
  have hF : LogConcaveDensity F := by
    intro t ht ht1 x y
    exact hlc t ht ht1 (x.1, toLp 2 x.2) (y.1, toLp 2 y.2)
  have hm := logConcaveDensity_marginal_all n F
    (fun x => (hf x).comp (by fun_prop)) hF
  have heq (x : E) : (∫⁻ y : Fin n → ℝ, F (x, y)) = ∫⁻ y, f (x, y) :=
    (PiLp.volume_preserving_toLp (Fin n)).lintegral_comp (hf x)
  simpa only [heq] using hm

theorem logConcaveDensity_convolution_euclidean (n : ℕ)
    (f g : EuclideanSpace ℝ (Fin n) → ℝ≥0∞) (hf : Measurable f) (hg : Measurable g)
    (hlf : LogConcaveDensity f) (hlg : LogConcaveDensity g) :
    LogConcaveDensity (fun x => ∫⁻ y, f (x - y) * g y) := by
  let A : (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) →ₗ[ℝ]
      EuclideanSpace ℝ (Fin n) := LinearMap.fst ℝ _ _ - LinearMap.snd ℝ _ _
  have hA : LogConcaveDensity (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      f (p.1 - p.2)) := logConcaveDensity_comp_linearMap f hlf A
  have hB : LogConcaveDensity (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      g p.2) := logConcaveDensity_comp_linearMap g hlg (LinearMap.snd ℝ _ _)
  exact logConcaveDensity_marginal_euclidean n (fun p => f (p.1 - p.2) * g p.2)
    (fun x => (hf.comp (by fun_prop)).mul hg)
    (logConcaveDensity_mul _ _ hA hB)

end AffineFKProof
