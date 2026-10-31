module

public import AffineFK.PrekopaLeindlerMarginal

/-!
# Linear images, products and convolution of log-concave densities

The convolution theorem applies the proved Prékopa marginal inequality.
It concerns the actual extended nonnegative integral and assumes neither
integrability nor positivity of the densities. The zero-dimensional case
and the endpoint weights are included.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory
open scoped ENNReal

theorem logConcaveDensity_comp_linearMap {E F : Type*}
    [AddCommMonoid E] [Module ℝ E] [AddCommMonoid F] [Module ℝ F]
    (f : F → ℝ≥0∞) (hf : LogConcaveDensity f) (A : E →ₗ[ℝ] F) :
    LogConcaveDensity (fun x => f (A x)) := by
  intro t ht ht1 x y
  simpa only [map_add, map_smul] using hf t ht ht1 (A x) (A y)

theorem logConcaveDensity_mul {E : Type*} [AddCommMonoid E] [Module ℝ E]
    (f g : E → ℝ≥0∞) (hf : LogConcaveDensity f) (hg : LogConcaveDensity g) :
    LogConcaveDensity (fun x => f x * g x) := by
  intro t ht ht1 x y
  calc
    (f x * g x) ^ (1 - t) * (f y * g y) ^ t =
        (f x ^ (1 - t) * f y ^ t) * (g x ^ (1 - t) * g y ^ t) := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ (sub_nonneg.mpr ht1),
        ENNReal.mul_rpow_of_nonneg _ _ ht]
      ac_rfl
    _ ≤ f ((1 - t) • x + t • y) * g ((1 - t) • x + t • y) :=
      mul_le_mul' (hf t ht ht1 x y) (hg t ht ht1 x y)

theorem logConcaveDensity_convolution (n : ℕ)
    (f g : (Fin n → ℝ) → ℝ≥0∞) (hf : Measurable f) (hg : Measurable g)
    (hlf : LogConcaveDensity f) (hlg : LogConcaveDensity g) :
    LogConcaveDensity (fun x => ∫⁻ y, f (x - y) * g y) := by
  let A : ((Fin n → ℝ) × (Fin n → ℝ)) →ₗ[ℝ] (Fin n → ℝ) :=
    LinearMap.fst ℝ _ _ - LinearMap.snd ℝ _ _
  have hA : LogConcaveDensity (fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
      f (p.1 - p.2)) := logConcaveDensity_comp_linearMap f hlf A
  have hB : LogConcaveDensity (fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
      g p.2) := logConcaveDensity_comp_linearMap g hlg (LinearMap.snd ℝ _ _)
  exact logConcaveDensity_marginal_all n (fun p => f (p.1 - p.2) * g p.2)
    (fun x => (hf.comp (by fun_prop)).mul hg)
    (logConcaveDensity_mul _ _ hA hB)

end AffineFKProof
