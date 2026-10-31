module

public import AffineFK.DirichletGaussianIteration
public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator

/-!
# Nontriviality and genuine Lp bounds for the killed Gaussian iterates

The actual finite-grid integrals are positive at every point of a
nonempty open domain. On a finite-volume domain their real versions have
all Lp bounds by the genuine domain indicator, and the actual total mass
is finite. No ground-state or continuous killed-kernel identification is
asserted.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory Set
open scoped ENNReal

theorem dirichletGaussianStep_pos (n : ℕ)
    (D : Set (EuclideanSpace ℝ (Fin n))) (hD : IsOpen D) (b : ℝ) (hb : 0 < b)
    (f : EuclideanSpace ℝ (Fin n) → ℝ≥0∞) (hf : Measurable f)
    (hpos : ∀ y ∈ D, 0 < f y) (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ D) :
    0 < dirichletGaussianStep n D b f x := by
  rw [dirichletGaussianStep, indicator_of_mem hx]
  apply (lintegral_pos_iff_support
    (((dirichletGaussianKernel_measurable n b).comp (measurable_const.sub measurable_id)).mul hf)).mpr
  have hsub : D ⊆ Function.support (fun y => dirichletGaussianKernel n b (x - y) * f y) := by
    intro y hy
    exact mul_ne_zero (dirichletGaussianKernel_pos n b hb (x - y)).ne' (hpos y hy).ne'
  exact (hD.measure_pos (μ := (volume : Measure (EuclideanSpace ℝ (Fin n)))) ⟨x, hx⟩).trans_le
    (measure_mono hsub)

theorem dirichletGaussianIterate_pos (n : ℕ)
    (D : Set (EuclideanSpace ℝ (Fin n))) (hD : IsOpen D) (b : ℝ) (hb : 0 < b)
    (k : ℕ) (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ D) :
    0 < dirichletGaussianIterate n D b k x := by
  induction k generalizing x with
  | zero => simp only [dirichletGaussianIterate, indicator_of_mem hx, zero_lt_one]
  | succ k hk =>
      exact dirichletGaussianStep_pos n D hD b hb _
        (dirichletGaussianIterate_measurable n D hD.measurableSet b k) hk x hx

theorem dirichletGaussianIterate_ne_top (n : ℕ)
    (D : Set (EuclideanSpace ℝ (Fin n))) (b : ℝ) (hb : 0 < b)
    (k : ℕ) (x : EuclideanSpace ℝ (Fin n)) : dirichletGaussianIterate n D b k x ≠ ∞ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top (dirichletGaussianIterate_le_one n D b hb k x)

theorem dirichletGaussianIterate_mass_pos (n : ℕ)
    (D : Set (EuclideanSpace ℝ (Fin n))) (hD : IsOpen D) (hne : D.Nonempty)
    (b : ℝ) (hb : 0 < b) (k : ℕ) : (0 : ℝ≥0∞) < ∫⁻ x, dirichletGaussianIterate n D b k x := by
  apply (lintegral_pos_iff_support (dirichletGaussianIterate_measurable n D hD.measurableSet b k)).mpr
  have hsub : D ⊆ Function.support (dirichletGaussianIterate n D b k) :=
    fun x hx => (dirichletGaussianIterate_pos n D hD b hb k x hx).ne'
  exact (hD.measure_pos (μ := (volume : Measure (EuclideanSpace ℝ (Fin n)))) hne).trans_le
    (measure_mono hsub)

theorem dirichletGaussianIterate_mass_ne_top (n : ℕ)
    (D : Set (EuclideanSpace ℝ (Fin n))) (hD : MeasurableSet D)
    (hfinite : (volume : Measure (EuclideanSpace ℝ (Fin n))) D ≠ ∞)
    (b : ℝ) (hb : 0 < b) (k : ℕ) : (∫⁻ x, dirichletGaussianIterate n D b k x) ≠ ∞ :=
  ne_top_of_le_ne_top hfinite (dirichletGaussianIterate_mass_le n D hD b hb k)

theorem dirichletGaussianIterate_toReal_memLp (n : ℕ)
    (D : Set (EuclideanSpace ℝ (Fin n))) (hD : MeasurableSet D)
    (hfinite : (volume : Measure (EuclideanSpace ℝ (Fin n))) D ≠ ∞)
    (b : ℝ) (hb : 0 < b) (k : ℕ) (p : ℝ≥0∞) :
    MemLp (fun x => (dirichletGaussianIterate n D b k x).toReal) p
      (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
  have hbound := memLp_indicator_const p hD.nullMeasurableSet (1 : ℝ) (Or.inr hfinite)
  apply hbound.mono' (dirichletGaussianIterate_measurable n D hD b k).ennreal_toReal.aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro x
  by_cases hx : x ∈ D
  · rw [indicator_of_mem hx, Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
    simpa only [ENNReal.toReal_one] using
      ENNReal.toReal_mono ENNReal.one_ne_top (dirichletGaussianIterate_le_one n D b hb k x)
  · rw [dirichletGaussianIterate_zero_outside n D b k x hx, ENNReal.toReal_zero,
      norm_zero, indicator_of_notMem hx]

end AffineFKProof
