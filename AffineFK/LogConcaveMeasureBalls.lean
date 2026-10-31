module

public import AffineFK.DirichletGaussianIterationLiminf
public import Mathlib.MeasureTheory.Covering.Besicovitch
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Closed-ball densities of a log-concave measure

The set formulation uses nonempty compact sets. This permits both endpoint
weights without applying the convention `0 ^ 0 = 1` to an empty Minkowski
summand. Closed-ball differentiation is Mathlib's Besicovitch theorem.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory Filter Metric Set
open scoped ENNReal Topology Pointwise

/-- The compact-set formulation of log-concavity, including the endpoint weights. -/
def IsLogConcaveMeasure (n : ℕ) (ν : Measure (EuclideanSpace ℝ (Fin n))) : Prop :=
  ∀ K L : Set (EuclideanSpace ℝ (Fin n)),
    IsCompact K → K.Nonempty → IsCompact L → L.Nonempty →
    ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      (ν K) ^ (1 - t) * (ν L) ^ t ≤ ν ((1 - t) • K + t • L)

/-- The actual measure of a closed ball divided by its Lebesgue volume. -/
def logConcaveBallDensity (n : ℕ) (ν : Measure (EuclideanSpace ℝ (Fin n)))
    (r : ℝ) (x : EuclideanSpace ℝ (Fin n)) : ℝ≥0∞ :=
  ν (closedBall x r) / volume (closedBall x r)

theorem closedBall_convex_combination_subset (n : ℕ)
    (x y : EuclideanSpace ℝ (Fin n)) (r t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    (1 - t) • closedBall x r + t • closedBall y r ⊆
      closedBall ((1 - t) • x + t • y) r := by
  rintro z ⟨u, ⟨u', hu, rfl⟩, v, ⟨v', hv, rfl⟩, rfl⟩
  rw [mem_closedBall, dist_eq_norm]
  have heq : (1 - t) • u' + t • v' - ((1 - t) • x + t • y) =
      (1 - t) • (u' - x) + t • (v' - y) := by module
  rw [heq]
  calc
    _ ≤ ‖(1 - t) • (u' - x)‖ + ‖t • (v' - y)‖ := norm_add_le _ _
    _ = (1 - t) * ‖u' - x‖ + t * ‖v' - y‖ := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (sub_nonneg.mpr ht1), abs_of_nonneg ht]
    _ ≤ (1 - t) * r + t * r := add_le_add
      (mul_le_mul_of_nonneg_left (by simpa only [mem_closedBall, dist_eq_norm] using hu)
        (sub_nonneg.mpr ht1))
      (mul_le_mul_of_nonneg_left (by simpa only [mem_closedBall, dist_eq_norm] using hv) ht)
    _ = r := by ring

theorem logConcaveMeasure_closedBall (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) (hν : IsLogConcaveMeasure n ν)
    {r : ℝ} (hr : 0 < r) :
    LogConcaveDensity (fun x => ν (closedBall x r)) := by
  intro t ht ht1 x y
  exact (hν _ _ (isCompact_closedBall x r) ⟨x, mem_closedBall_self hr.le⟩
    (isCompact_closedBall y r) ⟨y, mem_closedBall_self hr.le⟩ t ht ht1).trans
    (measure_mono (closedBall_convex_combination_subset n x y r t ht ht1))

theorem logConcaveDensity_div_const {E : Type*} [AddCommMonoid E] [Module ℝ E]
    (f : E → ℝ≥0∞) (hf : LogConcaveDensity f) (c : ℝ≥0∞) :
    LogConcaveDensity (fun x => f x / c) := by
  intro t ht ht1 x y
  change (f x / c) ^ (1 - t) * (f y / c) ^ t ≤ f ((1 - t) • x + t • y) / c
  simp only [div_eq_mul_inv, ENNReal.mul_rpow_of_nonneg _ _ (sub_nonneg.mpr ht1),
    ENNReal.mul_rpow_of_nonneg _ _ ht]
  calc
    _ = (f x ^ (1 - t) * f y ^ t) * ((c⁻¹) ^ (1 - t) * (c⁻¹) ^ t) := by ac_rfl
    _ = (f x ^ (1 - t) * f y ^ t) * c⁻¹ := by
      rw [← ENNReal.rpow_add_of_nonneg (1 - t) t (sub_nonneg.mpr ht1) ht]
      simp only [sub_add_cancel, ENNReal.rpow_one]
    _ ≤ f ((1 - t) • x + t • y) * c⁻¹ := mul_le_mul' (hf t ht ht1 x y) le_rfl

theorem logConcaveBallDensity_logConcave (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) (hν : IsLogConcaveMeasure n ν)
    {r : ℝ} (hr : 0 < r) : LogConcaveDensity (logConcaveBallDensity n ν r) := by
  have h := logConcaveDensity_div_const _ (logConcaveMeasure_closedBall n ν hν hr)
    (volume (closedBall (0 : EuclideanSpace ℝ (Fin n)) r))
  change LogConcaveDensity (fun x => ν (closedBall x r) / volume (closedBall x r))
  simp_rw [Measure.addHaar_closedBall_center]
  exact h

theorem logConcaveBallDensity_measurable (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [SFinite ν] (r : ℝ) :
    Measurable (logConcaveBallDensity n ν r) := by
  have hm : Measurable (fun x : EuclideanSpace ℝ (Fin n) => ν (closedBall x r)) := by
    have hs : MeasurableSet {p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) |
        dist p.2 p.1 ≤ r} := isClosed_le (continuous_snd.dist continuous_fst)
          continuous_const |>.measurableSet
    exact measurable_measure_prodMk_left hs
  change Measurable (fun x => ν (closedBall x r) / volume (closedBall x r))
  simp_rw [Measure.addHaar_closedBall_center]
  exact hm.div_const (volume (closedBall (0 : EuclideanSpace ℝ (Fin n)) r))

end AffineFKProof
