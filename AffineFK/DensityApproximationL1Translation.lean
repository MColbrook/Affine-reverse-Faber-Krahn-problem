module

public import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Genuine Lebesgue L1 translation continuity

This is continuity of actual integrable functions under translations of
Lebesgue volume. It reuses Yury Kudryashov's Mathlib continuity theorem
for Lp composition with continuous measure-preserving maps at p=1.
No moment, smoothness or density-approximation limit is assumed.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory Filter
open scoped Topology

def densityApproximationTranslation (n : ℕ) (y : EuclideanSpace ℝ (Fin n)) :
    C(EuclideanSpace ℝ (Fin n), EuclideanSpace ℝ (Fin n)) :=
  ⟨fun x => x - y, by fun_prop⟩

theorem densityApproximationTranslation_measurePreserving (n : ℕ)
    (y : EuclideanSpace ℝ (Fin n)) :
    MeasurePreserving (densityApproximationTranslation n y)
      (volume : Measure (EuclideanSpace ℝ (Fin n))) volume := by
  simpa only [densityApproximationTranslation, ContinuousMap.coe_mk, sub_eq_add_neg] using
    (measurePreserving_add_right (volume : Measure (EuclideanSpace ℝ (Fin n))) (-y))

theorem densityApproximationTranslation_continuous (n : ℕ) :
    Continuous (densityApproximationTranslation n) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  change Continuous (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) => p.2 - p.1)
  fun_prop

theorem densityApproximation_translation_L1_tendsto (n : ℕ)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : Integrable f (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    Tendsto (fun y : EuclideanSpace ℝ (Fin n) => ∫ x, ‖f (x - y) - f x‖)
      (𝓝 0) (𝓝 0) := by
  let fL := hf.toL1 f
  let g (y : EuclideanSpace ℝ (Fin n)) := Lp.compMeasurePreserving
    (densityApproximationTranslation n y) (densityApproximationTranslation_measurePreserving n y) fL
  have hg : Tendsto g (𝓝 0) (𝓝 (g 0)) :=
    tendsto_const_nhds.compMeasurePreservingLp
      (densityApproximationTranslation_continuous n).continuousAt.tendsto
      (densityApproximationTranslation_measurePreserving n)
      (densityApproximationTranslation_measurePreserving n 0) (by simp)
  have hdist := (tendsto_iff_dist_tendsto_zero).mp hg
  convert hdist using 1
  ext y
  rw [L1.dist_eq_integral_dist]
  apply integral_congr_ae
  have hgy := (Lp.coeFn_compMeasurePreserving fL (densityApproximationTranslation_measurePreserving n y)).trans
    ((densityApproximationTranslation_measurePreserving n y).quasiMeasurePreserving.ae_eq_comp hf.coeFn_toL1)
  have hg0 := (Lp.coeFn_compMeasurePreserving fL (densityApproximationTranslation_measurePreserving n 0)).trans
    ((densityApproximationTranslation_measurePreserving n 0).quasiMeasurePreserving.ae_eq_comp hf.coeFn_toL1)
  filter_upwards [hgy, hg0] with x hy h0
  simp only [g, fL] at hy h0 ⊢
  rw [hy, h0]
  simp [densityApproximationTranslation, Real.dist_eq, Real.norm_eq_abs]

end AffineFKProof
