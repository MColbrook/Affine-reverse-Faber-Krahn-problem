module

public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Tactic.FieldSimp

/-!
# Actual affine pushforward of a Lebesgue density

The Jacobian is derived from the genuine finite-dimensional Haar scaling
theorem, including dimension zero. Reuse: Haar measure change of variables
by Floris van Doorn, Sébastien Gouëzel and Mathlib contributors (Apache-2.0).
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory Set Filter
open scoped ENNReal Pointwise BigOperators Topology

theorem bridge_affine_lintegral (n : ℕ) (c : ℝ) (hc : 0 < c)
    (x : EuclideanSpace ℝ (Fin n)) (f : EuclideanSpace ℝ (Fin n) → ℝ≥0∞)
    (hf : Measurable f) :
    (∫⁻ u, f (x + c • u)) = ENNReal.ofReal ((c ^ n)⁻¹) * ∫⁻ y, f y := by
  calc
    _ = ∫⁻ y, f (x + y) ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).map (fun u => c • u)) :=
      (lintegral_map (hf.comp (by fun_prop)) (by fun_prop)).symm
    _ = _ := by
      rw [Measure.map_addHaar_smul volume hc.ne', lintegral_smul_measure, lintegral_add_left_eq_self]
      simp only [finrank_euclideanSpace_fin, abs_of_nonneg (inv_nonneg.mpr (pow_nonneg hc.le n))]
      rfl

theorem bridge_affine_density_map (n : ℕ) (c : ℝ) (hc : 0 < c)
    (x : EuclideanSpace ℝ (Fin n)) (g : EuclideanSpace ℝ (Fin n) → ℝ≥0∞)
    (hg : Measurable g) :
    ((volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity g).map (fun u => x + c • u) =
      volume.withDensity (fun y => ENNReal.ofReal ((c ^ n)⁻¹) * g (c⁻¹ • (y - x))) := by
  have he : Measurable (fun u : EuclideanSpace ℝ (Fin n) => x + c • u) := by fun_prop
  apply Measure.ext
  intro S hS
  rw [Measure.map_apply he hS, withDensity_apply _ (hS.preimage he), withDensity_apply _ hS]
  let K : EuclideanSpace ℝ (Fin n) → ℝ≥0∞ :=
    S.indicator (fun y => g (c⁻¹ • (y - x)))
  have hK : Measurable K := (hg.comp (by fun_prop)).indicator hS
  have hinv (u : EuclideanSpace ℝ (Fin n)) : c⁻¹ • ((x + c • u) - x) = u := by
    rw [add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hc.ne', one_smul]
  calc
    _ = ∫⁻ u, K (x + c • u) := by
      rw [← lintegral_indicator (hS.preimage he)]
      apply lintegral_congr
      intro u
      by_cases hu : x + c • u ∈ S
      · simp [K, hu, smul_smul, hc.ne']
      · simp [K, hu]
    _ = ENNReal.ofReal ((c ^ n)⁻¹) * ∫⁻ y, K y := bridge_affine_lintegral n c hc x K hK
    _ = _ := by
      rw [show (∫⁻ y, K y) = ∫⁻ y in S, g (c⁻¹ • (y - x)) from lintegral_indicator hS _]
      exact (lintegral_const_mul _ (hg.comp (by fun_prop))).symm

end AffineFKProof
