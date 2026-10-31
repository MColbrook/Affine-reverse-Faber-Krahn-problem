module

public import AffineFK.DirichletRayleighFinite
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith

/-!
# Genuine normalized minimizing sequences for the Dirichlet Rayleigh infimum

Nonempty open sets supply an actual nonzero compact test and hence finite
Rayleigh infimum. The infimum property then constructs normalized H0^1
competitors with gradient energy arbitrarily close to that actual value.
No minimizer, eigenfunction, compactness or spectral proxy is assumed.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory TopologicalSpace Filter
open scoped ENNReal Topology

theorem dirichletGroundstate_graph_norm_sq (n : ℕ)
    (U : Opens (EuclideanSpace ℝ (Fin n))) (v : dirichletSobolev n U) :
    ‖v‖ ^ 2 = ‖dirichletValue n U v‖ ^ 2 + ‖dirichletGradient n U v‖ ^ 2 :=
  unweighted_graph_norm_sq n (v : unweightedSobolevGraph n)

set_option maxHeartbeats 1000000 in
theorem dirichletGroundstate_normalized_competitor (n : ℕ)
    (U : Opens (EuclideanSpace ℝ (Fin n))) (hU : (U : Set (EuclideanSpace ℝ (Fin n))).Nonempty)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ v : dirichletSobolev n U, ‖dirichletValue n U v‖ ^ 2 = 1 ∧
      ‖dirichletGradient n U v‖ ^ 2 < (dirichletEigenvalue n U).toReal + ε := by
  have hf := dirichletEigenvalue_ne_top n U hU
  have hpos : 0 < (dirichletEigenvalue n U).toReal + ε :=
    add_pos_of_nonneg_of_pos ENNReal.toReal_nonneg hε
  have hlt : dirichletEigenvalue n U < ENNReal.ofReal ((dirichletEigenvalue n U).toReal + ε) := by
    calc
      _ = ENNReal.ofReal (dirichletEigenvalue n U).toReal := (ENNReal.ofReal_toReal hf).symm
      _ < _ := (ENNReal.ofReal_lt_ofReal_iff hpos).mpr (by linarith)
  change (⨅ (v : dirichletSobolev n U) (_ : dirichletValue n U v ≠ 0),
    ENNReal.ofReal (dirichletRayleigh n U v)) < _ at hlt
  obtain ⟨w, hw⟩ := iInf_lt_iff.mp hlt
  obtain ⟨hw0, hwR⟩ := iInf_lt_iff.mp hw
  have hR : dirichletRayleigh n U w < (dirichletEigenvalue n U).toReal + ε :=
    (ENNReal.ofReal_lt_ofReal_iff hpos).mp hwR
  let c : ℝ := ‖dirichletValue n U w‖⁻¹
  let v : dirichletSobolev n U := c • w
  have hn : ‖dirichletValue n U w‖ ≠ 0 := norm_ne_zero_iff.mpr hw0
  have hvalue : ‖dirichletValue n U v‖ ^ 2 = 1 := by
    simp only [v, map_smul, norm_smul, c, Real.norm_eq_abs, abs_inv, abs_norm,
      inv_mul_cancel₀ hn, one_pow]
  have hgradient : ‖dirichletGradient n U v‖ ^ 2 = dirichletRayleigh n U w := by
    simp only [v, map_smul, norm_smul, c, Real.norm_eq_abs, abs_inv, abs_norm,
      mul_pow, dirichletRayleigh, div_eq_mul_inv, inv_pow]
    ring
  exact ⟨v, hvalue, hgradient.trans_lt hR⟩

theorem dirichletGroundstate_normalized_minimizing_sequence (n : ℕ)
    (U : Opens (EuclideanSpace ℝ (Fin n))) (hU : (U : Set (EuclideanSpace ℝ (Fin n))).Nonempty) :
    ∃ v : ℕ → dirichletSobolev n U,
      (∀ k, ‖dirichletValue n U (v k)‖ ^ 2 = 1) ∧
      (∀ k, ‖dirichletGradient n U (v k)‖ ^ 2 <
        (dirichletEigenvalue n U).toReal + ((k : ℝ) + 1)⁻¹) := by
  classical
  have h (k : ℕ) := dirichletGroundstate_normalized_competitor n U hU
    (((k : ℝ) + 1)⁻¹) (by positivity)
  choose v hv hE using h
  exact ⟨v, hv, hE⟩

set_option maxHeartbeats 1000000 in
theorem dirichletGroundstate_bounded_minimizing_sequence (n : ℕ)
    (U : Opens (EuclideanSpace ℝ (Fin n))) (hU : (U : Set (EuclideanSpace ℝ (Fin n))).Nonempty) :
    ∃ v : ℕ → dirichletSobolev n U,
      (∀ k, ‖dirichletValue n U (v k)‖ ^ 2 = 1) ∧
      Tendsto (fun k => ‖dirichletGradient n U (v k)‖ ^ 2) atTop
        (𝓝 (dirichletEigenvalue n U).toReal) ∧
      (∀ k, ‖v k‖ ≤ Real.sqrt ((dirichletEigenvalue n U).toReal + 2)) := by
  obtain ⟨v, hv, hE⟩ := dirichletGroundstate_normalized_minimizing_sequence n U hU
  have hne (k : ℕ) : dirichletValue n U (v k) ≠ 0 := by
    intro h
    have hk := hv k
    simp only [h, norm_zero, zero_pow (by norm_num : 2 ≠ 0)] at hk
    exact zero_ne_one hk
  have hlower (k : ℕ) : (dirichletEigenvalue n U).toReal ≤ ‖dirichletGradient n U (v k)‖ ^ 2 := by
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top
      (dirichletEigenvalue_le_rayleigh n U (v k) (hne k))
    simpa only [dirichletRayleigh, hv k, div_one,
      ENNReal.toReal_ofReal (sq_nonneg ‖dirichletGradient n U (v k)‖)] using h
  have hdiff : Tendsto (fun k => ‖dirichletGradient n U (v k)‖ ^ 2 -
      (dirichletEigenvalue n U).toReal) atTop (𝓝 (0 : ℝ)) :=
    squeeze_zero (fun k => sub_nonneg.mpr (hlower k))
      (fun k => by linarith [hE k]) tendsto_inverse_succ
  refine ⟨v, hv, ?_, ?_⟩
  · simpa only [sub_add_cancel, zero_add] using hdiff.add_const (dirichletEigenvalue n U).toReal
  · intro k
    have heps : ((k : ℝ) + 1)⁻¹ ≤ 1 := by
      rw [inv_eq_one_div, div_le_one (by positivity : 0 < (k : ℝ) + 1)]
      linarith [Nat.cast_nonneg (α := ℝ) k]
    have hsq : ‖v k‖ ^ 2 ≤ (dirichletEigenvalue n U).toReal + 2 := by
      rw [dirichletGroundstate_graph_norm_sq, hv k]
      linarith [hE k]
    calc
      _ = Real.sqrt (‖v k‖ ^ 2) := (Real.sqrt_sq (norm_nonneg (v k))).symm
      _ ≤ _ := Real.sqrt_le_sqrt hsq

end AffineFKProof
