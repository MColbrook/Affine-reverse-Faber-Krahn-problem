module

public import AffineFK.PrekopaLeindlerMarginal
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.Topology.Order.MonotoneConvergence
public import Mathlib.Topology.Order.LiminfLimsup

/-!
# Genuine pointwise liminf closure of log-concave densities

Tail infima and their increasing supremum preserve the actual extended
nonnegative log-concavity inequality. Endpoint exponents and zero values
are treated explicitly, without a uniform bound or an assumed finite limit.
The final lemma identifies this chosen representative under actual AE
pointwise convergence; it does not infer that convergence from L2 alone.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory Filter
open scoped ENNReal Topology

theorem logConcaveDensity_iInf {E : Type*} {ι : Sort*}
    [AddCommMonoid E] [Module ℝ E]
    (f : ι → E → ℝ≥0∞) (hf : ∀ i, LogConcaveDensity (f i)) :
    LogConcaveDensity (fun x => ⨅ i, f i x) := by
  intro t ht ht1 x y
  refine le_iInf fun i => ?_
  exact (mul_le_mul'
    (ENNReal.rpow_le_rpow (iInf_le (fun i => f i x) i) (sub_nonneg.mpr ht1))
    (ENNReal.rpow_le_rpow (iInf_le (fun i => f i y) i) ht)).trans (hf i t ht ht1 x y)

theorem logConcaveDensity_iSup_of_monotone_unbounded {E : Type*}
    [AddCommMonoid E] [Module ℝ E]
    (f : ℕ → E → ℝ≥0∞) (hf : ∀ k, LogConcaveDensity (f k))
    (hmono : ∀ x, Monotone (fun k => f k x)) :
    LogConcaveDensity (fun x => ⨆ k, f k x) := by
  intro t ht ht1 x y
  change (⨆ k, f k x) ^ (1 - t) * (⨆ k, f k y) ^ t ≤
    ⨆ k, f k ((1 - t) • x + t • y)
  by_cases htzero : t = 0
  · subst t
    simp
  by_cases htone : t = 1
  · subst t
    simp
  have htpos : 0 < t := lt_of_le_of_ne ht (Ne.symm htzero)
  have hsub : 0 < 1 - t := sub_pos.mpr (lt_of_le_of_ne ht1 htone)
  by_cases hx : (⨆ k, f k x) = 0
  · rw [hx, ENNReal.zero_rpow_of_pos hsub, zero_mul]
    exact bot_le
  by_cases hy : (⨆ k, f k y) = 0
  · rw [hy, ENNReal.zero_rpow_of_pos htpos, mul_zero]
    exact bot_le
  have hxp : (⨆ k, f k x) ^ (1 - t) ≠ 0 :=
    (ENNReal.rpow_eq_zero_iff_of_pos hsub).not.mpr hx
  have hyp : (⨆ k, f k y) ^ t ≠ 0 :=
    (ENNReal.rpow_eq_zero_iff_of_pos htpos).not.mpr hy
  have hlim (z : E) : Tendsto (fun k => f k z) atTop (𝓝 (⨆ k, f k z)) :=
    tendsto_atTop_iSup (hmono z)
  have hp : Tendsto (fun k => f k x ^ (1 - t) * f k y ^ t) atTop
      (𝓝 ((⨆ k, f k x) ^ (1 - t) * (⨆ k, f k y) ^ t)) :=
    ENNReal.Tendsto.mul
      (ENNReal.continuous_rpow_const.tendsto _ |>.comp (hlim x)) (Or.inl hxp)
      (ENNReal.continuous_rpow_const.tendsto _ |>.comp (hlim y)) (Or.inl hyp)
  exact le_of_tendsto_of_tendsto hp (hlim ((1 - t) • x + t • y))
    (Eventually.of_forall fun k => hf k t ht ht1 x y)

theorem logConcaveDensity_liminf {E : Type*}
    [AddCommMonoid E] [Module ℝ E]
    (f : ℕ → E → ℝ≥0∞) (hf : ∀ k, LogConcaveDensity (f k)) :
    LogConcaveDensity (fun x => liminf (fun k => f k x) atTop) := by
  have htail (N : ℕ) : LogConcaveDensity (fun x => ⨅ k ≥ N, f k x) :=
    logConcaveDensity_iInf (fun k x => ⨅ _h : N ≤ k, f k x)
      (fun k => logConcaveDensity_iInf (fun _h : N ≤ k => f k) (fun _ => hf k))
  have hmono : ∀ x, Monotone (fun N : ℕ => ⨅ k ≥ N, f k x) := by
    intro x N M hNM
    exact iInf_le_iInf_of_subset fun _ hi => le_trans hNM hi
  simpa only [liminf_eq_iSup_iInf_of_nat] using
    logConcaveDensity_iSup_of_monotone_unbounded _ htail hmono

theorem measurable_logConcave_liminf {E : Type*} [MeasurableSpace E]
    (f : ℕ → E → ℝ≥0∞) (hf : ∀ k, Measurable (f k)) :
    Measurable (fun x => liminf (fun k => f k x) atTop) := by
  simpa only [liminf_eq_iSup_iInf_of_nat] using
    Measurable.iSup (fun N : ℕ => Measurable.iInf (fun k : ℕ =>
      Measurable.iInf (fun _h : N ≤ k => hf k)))

theorem logConcave_liminf_ae_eq_of_ae_tendsto {E : Type*} [MeasurableSpace E]
    (μ : Measure E) (f : ℕ → E → ℝ≥0∞) (g : E → ℝ≥0∞)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun k => f k x) atTop (𝓝 (g x))) :
    (fun x => liminf (fun k => f k x) atTop) =ᵐ[μ] g :=
  hlim.mono fun _ hx => hx.liminf_eq

end AffineFKProof
