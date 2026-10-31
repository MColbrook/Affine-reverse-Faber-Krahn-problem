module

public import AffineFK.OUEntropyDissipationTail

/-!
# Deriving finite initial KL before using its real zero-time endpoint

The extended-valued initial entropy limit is used with a uniform bound
obtained from actual positive-time dissipation and the infinite endpoint.
Finite initial entropy is therefore a conclusion, not an assumption.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory InformationTheory TopologicalSpace Filter Set
open scoped Distributions RealInnerProductSpace Topology ENNReal

theorem ou_initial_entropy_bound (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (hac : ν ≪ volume)
    (hxi : ∀ i : Fin n, MemLp (fun x : EuclideanSpace ℝ (Fin n) => x i) 2 ν)
    (v : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (hv : MemLp v 2 ν)
    (hweak : ∀ F : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), EuclideanSpace ℝ (Fin n)),
      (∫ x, ⟪v x, F x⟫ ∂ν) = ∫ x, ⟪x, F x⟫ - vectorDivergence n F x ∂ν) :
    klDiv ν (stdGaussian (EuclideanSpace ℝ (Fin n))) ≤
      ENNReal.ofReal ((∫ x, ‖v x‖ ^ 2 ∂ν) / 2) ∧
    klDiv ν (stdGaussian (EuclideanSpace ℝ (Fin n))) ≠ ∞ := by
  let γ := stdGaussian (EuclideanSpace ℝ (Fin n))
  let S : ℝ := ∫ x, ‖v x‖ ^ 2 ∂ν
  have hS : 0 ≤ S := integral_nonneg (fun x => sq_nonneg _)
  have hbound (s : ℝ) (hs : 0 < s) : klDiv (ouInitialLaw n ν s) γ ≤ ENNReal.ofReal (S / 2) := by
    have hfin : klDiv (ouInitialLaw n ν s) γ ≠ ∞ := (ou_entropy_dissipation n ν hxi v hv hweak s s hs le_rfl).1
    have ht := (ou_positive_entropy_eq_score_tail n ν hxi v hv hweak s hs).trans_le
      (ouScoreEnergy_integral_le n ν hxi v hv hweak s hs.le)
    have he : Real.exp (-2 * s) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    have htail : (Real.exp (-2 * s) / 2) * S ≤ S / 2 := by nlinarith [mul_le_mul_of_nonneg_right he hS]
    rw [← ENNReal.ofReal_toReal hfin]
    exact ENNReal.ofReal_le_ofReal (ht.trans htail)
  have hlim := ouInitial_entropy_tendsto_of_volume_ac n ν hac
  have hfinal : klDiv ν γ ≤ ENNReal.ofReal (S / 2) := by
    apply le_of_tendsto hlim
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact hbound s hs
  exact ⟨hfinal, ne_of_lt (lt_of_le_of_lt hfinal ENNReal.ofReal_lt_top)⟩

end AffineFKProof
