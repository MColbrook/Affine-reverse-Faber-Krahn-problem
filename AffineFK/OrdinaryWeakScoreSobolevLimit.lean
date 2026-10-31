module

public import AffineFK.OrdinaryWeakScoreSobolevCompactness
public import AffineFK.DensityApproximationL1SquareRoot

/-!
# The actual energy-preserving H1 approximation limit

The bounded-preimage theorem is applied to the completed graph's genuine
value projection. Unit value norm and a uniform gradient bound control the
Hilbert graph norm. The limiting value fixes its gradient energy bound;
no weak lower-semicontinuity premise is introduced.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory Filter
open scoped Topology

theorem ordinaryWeakScore_graph_limit (n : ℕ)
    (v : ℕ → unweightedSobolevGraph n)
    (f : Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (M : ℝ) (hM : 0 ≤ M) (hf : ‖f‖ ^ 2 = 1)
    (hvalue : ∀ k, ‖unweightedValue n (v k)‖ ^ 2 = 1)
    (hgradient : ∀ k, 4 * ‖unweightedGradient n (v k)‖ ^ 2 ≤ M)
    (hlimit : Tendsto (fun k => unweightedValue n (v k)) atTop (𝓝 f)) :
    ∃ w : unweightedSobolevGraph n,
      unweightedValue n w = f ∧ 4 * ‖unweightedGradient n w‖ ^ 2 ≤ M := by
  have hR : 0 ≤ 1 + M / 4 := by positivity
  have hbound (k : ℕ) : ‖v k‖ ≤ Real.sqrt (1 + M / 4) := by
    have hnorm := unweighted_graph_norm_sq n (v k)
    rw [hvalue k] at hnorm
    have hsquare : ‖v k‖ ^ 2 ≤ 1 + M / 4 := by nlinarith [hgradient k]
    calc
      _ = Real.sqrt (‖v k‖ ^ 2) := (Real.sqrt_sq_eq_abs ‖v k‖).trans (abs_norm _)|>.symm
      _ ≤ _ := Real.sqrt_le_sqrt hsquare
  obtain ⟨w, hw, hwnorm⟩ := ordinaryWeakScore_hilbert_bounded_preimage_limit
    (unweightedValue n) v f (Real.sqrt (1 + M / 4)) hbound hlimit
  refine ⟨w, hw, ?_⟩
  have hnorm := unweighted_graph_norm_sq n w
  rw [hw, hf] at hnorm
  have hsquare := (sq_le_sq₀ (norm_nonneg w) (Real.sqrt_nonneg _)).mpr hwnorm
  rw [Real.sq_sqrt hR] at hsquare
  nlinarith

end AffineFKProof
