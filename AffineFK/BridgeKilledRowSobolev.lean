module

public import AffineFK.BridgeKilledL2Rows
public import AffineFK.BridgeKilledLogGrid
public import AffineFK.BridgeFreeHeatL2Continuity

/-!
# Genuine H1 energy of actual killed density rows

The true free heat approximation tends strongly to the actual killed row.
Its energy is bounded by the actual killed semigroup difference, which the
proved finite logarithmic grid estimate controls. Weak graph compactness
therefore constructs the row's H1 element with the logarithmic energy bound.
No killed-generator or spectral identification is assumed.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology RealInnerProductSpace

set_option maxHeartbeats 600000 in
set_option backward.isDefEq.respectTransparency false in
theorem bridgeKilledRowL2_has_sobolev_energy (n : ℕ) (a : ℝ) (ha : 0 < a)
    (x : EuclideanSpace ℝ (Fin n)) (Ω : Set (EuclideanSpace ℝ (Fin n))) (hΩ : IsOpen Ω)
    (hpos : ∀ r : ℝ, a ≤ r → r ≤ 3*a → 0 < bridgeKilledDiagonal n r x Ω) :
    ∃ v : unweightedSobolevGraph n,
      unweightedValue n v = bridgeKilledRowL2 n a ha x Ω hΩ ∧
      ‖unweightedGradient n v‖^2 ≤ (2/a) * bridgeKilledDiagonal n (2*a) x Ω *
        (Real.log (bridgeKilledDiagonal n a x Ω) - Real.log (bridgeKilledDiagonal n (2*a) x Ω)) := by
  let τ : ℕ → ℝ := fun k => a / ((k : ℝ)+1)
  have hτ (k : ℕ) : 0 < τ k := by dsimp [τ]; positivity
  have hτle (k : ℕ) : τ k ≤ a := by
    dsimp [τ]
    apply (div_le_iff₀ (by positivity : 0 < (k : ℝ)+1)).mpr
    nlinarith [Nat.cast_nonneg (α := ℝ) k]
  have hτlim : Tendsto τ atTop (𝓝 0) := by
    simpa only [τ, div_eq_mul_inv, mul_zero] using tendsto_inverse_succ.const_mul a
  have hmh (k : ℕ) : ((k+1 : ℕ) : ℝ) * τ k = a := by
    dsimp [τ]
    push_cast
    field_simp
  let f := bridgeKilledRowL2 n a ha x Ω hΩ
  let E : ℝ := (2/a) * bridgeKilledDiagonal n (2*a) x Ω *
    (Real.log (bridgeKilledDiagonal n a x Ω) - Real.log (bridgeKilledDiagonal n (2*a) x Ω))
  choose v hv hg using fun k => bridgeFreeHeatL2_graph_energy_le_killed_difference n
    (τ k) (hτ k) Ω hΩ f (bridgeKilledRowL2_nonneg n a ha x Ω hΩ)
  have hgrid (k : ℕ) :
      (bridgeKilledDiagonal n (2*a) x Ω - bridgeKilledDiagonal n (2*a+τ k) x Ω) / τ k ≤
        (bridgeKilledDiagonal n (2*a) x Ω / a) *
          (Real.log (bridgeKilledDiagonal n a x Ω) - Real.log (bridgeKilledDiagonal n (2*a) x Ω)) := by
    apply bridgeKilledDiagonal_grid_log_slope n a (τ k) ha (hτ k) (k+1)
      (by omega) (hmh k) x Ω hΩ
    intro j hj
    have hj' : (j : ℝ) ≤ ((k+1 : ℕ) : ℝ)+1 := by exact_mod_cast hj
    have hmul := mul_le_mul_of_nonneg_right hj' (hτ k).le
    apply hpos
    · exact le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg _) (hτ k).le)
    · nlinarith [hmh k, hτle k]
  have hG (k : ℕ) : ‖unweightedGradient n (v k)‖^2 ≤ E := by
    have hk := hg k
    change τ k * ‖unweightedGradient n (v k)‖^2 ≤
      2 * (‖bridgeKilledRowL2 n a ha x Ω hΩ‖^2 -
        ⟪bridgeKilledRowL2 n a ha x Ω hΩ,
          bridgeKilledL2Operator n (τ k) (hτ k) Ω hΩ (bridgeKilledRowL2 n a ha x Ω hΩ)⟫) at hk
    rw [bridgeKilledRowL2_norm_sq, bridgeKilledRowL2_killed_inner] at hk
    change τ k * ‖unweightedGradient n (v k)‖^2 ≤
      2 * (bridgeKilledDiagonal n (2*a) x Ω - bridgeKilledDiagonal n (2*a+τ k) x Ω) at hk
    have hdiv : ‖unweightedGradient n (v k)‖^2 ≤
        2 * ((bridgeKilledDiagonal n (2*a) x Ω - bridgeKilledDiagonal n (2*a+τ k) x Ω) / τ k) := by
      rw [← mul_div_assoc]
      apply (le_div_iff₀ (hτ k)).mpr
      simpa only [mul_comm] using hk
    calc
      _ ≤ _ := hdiv
      _ ≤ 2 * ((bridgeKilledDiagonal n (2*a) x Ω / a) *
          (Real.log (bridgeKilledDiagonal n a x Ω) - Real.log (bridgeKilledDiagonal n (2*a) x Ω))) :=
        mul_le_mul_of_nonneg_left (hgrid k) (by norm_num)
      _ = E := by dsimp [E]; ring
  have hvlim : Tendsto (fun k => unweightedValue n (v k)) atTop (𝓝 f) := by
    simpa only [hv] using bridgeFreeHeatL2_tendsto_zero n τ hτ hτlim f
  obtain ⟨w, hw, henergy⟩ := bridge_unweighted_graph_limit_energy n v f
    (fun _ => E) E hG tendsto_const_nhds hvlim
  exact ⟨w, hw, henergy⟩

end AffineFKProof
