module

public import AffineFK.BridgeFreeHeatSobolev
public import AffineFK.BridgeKilledRowAction

/-!
# Actual killed-to-free energy comparison for nonnegative L2 inputs

The particular killed kernel is dominated by the genuine unrestricted
kernel as a measure. Row-L1 integrability precedes integral comparison.
Nonnegativity is explicit, which suffices for the actual density rows.
No Dirichlet generator or energy identification is assumed.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory Set
open scoped RealInnerProductSpace

theorem bridgeKilledTransitionKernel_le_free (n : ℕ) (t : ℝ) (ht : 0 < t)
    (Ω : Set (EuclideanSpace ℝ (Fin n))) (hΩ : IsOpen Ω)
    (x : EuclideanSpace ℝ (Fin n)) :
    bridgeKilledTransitionKernel n t ht Ω hΩ x ≤
      bridgeKilledTransitionKernel n t ht univ isOpen_univ x := by
  rw [bridgeKilledTransitionKernel_eq_withDensity,
    bridgeKilledTransitionKernel_eq_withDensity]
  apply withDensity_mono
  exact Filter.Eventually.of_forall fun y => by
    rw [bridgeKilledKernel_univ n t ht x y]
    exact bridgeKilledKernel_le_free n t x y Ω

theorem bridgeKilledIntegral_le_free (n : ℕ) (t : ℝ) (ht : 0 < t)
    (Ω : Set (EuclideanSpace ℝ (Fin n))) (hΩ : IsOpen Ω)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : MemLp f 2 volume)
    (hf0 : 0 ≤ᵐ[volume] f) (x : EuclideanSpace ℝ (Fin n)) :
    bridgeKilledIntegral n t ht Ω hΩ f x ≤
      bridgeKilledIntegral n t ht univ isOpen_univ f x := by
  apply integral_mono_measure (bridgeKilledTransitionKernel_le_free n t ht Ω hΩ x)
  · exact hf0.filter_mono
      (bridgeKilledTransitionKernel_absolutelyContinuous_volume n t ht univ isOpen_univ x).ae_le
  · exact (bridge_memLp_killed_row n t ht univ isOpen_univ f hf x).integrable (by norm_num)

theorem bridgeKilledL2_inner_le_free (n : ℕ) (t : ℝ) (ht : 0 < t)
    (Ω : Set (EuclideanSpace ℝ (Fin n))) (hΩ : IsOpen Ω)
    (f : Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) (hf0 : 0 ≤ᵐ[volume] f) :
    ⟪f, bridgeKilledL2Operator n t ht Ω hΩ f⟫ ≤ ⟪f, bridgeFreeHeatL2 n t ht f⟫ := by
  unfold bridgeFreeHeatL2
  rw [L2.inner_def, L2.inner_def]
  apply integral_mono_ae (L2.integrable_inner _ _) (L2.integrable_inner _ _)
  filter_upwards [bridgeKilledL2Operator_coe n t ht Ω hΩ f,
    bridgeKilledL2Operator_coe n t ht univ isOpen_univ f, hf0] with x hP hQ h0
  have hi := bridgeKilledIntegral_le_free n t ht Ω hΩ f (Lp.memLp f) hf0 x
  simpa [hP, hQ, mul_comm] using mul_le_mul_of_nonneg_left hi h0

theorem bridgeFreeHeatL2_graph_energy_le_killed_difference (n : ℕ) (t : ℝ) (ht : 0 < t)
    (Ω : Set (EuclideanSpace ℝ (Fin n))) (hΩ : IsOpen Ω)
    (f : Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) (hf0 : 0 ≤ᵐ[volume] f) :
    ∃ v : unweightedSobolevGraph n, unweightedValue n v = bridgeFreeHeatL2 n t ht f ∧
      t * ‖unweightedGradient n v‖^2 ≤
        2 * (‖f‖^2 - ⟪f, bridgeKilledL2Operator n t ht Ω hΩ f⟫) := by
  obtain ⟨v, hv, henergy⟩ := bridgeFreeHeatL2_has_graph_energy n t ht f
  have hs := sq_nonneg ‖f - bridgeFreeHeatL2 n t ht f‖
  rw [norm_sub_sq_real] at hs
  have hi := bridgeKilledL2_inner_le_free n t ht Ω hΩ f hf0
  exact ⟨v, hv, by nlinarith⟩

end AffineFKProof
