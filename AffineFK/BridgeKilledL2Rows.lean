module

public import AffineFK.BridgeKilledFreeEnergy
public import AffineFK.BridgeKilledDiagonalConvexity
public import AffineFK.BridgeKilledKernelSupport

/-!
# Positive density rows and their actual L2 semigroup action
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory Set
open scoped RealInnerProductSpace

theorem bridgeKilledRowL2_nonneg (n : ℕ) (t : ℝ) (ht : 0 < t)
    (x : EuclideanSpace ℝ (Fin n)) (Ω : Set (EuclideanSpace ℝ (Fin n))) (hΩ : IsOpen Ω) :
    0 ≤ᵐ[volume] (bridgeKilledRowL2 n t ht x Ω hΩ : EuclideanSpace ℝ (Fin n) → ℝ) := by
  filter_upwards [bridgeKilledRowL2_coe n t ht x Ω hΩ] with y hy
  rw [hy]
  exact ENNReal.toReal_nonneg

theorem bridgeKilledL2Operator_row (n : ℕ) (s t : ℝ) (hs : 0 < s) (ht : 0 < t)
    (x : EuclideanSpace ℝ (Fin n)) (Ω : Set (EuclideanSpace ℝ (Fin n))) (hΩ : IsOpen Ω) :
    bridgeKilledL2Operator n s hs Ω hΩ (bridgeKilledRowL2 n t ht x Ω hΩ) =
      bridgeKilledRowL2 n (s+t) (add_pos hs ht) x Ω hΩ := by
  have he := bridgeKilledIntegral_congr_ae_input n s hs Ω hΩ _ _
    (bridgeKilledRowL2_coe n t ht x Ω hΩ)
  apply Lp.ext
  filter_upwards [bridgeKilledL2Operator_coe n s hs Ω hΩ (bridgeKilledRowL2 n t ht x Ω hΩ),
    bridgeKilledRowL2_coe n (s+t) (add_pos hs ht) x Ω hΩ] with z hP hr
  rw [hP, hr, congrFun he z]
  exact bridgeKilledIntegral_row n s t hs ht Ω hΩ x z

theorem bridgeKilledRowL2_killed_inner (n : ℕ) (s t : ℝ) (hs : 0 < s) (ht : 0 < t)
    (x : EuclideanSpace ℝ (Fin n)) (Ω : Set (EuclideanSpace ℝ (Fin n))) (hΩ : IsOpen Ω) :
    ⟪bridgeKilledRowL2 n t ht x Ω hΩ,
      bridgeKilledL2Operator n s hs Ω hΩ (bridgeKilledRowL2 n t ht x Ω hΩ)⟫ =
        bridgeKilledDiagonal n (2*t+s) x Ω := by
  rw [bridgeKilledL2Operator_row, bridgeKilledRowL2_inner]
  have he : t+(s+t)=2*t+s := by ring
  rw [he]
  rfl

theorem bridgeKilledRowL2_zero_exterior (n : ℕ) (t : ℝ) (ht : 0 < t)
    (x : EuclideanSpace ℝ (Fin n)) (Ω : Set (EuclideanSpace ℝ (Fin n))) (hΩ : IsOpen Ω) :
    ∀ᵐ y ∂volume, y ∉ Ω → bridgeKilledRowL2 n t ht x Ω hΩ y = 0 := by
  filter_upwards [bridgeKilledRowL2_coe n t ht x Ω hΩ] with y hy
  intro hyΩ
  rw [hy, bridgeKilledKernel_zero_of_end n t ht x y Ω hΩ hyΩ,
    ENNReal.toReal_zero]

end AffineFKProof
