module

public import AffineFK.BridgeKilledKernelRow

/-!
# Inner products of the actual killed heat-kernel rows

The equality below follows from the pointwise bridge-density composition
and symmetry. In particular it identifies the selected diagonal, rather
than choosing a new almost-everywhere version of the transition density.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace

theorem bridgeKilledKernel_row_product_integrable (n : ℕ) (s t : ℝ)
    (hs : 0 < s) (ht : 0 < t) (x z : EuclideanSpace ℝ (Fin n))
    (Ω : Set (EuclideanSpace ℝ (Fin n))) (hΩ : IsOpen Ω) :
    Integrable (fun y => (bridgeKilledKernel n s x Ω y).toReal *
      (bridgeKilledKernel n t z Ω y).toReal) volume :=
  (bridgeKilledKernel_row_memLp_and_square n s hs x Ω hΩ).1.integrable_mul
    (bridgeKilledKernel_row_memLp_and_square n t ht z Ω hΩ).1

theorem bridgeKilledKernel_row_product_integral (n : ℕ) (s t : ℝ)
    (hs : 0 < s) (ht : 0 < t) (x z : EuclideanSpace ℝ (Fin n))
    (Ω : Set (EuclideanSpace ℝ (Fin n))) (hΩ : IsOpen Ω) :
    (∫ y, (bridgeKilledKernel n s x Ω y).toReal *
      (bridgeKilledKernel n t z Ω y).toReal ∂volume) =
        (bridgeKilledKernel n (s+t) x Ω z).toReal := by
  have hi := bridgeKilledKernel_row_product_integrable n s t hs ht x z Ω hΩ
  have hn (y : EuclideanSpace ℝ (Fin n)) : 0 ≤
      (bridgeKilledKernel n s x Ω y).toReal * (bridgeKilledKernel n t z Ω y).toReal :=
    mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
  have he : (∫⁻ y, ENNReal.ofReal ((bridgeKilledKernel n s x Ω y).toReal *
      (bridgeKilledKernel n t z Ω y).toReal) ∂volume) =
        bridgeKilledKernel n (s+t) x Ω z := by
    rw [bridgeKilledKernel_pointwise_semigroup n s t hs ht x z Ω hΩ]
    apply lintegral_congr
    intro y
    rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg,
      ENNReal.ofReal_toReal (bridgeKilledKernel_ne_top n s x y Ω),
      ENNReal.ofReal_toReal (bridgeKilledKernel_ne_top n t z y Ω),
      bridgeKilledKernel_symmetric n t ht z y Ω hΩ]
  have hI := ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall hn)
  rw [he] at hI
  have h := congrArg ENNReal.toReal hI
  simpa only [ENNReal.toReal_ofReal (integral_nonneg hn)] using h

theorem bridgeKilledRowL2_inner (n : ℕ) (s t : ℝ)
    (hs : 0 < s) (ht : 0 < t) (x z : EuclideanSpace ℝ (Fin n))
    (Ω : Set (EuclideanSpace ℝ (Fin n))) (hΩ : IsOpen Ω) :
    ⟪bridgeKilledRowL2 n s hs x Ω hΩ, bridgeKilledRowL2 n t ht z Ω hΩ⟫ =
      (bridgeKilledKernel n (s+t) x Ω z).toReal := by
  rw [L2.inner_def]
  calc
    _ = ∫ y, (bridgeKilledKernel n s x Ω y).toReal *
        (bridgeKilledKernel n t z Ω y).toReal ∂volume := by
      apply integral_congr_ae
      filter_upwards [bridgeKilledRowL2_coe n s hs x Ω hΩ,
        bridgeKilledRowL2_coe n t ht z Ω hΩ] with y h1 h2
      simp [h1, h2, mul_comm]
    _ = _ := bridgeKilledKernel_row_product_integral n s t hs ht x z Ω hΩ

end AffineFKProof
