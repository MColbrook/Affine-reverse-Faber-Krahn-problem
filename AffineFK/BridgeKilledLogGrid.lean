module

public import AffineFK.BridgeKilledDiagonalConvexity
public import AffineFK.BridgeLogSlope

/-!
# Finite actual killed-diagonal logarithmic slopes

The only positivity hypotheses concern the explicitly listed finite grid
of the actual pointwise killed diagonal. Its second differences are proved
from genuine density-row Cauchy--Schwarz, not supplied as an assumption.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory Set

set_option backward.isDefEq.respectTransparency false in
theorem bridgeKilledDiagonal_grid_log_slope (n : ℕ) (a h : ℝ)
    (ha : 0 < a) (hh : 0 < h) (m : ℕ) (hm : 0 < m) (hmh : (m : ℝ)*h = a)
    (x : EuclideanSpace ℝ (Fin n)) (Ω : Set (EuclideanSpace ℝ (Fin n))) (hΩ : IsOpen Ω)
    (hpos : ∀ k : ℕ, k ≤ m+1 → 0 < bridgeKilledDiagonal n (a+(k : ℝ)*h) x Ω) :
    (bridgeKilledDiagonal n (2*a) x Ω - bridgeKilledDiagonal n (2*a+h) x Ω) / h ≤
      (bridgeKilledDiagonal n (2*a) x Ω / a) *
        (Real.log (bridgeKilledDiagonal n a x Ω) - Real.log (bridgeKilledDiagonal n (2*a) x Ω)) := by
  let ℓ : ℕ → ℝ := fun k => Real.log (bridgeKilledDiagonal n (a+(k : ℝ)*h) x Ω)
  have hsecond (k : ℕ) (hk : k < m) : 0 ≤ ℓ k - 2*ℓ (k+1) + ℓ (k+2) := by
    have he1 : a+(k : ℝ)*h+h = a+((k+1 : ℕ) : ℝ)*h := by push_cast; ring
    have he2 : a+(k : ℝ)*h+2*h = a+((k+2 : ℕ) : ℝ)*h := by push_cast; ring
    have h0 := hpos k (by omega)
    have h1 := hpos (k+1) (by omega)
    have h2 := hpos (k+2) (by omega)
    have hz := bridgeKilledDiagonal_log_second_difference n (a+(k : ℝ)*h) h
      (by positivity) hh x Ω hΩ h0 (by rwa [he1]) (by rwa [he2])
    simpa only [he1, he2, ℓ] using hz
  have ht := bridge_sequence_slope_telescope ℓ m hsecond
  have he0 : a+(0 : ℕ)*h = a := by simp
  have hem : a+(m : ℝ)*h = 2*a := by rw [hmh]; ring
  have hem1 : a+((m+1 : ℕ) : ℝ)*h = 2*a+h := by push_cast; rw [add_mul, hmh]; ring
  have hd : 0 < bridgeKilledDiagonal n (2*a) x Ω := by simpa only [hem] using hpos m (by omega)
  have hd' : 0 < bridgeKilledDiagonal n (2*a+h) x Ω := by simpa only [hem1] using hpos (m+1) le_rfl
  simp only [ℓ, Nat.cast_zero, zero_mul, add_zero, hem, hem1] at ht
  have hs := bridge_positive_sub_le_log _ _ hd hd'
  have hm0 : 0 < (m : ℝ) := Nat.cast_pos.mpr hm
  have hsm := mul_le_mul_of_nonneg_left hs hm0.le
  have htm := mul_le_mul_of_nonneg_left ht hd.le
  have hf : (m : ℝ) * (bridgeKilledDiagonal n (2*a) x Ω - bridgeKilledDiagonal n (2*a+h) x Ω) ≤
      bridgeKilledDiagonal n (2*a) x Ω *
        (Real.log (bridgeKilledDiagonal n a x Ω) - Real.log (bridgeKilledDiagonal n (2*a) x Ω)) := by
    nlinarith
  have hscaled := mul_le_mul_of_nonneg_left hf hh.le
  have hc : a * (bridgeKilledDiagonal n (2*a) x Ω - bridgeKilledDiagonal n (2*a+h) x Ω) ≤
      h * (bridgeKilledDiagonal n (2*a) x Ω *
        (Real.log (bridgeKilledDiagonal n a x Ω) - Real.log (bridgeKilledDiagonal n (2*a) x Ω))) := by
    convert hscaled using 1 <;> nlinarith [hmh]
  apply (div_le_iff₀ hh).mpr
  calc
    _ = (a * (bridgeKilledDiagonal n (2*a) x Ω - bridgeKilledDiagonal n (2*a+h) x Ω)) / a := by
      field_simp
    _ ≤ (h * (bridgeKilledDiagonal n (2*a) x Ω *
        (Real.log (bridgeKilledDiagonal n a x Ω) - Real.log (bridgeKilledDiagonal n (2*a) x Ω)))) / a :=
      div_le_div_of_nonneg_right hc ha.le
    _ = _ := by ring

end AffineFKProof
