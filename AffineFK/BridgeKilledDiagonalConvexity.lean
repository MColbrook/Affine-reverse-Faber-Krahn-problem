module

public import AffineFK.BridgeKilledRowInner
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Actual killed-kernel diagonal Cauchy and logarithmic convexity

The particular diagonal is the squared norm of a genuine density row.
Cauchy--Schwarz and its exact row cross inner product prove midpoint
logarithmic convexity wherever the three actual diagonal values are positive.
Positivity is explicit here and is discharged separately by a bridge bound.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory Set
open scoped RealInnerProductSpace

def bridgeKilledDiagonal (n : ℕ) (t : ℝ) (x : EuclideanSpace ℝ (Fin n))
    (Ω : Set (EuclideanSpace ℝ (Fin n))) : ℝ := (bridgeKilledKernel n t x Ω x).toReal

theorem bridgeKilledDiagonal_nonneg (n : ℕ) (t : ℝ) (x : EuclideanSpace ℝ (Fin n))
    (Ω : Set (EuclideanSpace ℝ (Fin n))) : 0 ≤ bridgeKilledDiagonal n t x Ω :=
  ENNReal.toReal_nonneg

theorem bridgeKilledDiagonal_cauchy (n : ℕ) (s t : ℝ) (hs : 0 < s) (ht : 0 < t)
    (x : EuclideanSpace ℝ (Fin n)) (Ω : Set (EuclideanSpace ℝ (Fin n))) (hΩ : IsOpen Ω) :
    (bridgeKilledDiagonal n (s+t) x Ω)^2 ≤
      bridgeKilledDiagonal n (2*s) x Ω * bridgeKilledDiagonal n (2*t) x Ω := by
  have h := norm_inner_le_norm (𝕜 := ℝ) (bridgeKilledRowL2 n s hs x Ω hΩ)
    (bridgeKilledRowL2 n t ht x Ω hΩ)
  have h2 := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr h
  simpa only [bridgeKilledRowL2_inner, Real.norm_eq_abs, sq_abs, mul_pow,
    bridgeKilledRowL2_norm_sq, bridgeKilledDiagonal] using h2

theorem bridgeKilledDiagonal_log_second_difference (n : ℕ) (r h : ℝ)
    (hr : 0 < r) (hh : 0 < h) (x : EuclideanSpace ℝ (Fin n))
    (Ω : Set (EuclideanSpace ℝ (Fin n))) (hΩ : IsOpen Ω)
    (h0 : 0 < bridgeKilledDiagonal n r x Ω)
    (h1 : 0 < bridgeKilledDiagonal n (r+h) x Ω)
    (h2 : 0 < bridgeKilledDiagonal n (r+2*h) x Ω) :
    0 ≤ Real.log (bridgeKilledDiagonal n r x Ω) -
      2 * Real.log (bridgeKilledDiagonal n (r+h) x Ω) +
        Real.log (bridgeKilledDiagonal n (r+2*h) x Ω) := by
  have hc := bridgeKilledDiagonal_cauchy n (r/2) ((r+2*h)/2)
    (by positivity) (by positivity) x Ω hΩ
  have he1 : r/2+(r+2*h)/2 = r+h := by ring
  have he2 : 2*(r/2) = r := by ring
  have he3 : 2*((r+2*h)/2) = r+2*h := by ring
  rw [he1, he2, he3] at hc
  have hl := Real.log_le_log (sq_pos_of_pos h1) hc
  rw [Real.log_pow, Real.log_mul h0.ne' h2.ne'] at hl
  norm_num only [Nat.cast_ofNat] at hl
  nlinarith

end AffineFKProof
