module

public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Tactic

/-!
# Smooth scalar truncations for relative entropy

The shifted entropy has value and first derivative zero at one. Subtracting
two shifts gives a convex entropy with bounded first derivative and a
Fisher coefficient between zero and r. The scalar derivative identities
below use the ordinary logarithm and genuine kernel-checked field algebra.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open scoped ContDiff

/-- The shifted entropy (r+z) log((r+z)/(1+z))-r+1. -/
def entropyShift (z r : ℝ) : ℝ :=
  (r + z) * Real.log ((r + z) / (1 + z)) - r + 1

/-- The difference of two shifted entropies, for 0<epsilon<L. -/
def entropyTruncation (ε L r : ℝ) : ℝ := entropyShift ε r - entropyShift L r

/-- The actual first derivative of the truncated entropy on the nonnegative axis. -/
def entropyTruncationDeriv (ε L r : ℝ) : ℝ :=
  Real.log ((r + ε) / (1 + ε)) - Real.log ((r + L) / (1 + L))

theorem entropyShift_hasDerivAt (z r : ℝ) (hz : 0 < z) (hr : 0 ≤ r) :
    HasDerivAt (entropyShift z) (Real.log ((r + z) / (1 + z))) r := by
  change HasDerivAt (fun x : ℝ => (x + z) * Real.log ((x + z) / (1 + z)) - x + 1) _ r
  have hrz : 0 < r + z := by linarith
  have h1z : 0 < 1 + z := by linarith
  have hlog := (((hasDerivAt_id r).add_const z).div_const (1 + z)).log
    (div_pos hrz h1z).ne'
  have hlog' : HasDerivAt (fun x : ℝ => Real.log ((x + z) / (1 + z))) (r + z)⁻¹ r := by
    convert hlog using 1 <;> simp only [id_eq] <;> field_simp [hrz.ne', h1z.ne']
  have h : HasDerivAt (fun x : ℝ => (x + z) * Real.log ((x + z) / (1 + z)) - x + 1)
      (1 * Real.log ((r + z) / (1 + z)) + (r + z) * (r + z)⁻¹ - 1) r := by
    apply HasDerivAt.add_const
    apply HasDerivAt.sub
    · exact ((hasDerivAt_id r).add_const z).mul hlog'
    · exact hasDerivAt_id r
  simpa only [one_mul, mul_inv_cancel₀ hrz.ne', add_sub_cancel_right] using h

theorem entropyTruncation_hasDerivAt (ε L r : ℝ)
    (hε : 0 < ε) (hL : 0 < L) (hr : 0 ≤ r) :
    HasDerivAt (entropyTruncation ε L) (entropyTruncationDeriv ε L r) r :=
  (entropyShift_hasDerivAt ε r hε hr).sub (entropyShift_hasDerivAt L r hL hr)

theorem entropyTruncationDeriv_hasDerivAt (ε L r : ℝ)
    (hε : 0 < ε) (hL : 0 < L) (hr : 0 ≤ r) :
    HasDerivAt (entropyTruncationDeriv ε L) ((r + ε)⁻¹ - (r + L)⁻¹) r := by
  have hlog (z : ℝ) (hz : 0 < z) :
      HasDerivAt (fun x : ℝ => Real.log ((x + z) / (1 + z))) (r + z)⁻¹ r := by
    have hrz : 0 < r + z := by linarith
    have h1z : 0 < 1 + z := by linarith
    convert ((((hasDerivAt_id r).add_const z).div_const (1 + z)).log
      (div_pos hrz h1z).ne') using 1 <;> simp only [id_eq] <;> field_simp [hrz.ne', h1z.ne']
  exact (hlog ε hε).sub (hlog L hL)

theorem entropyTruncation_contDiffAt (ε L r : ℝ)
    (hε : 0 < ε) (hL : 0 < L) (hr : 0 ≤ r) :
    ContDiffAt ℝ ∞ (entropyTruncation ε L) r := by
  unfold entropyTruncation entropyShift
  fun_prop (disch := positivity)

theorem entropyTruncation_fisher_coefficient (ε L r : ℝ)
    (hε : 0 < ε) (hεL : ε ≤ L) (hr : 0 ≤ r) :
    0 ≤ r ^ 2 * ((r + ε)⁻¹ - (r + L)⁻¹) ∧
      r ^ 2 * ((r + ε)⁻¹ - (r + L)⁻¹) ≤ r := by
  have hL : 0 < L := hε.trans_le hεL
  have hrε : 0 < r + ε := by linarith
  have hrL : 0 < r + L := by linarith
  have hid : (r + ε)⁻¹ - (r + L)⁻¹ = (L - ε) / ((r + ε) * (r + L)) := by
    field_simp
    ring
  refine ⟨mul_nonneg (sq_nonneg r) (by rw [hid]; positivity), ?_⟩
  calc
    _ ≤ r ^ 2 * (r + ε)⁻¹ :=
      mul_le_mul_of_nonneg_left (sub_le_self _ (inv_nonneg.mpr hrL.le)) (sq_nonneg r)
    _ = r ^ 2 / (r + ε) := by rw [div_eq_mul_inv]
    _ ≤ r := (div_le_iff₀ hrε).mpr (by nlinarith)

theorem entropyTruncation_at_one (ε L : ℝ) (hε : 0 < ε) (hL : 0 < L) :
    entropyTruncation ε L 1 = 0 ∧ entropyTruncationDeriv ε L 1 = 0 := by
  have h1ε : (1 : ℝ) + ε ≠ 0 := by positivity
  have h1L : (1 : ℝ) + L ≠ 0 := by positivity
  simp [entropyTruncation, entropyTruncationDeriv, entropyShift, h1ε, h1L]

end AffineFKProof
