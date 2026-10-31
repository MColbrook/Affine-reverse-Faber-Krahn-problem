module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.FieldSimp

/-!
# Scalar steps in the affine reverse Faber--Krahn manuscript

These are unconditional real inequalities and explicit conditional algebraic
implications. They do not assert that a Dirichlet eigenvalue, entropy, covariance,
or Stein tensor satisfies an analytic premise.

Source: Colbrook--Stepaniants, `source/affine_reverse_faber_krahn.tex`.
Reuse: Mathlib's `Real.sq_sqrt`, `Real.sqrt_mul` and ordered-field lemmas;
`linarith`, `nlinarith`, `norm_num`, `ring` and `field_simp` construct proof terms
checked by the Lean kernel. No native decision procedure is used.
-/

@[expose] public section
namespace AffineFKProof

/-- Young's inequality with the exact square-root term used in the final proof. -/
theorem young_sqrt (C n l : ℝ) (hn : 0 ≤ n) (hl : 0 ≤ l) :
    C * Real.sqrt (n * l) ≤ l / 2 + C ^ 2 * n / 2 := by
  rw [Real.sqrt_mul hn]
  nlinarith [sq_nonneg (Real.sqrt l - C * Real.sqrt n),
    Real.sq_sqrt hn, Real.sq_sqrt hl]

/-- Absorption, with the explicit constant appearing in the manuscript.
The premise is an inequality between real numbers, not a spectral theorem. -/
theorem absorb_sublinear (C n l : ℝ) (_hC : 0 ≤ C) (hn : 0 ≤ n)
    (hl : 0 ≤ l) (h : l ≤ C * (n + Real.sqrt (n * l))) :
    l ≤ (2 * C + C ^ 2) * n := by
  have hy := young_sqrt C n l hn hl
  nlinarith

/-- The same absorption in a form in which the factor of eight is retained. -/
theorem absorb_information_bound (C n l : ℝ) (hC : 0 ≤ C) (hn : 0 ≤ n)
    (hl : 0 ≤ l) (h : l ≤ C * (n + Real.sqrt (n * (8 * l + n)))) :
    l ≤ (4 * C + 8 * C ^ 2) * n := by
  have hs : Real.sqrt (n * (8 * l + n)) ≤
      Real.sqrt (8 * n * l) + n := by
    have hprod : 0 ≤ 8 * n * l := by positivity
    have hs0 := Real.sqrt_nonneg (n * (8 * l + n))
    have hs1 := Real.sqrt_nonneg (8 * n * l)
    have hs2 := Real.sq_sqrt (show 0 ≤ n * (8 * l + n) by positivity)
    have hs3 := Real.sq_sqrt hprod
    nlinarith
  have hy := young_sqrt C (8 * n) l (by positivity) hl
  have hc := mul_le_mul_of_nonneg_left hs hC
  nlinarith

/-- The ground-state information bound is this arithmetic consequence of the
energy identity and the covariance/second-moment bound. Those premises remain
analytic obligations outside this theorem. -/
theorem groundstate_information_arithmetic (J l moment n : ℝ)
    (hidentity : J = 4 * l + moment) (hmoment : moment ≤ n) :
    J ≤ 4 * l + n := by
  linarith

/-- Exact conversion to relative information after convolution and whitening.
No probability measure is hidden in these real-valued parameters. -/
theorem whitened_information_arithmetic (JZ JY I l n : ℝ)
    (hZ : JZ ≤ 2 * JY) (hY : JY ≤ 4 * l + n) (hI : I = JZ - n) :
    I ≤ 8 * l + n := by
  linarith

/-- Squared tensor-norm scaling after the cross-term cancellation and Jensen
estimates have been established. `m > 0` is essential. -/
theorem tensor_scaling_arithmetic (m B value : ℝ) (hm : 0 < m)
    (h : value ≤ m⁻¹ ^ 3 * (m * B)) : value ≤ B / m ^ 2 := by
  have heq : m⁻¹ ^ 3 * (m * B) = B / m ^ 2 := by
    field_simp
  simpa only [heq] using h

/-- The exponent in the information jump gives a genuine contraction factor. -/
theorem jump_factor_bounds (P : ℝ) (hP : 2 ≤ P) :
    (15 / 16 : ℝ) ≤ 1 - 1 / (8 * P) ∧ 1 - 1 / (8 * P) < 1 := by
  have hp : 0 < 8 * P := by linarith
  constructor
  · have hi : 1 / (8 * P) ≤ (1 / 16 : ℝ) := by
      apply (div_le_div_iff₀ hp (by norm_num : (0 : ℝ) < 16)).2
      nlinarith
    linarith
  · have hi : 0 < 1 / (8 * P) := by positivity
    linarith

/-- The dyadic contraction iteration itself, before any identification with
Fisher information. All nontrivial analytic hypotheses remain explicit. -/
theorem dyadic_contraction_iteration (q I₀ : ℝ) (hq : 0 ≤ q)
    (F : ℕ → ℝ) (hzero : F 0 ≤ I₀)
    (hstep : ∀ r, F (r + 1) ≤ q * F r) (r : ℕ) :
    F r ≤ q ^ r * I₀ := by
  induction r with
  | zero => simpa using hzero
  | succ r ihr =>
    calc
      F (r + 1) ≤ q * F r := hstep r
      _ ≤ q * (q ^ r * I₀) := mul_le_mul_of_nonneg_left ihr hq
      _ = q ^ (r + 1) * I₀ := by ring

end AffineFKProof
