module

public import Mathlib.Analysis.Matrix.Order
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith

/-!
# Hilbert--Schmidt squared energy and positive-semidefinite matrix order

The energy here is the explicit sum of squared real entries. Matrix
operator norms occur only in Mathlib's auxiliary C-star square-root
factorisation, never as the Hilbert--Schmidt quantity in the statements.

These are the deterministic matrix steps in Bizeul, Entropy and
Information jump for log-concave vectors (2023), Lemma 5, DOI
10.5802/crmath.390. The source's probabilistic Hessian comparison and
conditional Jensen steps are separate assertions.

Primary reuse: Matrix.PosSemidef and conjugation/trace positivity by
Alexander Bentkamp and Mohanad Ahmed; matrix order by Monica Omar;
C-star square-root factorisation by Frederic Dupuis and contributors;
matrix C-star structure by Hans Parshall (Mathlib, Apache-2.0).
-/

@[expose] public noncomputable section
namespace AffineFKProof
open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator

/-- The squared Hilbert--Schmidt norm: the sum of squared entries. -/
def matrixHilbertSchmidtSq {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℝ) : ℝ := ∑ i, ∑ j, (A i j) ^ 2

theorem matrixHilbertSchmidtSq_nonneg {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℝ) : 0 ≤ matrixHilbertSchmidtSq A := by
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg (A i j)

theorem matrixHilbertSchmidtSq_add {m n : Type*} [Fintype m] [Fintype n]
    (A B : Matrix m n ℝ) :
    matrixHilbertSchmidtSq (A + B) = matrixHilbertSchmidtSq A +
      2 * (∑ i, ∑ j, A i j * B i j) + matrixHilbertSchmidtSq B := by
  classical
  calc
    _ = ∑ i, ∑ j, ((A i j) ^ 2 + 2 * (A i j * B i j) + (B i j) ^ 2) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      simp only [Matrix.add_apply]
      ring
    _ = _ := by
      simp only [matrixHilbertSchmidtSq, Finset.sum_add_distrib, Finset.mul_sum]

theorem matrix_trace_mul_nonneg_of_posSemidef {n : Type*} [Fintype n]
    {A B : Matrix n n ℝ} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    0 ≤ (A * B).trace := by
  classical
  obtain ⟨P, hP⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA.nonneg
  have hP' : A = Pᴴ * P := by simpa only [Matrix.star_eq_conjTranspose] using hP
  have htrace := (hB.mul_mul_conjTranspose_same P).trace_nonneg
  rwa [Matrix.trace_mul_cycle, ← hP'] at htrace

theorem matrix_entry_pairing_eq_trace_mul {n : Type*} [Fintype n]
    (A B : Matrix n n ℝ) (hB : B.IsHermitian) :
    (∑ i, ∑ j, A i j * B i j) = (A * B).trace := by
  classical
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have hsym : B j i = B i j := by simpa only [star_trivial] using hB.apply i j
  rw [hsym]

theorem matrix_entry_pairing_nonneg_of_posSemidef {n : Type*} [Fintype n]
    {A B : Matrix n n ℝ} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    0 ≤ ∑ i, ∑ j, A i j * B i j := by
  rw [matrix_entry_pairing_eq_trace_mul A B hB.isHermitian]
  exact matrix_trace_mul_nonneg_of_posSemidef hA hB

theorem matrixHilbertSchmidtSq_mono_of_posSemidef {n : Type*} [Fintype n]
    {A B : Matrix n n ℝ} (hA : A.PosSemidef) (hBA : (B - A).PosSemidef) :
    matrixHilbertSchmidtSq A ≤ matrixHilbertSchmidtSq B := by
  have hinner := matrix_entry_pairing_nonneg_of_posSemidef hA hBA
  have hsquare := matrixHilbertSchmidtSq_nonneg (B - A)
  have hsum : A + (B - A) = B := by ext i j; simp
  have hexpand := matrixHilbertSchmidtSq_add A (B - A)
  rw [hsum] at hexpand
  linarith

theorem matrixHilbertSchmidtSq_convex_combination {m n : Type*} [Fintype m] [Fintype n]
    (A B : Matrix m n ℝ) (t : ℝ) :
    matrixHilbertSchmidtSq ((1 - t) • A + t • B) =
      (1 - t) * matrixHilbertSchmidtSq A + t * matrixHilbertSchmidtSq B -
        t * (1 - t) * matrixHilbertSchmidtSq (A - B) := by
  classical
  calc
    _ = ∑ i, ∑ j, ((1 - t) * (A i j) ^ 2 + t * (B i j) ^ 2 -
        t * (1 - t) * (A i j - B i j) ^ 2) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
      ring
    _ = _ := by
      simp only [matrixHilbertSchmidtSq, Matrix.sub_apply, Finset.sum_add_distrib,
        Finset.sum_sub_distrib, Finset.mul_sum]

theorem matrixHilbertSchmidtSq_convex_combination_gap {m n : Type*} [Fintype m] [Fintype n]
    (A B : Matrix m n ℝ) (t : ℝ) :
    (1 - t) * matrixHilbertSchmidtSq A + t * matrixHilbertSchmidtSq B -
      matrixHilbertSchmidtSq ((1 - t) • A + t • B) =
        t * (1 - t) * matrixHilbertSchmidtSq (A - B) := by
  rw [matrixHilbertSchmidtSq_convex_combination]
  ring

theorem matrixHilbertSchmidtSq_convex_combination_le {m n : Type*} [Fintype m] [Fintype n]
    (A B : Matrix m n ℝ) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    matrixHilbertSchmidtSq ((1 - t) • A + t • B) ≤
      (1 - t) * matrixHilbertSchmidtSq A + t * matrixHilbertSchmidtSq B := by
  rw [matrixHilbertSchmidtSq_convex_combination]
  exact sub_le_self _ (mul_nonneg (mul_nonneg ht0 (sub_nonneg.mpr ht1))
    (matrixHilbertSchmidtSq_nonneg (A - B)))

end AffineFKProof
