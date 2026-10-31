module

public import AffineFK.VectorPoincareRegressionWeakScore
public import AffineFK.MatrixEntryLp
public import AffineFK.ConditionalMatrixHilbertSchmidt

/-!
# Product regression for genuine relative-score derivatives

The fixed-matrix regression is integrated against the independent second
law. Actual L2 derivative matrices supply every joint and iterated L1
guard. This is the one-sided estimate in Bizeul's Lemma 8; the relative
score's moment identities are derived by the imported compact-cutoff
proof, rather than assumed cross-moment cancellations.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory TopologicalSpace Matrix
open scoped Distributions RealInnerProductSpace ENNReal NNReal ContDiff Matrix.Norms.L2Operator

theorem vectorPoincareDerivativeMatrix_memLp_two (n : ℕ)
    (μ : Measure (EuclideanSpace ℝ (Fin n)))
    (r : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hg : ∀ i : Fin n, MemLp (gradient (fun y => r y i)) 2 μ) :
    MemLp (vectorPoincareDerivativeMatrix n r) 2 μ := by
  apply matrix_memLp_two_of_entries
  intro i j
  exact (hg i).eval_piLp j

theorem matrixHilbertSchmidtSq_neg (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) :
    matrixHilbertSchmidtSq (-A) = matrixHilbertSchmidtSq A := by
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  change (-A i j) ^ 2 = (A i j) ^ 2
  exact neg_sq _

theorem weakRelativeScore_product_regression (n : ℕ)
    (ν η : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν] [IsProbabilityMeasure η]
    (P : ℝ≥0) (hP0 : 0 < P) (hP : poincareConstant n ν ≤ (P : ℝ≥0∞))
    (hmean : ∀ i : Fin n, (∫ x : EuclideanSpace ℝ (Fin n), x i ∂ν) = 0)
    (hsecond : ∀ i j : Fin n, (∫ x : EuclideanSpace ℝ (Fin n), x i * x j ∂ν) =
      if i = j then (1 : ℝ) else 0)
    (r₁ r₂ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (hr₁ : MemLp r₁ 2 ν)
    (hweak₁ : ∀ F : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), EuclideanSpace ℝ (Fin n)),
      (∫ x, ⟪r₁ x, F x⟫ ∂ν) = ∫ x, ⟪x, F x⟫ - vectorDivergence n F x ∂ν)
    (hsm₁ : ContDiff ℝ ∞ r₁)
    (hg₁ : ∀ i : Fin n, MemLp (gradient (fun y => r₁ y i)) 2 ν)
    (hg₂ : ∀ i : Fin n, MemLp (gradient (fun y => r₂ y i)) 2 η) :
    Integrable (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      matrixHilbertSchmidtSq (vectorPoincareDerivativeMatrix n r₁ p.1 - vectorPoincareDerivativeMatrix n r₂ p.2))
      (ν.prod η) ∧
    ((∫ x, ‖r₁ x‖ ^ 2 ∂ν) + (∫ y, matrixHilbertSchmidtSq (vectorPoincareDerivativeMatrix n r₂ y) ∂η)) / (P : ℝ) ≤
      ∫ p, matrixHilbertSchmidtSq
        (vectorPoincareDerivativeMatrix n r₁ p.1 - vectorPoincareDerivativeMatrix n r₂ p.2) ∂ν.prod η := by
  let E := EuclideanSpace ℝ (Fin n)
  let D₁ := vectorPoincareDerivativeMatrix n r₁
  let D₂ := vectorPoincareDerivativeMatrix n r₂
  let I := ∫ x, ‖r₁ x‖ ^ 2 ∂ν
  let q : E × E → ℝ := fun p => matrixHilbertSchmidtSq (D₁ p.1 - D₂ p.2)
  have hD₁ : MemLp D₁ 2 ν := vectorPoincareDerivativeMatrix_memLp_two n ν r₁ hg₁
  have hD₂ : MemLp D₂ 2 η := vectorPoincareDerivativeMatrix_memLp_two n η r₂ hg₂
  have hq : Integrable q (ν.prod η) := matrix_hilbertSchmidt_integrable_of_memLp (ν.prod η) n _
    ((hD₁.comp_fst η).sub (hD₂.comp_snd ν))
  have hD₂i := matrix_hilbertSchmidt_integrable_of_memLp η n D₂ hD₂
  refine ⟨hq, ?_⟩
  have hpoint (y : E) : (I + matrixHilbertSchmidtSq (D₂ y)) / (P : ℝ) ≤ ∫ x, q (x, y) ∂ν := by
    have h := (weakRelativeScore_poincare_regression n ν P hP0 hP hmean hsecond r₁ hr₁ hweak₁ hsm₁ hg₁ (-D₂ y)).2
    simpa only [matrixHilbertSchmidtSq_neg, ← sub_eq_add_neg] using h
  have hleft : Integrable (fun y => (I + matrixHilbertSchmidtSq (D₂ y)) / (P : ℝ)) η :=
    ((integrable_const I).add hD₂i).div_const _
  have hmono := integral_mono_ae hleft hq.integral_prod_right (Filter.Eventually.of_forall hpoint)
  have hmass : (∫ y, (I + matrixHilbertSchmidtSq (D₂ y)) / (P : ℝ) ∂η) =
      (I + ∫ y, matrixHilbertSchmidtSq (D₂ y) ∂η) / (P : ℝ) := by
    rw [integral_div, integral_add (integrable_const I) hD₂i, integral_const]
    simp only [probReal_univ, one_smul]
  rw [hmass, ← integral_prod_symm q hq] at hmono
  exact hmono

end AffineFKProof
