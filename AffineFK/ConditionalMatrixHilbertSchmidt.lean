module

public import AffineFK.ConditionalCovarianceMatrix

/-!
# Actual conditional Hilbert--Schmidt contraction and matrix deficit

Conditional expectation contracts each real matrix entry in L2. Finite
summation gives contraction of the explicit squared Hilbert--Schmidt
energy, independently of the auxiliary operator norm used for Bochner
matrix integration. Positive-semidefinite comparison then gives the
matrix deficit used in Bizeul's Lemma 5, DOI 10.5802/crmath.390.
The actual marginal-Hessian comparison is a separate analytic input.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator

def matrixEntryLinear (n : ℕ) (i j : Fin n) : Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] ℝ where
  toFun A := A i j
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def matrixEntryContinuousLinear (n : ℕ) (i j : Fin n) :
    Matrix (Fin n) (Fin n) ℝ →L[ℝ] ℝ :=
  (matrixEntryLinear n i j).toContinuousLinearMap

theorem matrixEntryContinuousLinear_apply (n : ℕ) (i j : Fin n)
    (A : Matrix (Fin n) (Fin n) ℝ) : matrixEntryContinuousLinear n i j A = A i j := rfl

theorem matrix_hilbertSchmidt_integrable_of_memLp
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (n : ℕ)
    (A : Ω → Matrix (Fin n) (Fin n) ℝ) (hA : MemLp A 2 μ) :
    Integrable (fun ω => matrixHilbertSchmidtSq (A ω)) μ := by
  unfold matrixHilbertSchmidtSq
  apply integrable_finsetSum
  intro i _
  apply integrable_finsetSum
  intro j _
  have h := ((matrixEntryContinuousLinear n i j).comp_memLp' hA).integrable_norm_pow
    (by norm_num : (2 : ℕ) ≠ 0)
  simpa only [Function.comp_def, matrixEntryContinuousLinear_apply, Real.norm_eq_abs, sq_abs] using h

theorem conditional_matrix_entry
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (s : MeasurableSpace Ω)
    (n : ℕ) (A : Ω → Matrix (Fin n) (Fin n) ℝ) (hA : MemLp A 2 μ) (i j : Fin n) :
    (fun ω => condExp s μ A ω i j) =ᵐ[μ]
      condExp s μ (fun ω => A ω i j) := by
  let : MeasurableSpace Ω := mΩ
  simpa only [Function.comp_def, matrixEntryContinuousLinear_apply] using
    (matrixEntryContinuousLinear n i j).comp_condExp_comm (hA.integrable (by norm_num))

theorem conditional_matrix_hilbertSchmidt_le
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (s : MeasurableSpace Ω) (hs : s ≤ mΩ)
    (n : ℕ) (A : Ω → Matrix (Fin n) (Fin n) ℝ) (hA : MemLp A 2 μ) :
    (∫ ω, matrixHilbertSchmidtSq (condExp s μ A ω) ∂μ) ≤
      ∫ ω, matrixHilbertSchmidtSq (A ω) ∂μ := by
  let : MeasurableSpace Ω := mΩ
  have hCE : MemLp (condExp s μ A) 2 μ := hA.condExp (by norm_num)
  have hentry (F : Ω → Matrix (Fin n) (Fin n) ℝ) (hF : MemLp F 2 μ) (i j : Fin n) :
      Integrable (fun ω => (F ω i j) ^ 2) μ := by
    have h := ((matrixEntryContinuousLinear n i j).comp_memLp' hF).integrable_norm_pow
      (by norm_num : (2 : ℕ) ≠ 0)
    simpa only [Function.comp_def, matrixEntryContinuousLinear_apply, Real.norm_eq_abs, sq_abs] using h
  have hrow (F : Ω → Matrix (Fin n) (Fin n) ℝ) (hF : MemLp F 2 μ) (i : Fin n) :
      Integrable (fun ω => ∑ j, (F ω i j) ^ 2) μ :=
    integrable_finsetSum Finset.univ fun j _ => hentry F hF i j
  unfold matrixHilbertSchmidtSq
  rw [integral_finsetSum Finset.univ (fun i _ => hrow _ hCE i),
    integral_finsetSum Finset.univ (fun i _ => hrow _ hA i)]
  apply Finset.sum_le_sum
  intro i _
  rw [integral_finsetSum Finset.univ (fun j _ => hentry _ hCE i j),
    integral_finsetSum Finset.univ (fun j _ => hentry _ hA i j)]
  apply Finset.sum_le_sum
  intro j _
  have heq := conditional_matrix_entry μ s n A hA i j
  calc
    _ = ∫ ω, (condExp s μ (fun z => A z i j) ω) ^ 2 ∂μ := by
      apply integral_congr_ae
      filter_upwards [heq] with ω hω
      rw [hω]
    _ ≤ _ := by
      have h := conditional_second_moment_le μ s hs (fun ω => A ω i j)
        ((matrixEntryContinuousLinear n i j).comp_memLp' hA)
      simpa only [Real.norm_eq_abs, sq_abs] using h

theorem conditional_matrix_hilbertSchmidt_deficit
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (s : MeasurableSpace Ω) (hs : s ≤ mΩ)
    (n : ℕ) (A B C : Ω → Matrix (Fin n) (Fin n) ℝ)
    (hA : MemLp A 2 μ) (hB : MemLp B 2 μ) (hC : MemLp C 2 μ) (t : ℝ)
    (hpos : ∀ᵐ ω ∂μ, (C ω).PosSemidef)
    (hcomp : ∀ᵐ ω ∂μ, (condExp s μ (fun z => (1 - t) • A z + t • B z) ω - C ω).PosSemidef) :
    (1 - t) * (∫ ω, matrixHilbertSchmidtSq (A ω) ∂μ) +
      t * (∫ ω, matrixHilbertSchmidtSq (B ω) ∂μ) -
      (∫ ω, matrixHilbertSchmidtSq (C ω) ∂μ) ≥
      t * (1 - t) * ∫ ω, matrixHilbertSchmidtSq (A ω - B ω) ∂μ := by
  let : MeasurableSpace Ω := mΩ
  let M : Ω → Matrix (Fin n) (Fin n) ℝ := fun ω => (1 - t) • A ω + t • B ω
  have hM : MemLp M 2 μ := (hA.const_smul (1 - t)).add (hB.const_smul t)
  have hMC : MemLp (condExp s μ M) 2 μ := hM.condExp (by norm_num)
  have hAi := matrix_hilbertSchmidt_integrable_of_memLp μ n A hA
  have hBi := matrix_hilbertSchmidt_integrable_of_memLp μ n B hB
  have hDi := matrix_hilbertSchmidt_integrable_of_memLp μ n (fun ω => A ω - B ω) (hA.sub hB)
  have hCi := matrix_hilbertSchmidt_integrable_of_memLp μ n C hC
  have hMCi := matrix_hilbertSchmidt_integrable_of_memLp μ n _ hMC
  have hmono : (∫ ω, matrixHilbertSchmidtSq (C ω) ∂μ) ≤
      ∫ ω, matrixHilbertSchmidtSq (condExp s μ M ω) ∂μ := by
    apply integral_mono_ae hCi hMCi
    filter_upwards [hpos, hcomp] with ω hp hc
    exact matrixHilbertSchmidtSq_mono_of_posSemidef hp hc
  have hJ := hmono.trans (conditional_matrix_hilbertSchmidt_le μ s hs n M hM)
  have hmix : (∫ ω, matrixHilbertSchmidtSq (M ω) ∂μ) =
      (1 - t) * (∫ ω, matrixHilbertSchmidtSq (A ω) ∂μ) +
      t * (∫ ω, matrixHilbertSchmidtSq (B ω) ∂μ) -
      t * (1 - t) * ∫ ω, matrixHilbertSchmidtSq (A ω - B ω) ∂μ := by
    calc
      _ = ∫ ω, (1 - t) * matrixHilbertSchmidtSq (A ω) +
          t * matrixHilbertSchmidtSq (B ω) - t * (1 - t) * matrixHilbertSchmidtSq (A ω - B ω) ∂μ :=
        integral_congr_ae (Filter.Eventually.of_forall fun ω =>
          matrixHilbertSchmidtSq_convex_combination (A ω) (B ω) t)
      _ = _ := by
        rw [integral_sub
          (f := fun ω => (1 - t) * matrixHilbertSchmidtSq (A ω) + t * matrixHilbertSchmidtSq (B ω))
          (g := fun ω => t * (1 - t) * matrixHilbertSchmidtSq (A ω - B ω))
          ((hAi.const_mul (1 - t)).add (hBi.const_mul t)) (hDi.const_mul _),
          integral_add (f := fun ω => (1 - t) * matrixHilbertSchmidtSq (A ω))
            (g := fun ω => t * matrixHilbertSchmidtSq (B ω))
            (hAi.const_mul (1 - t)) (hBi.const_mul t),
          integral_const_mul, integral_const_mul, integral_const_mul]
  linarith

end AffineFKProof
