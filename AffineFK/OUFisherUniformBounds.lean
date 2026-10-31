module

public import AffineFK.GaussianHessianL2

/-!
# Actual Gaussian-smoothed ordinary Fisher and Hessian energy bounds

The second-density ratio and logarithmic score bounds are already
derived from their actual conditional representations. This finite-sum
calculation supplies explicit positive-time energy majorants for later
time integration. No information or Hessian energy bound is an input.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

theorem matrixHilbertSchmidtSq_outer (n : ℕ) (s : EuclideanSpace ℝ (Fin n)) :
    matrixHilbertSchmidtSq (fun i j : Fin n => s i * s j) = ‖s‖ ^ 4 := by
  calc
    _ = ∑ i : Fin n, ∑ j : Fin n, (s i) ^ 2 * (s j) ^ 2 := by simp only [matrixHilbertSchmidtSq, mul_pow]
    _ = (∑ i : Fin n, (s i) ^ 2) * (∑ j : Fin n, (s j) ^ 2) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
    _ = _ := by rw [← EuclideanSpace.real_norm_sq_eq]; ring

theorem matrixHilbertSchmidtSq_sub_outer_le (n : ℕ)
    (Q : Matrix (Fin n) (Fin n) ℝ) (s : EuclideanSpace ℝ (Fin n)) :
    matrixHilbertSchmidtSq (fun i j => Q i j - s i * s j) ≤
      2 * matrixHilbertSchmidtSq Q + 2 * ‖s‖ ^ 4 := by
  have h (i j : Fin n) : (Q i j - s i * s j) ^ 2 ≤
      2 * (Q i j) ^ 2 + 2 * (s i * s j) ^ 2 := by nlinarith [sq_nonneg (Q i j + s i * s j)]
  have hsum := Finset.sum_le_sum fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) =>
    Finset.sum_le_sum fun j (_ : j ∈ (Finset.univ : Finset (Fin n))) => h i j
  have houter := matrixHilbertSchmidtSq_outer n s
  simp only [matrixHilbertSchmidtSq] at houter
  simpa only [matrixHilbertSchmidtSq, Matrix.sub_apply, Finset.sum_add_distrib,
    ← Finset.mul_sum, houter] using hsum

theorem gaussianSmoothing_secondRatio_squared_energy_bound (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (a b : ℝ) (hb : 0 < b) :
    Integrable (fun x => ∑ i : Fin n, ∑ j : Fin n,
      (secondDensityRatio n (gaussianSmoothingDensity n ν a b) i j x) ^ 2)
      (densityMeasure n (gaussianSmoothingDensity n ν a b)) ∧
    (∫ x, ∑ i : Fin n, ∑ j : Fin n,
      (secondDensityRatio n (gaussianSmoothingDensity n ν a b) i j x) ^ 2
      ∂densityMeasure n (gaussianSmoothingDensity n ν a b)) ≤ (b⁻¹) ^ 4 * (n : ℝ) * (n + 1) := by
  classical
  let μ := densityMeasure n (gaussianSmoothingDensity n ν a b)
  have hi (i j : Fin n) : Integrable (fun x =>
      (secondDensityRatio n (gaussianSmoothingDensity n ν a b) i j x) ^ 2) μ :=
    (gaussianSmoothing_secondDensityRatio_memLp n ν i j a b hb).2.1
  have hisum (i : Fin n) : Integrable (fun x => ∑ j : Fin n,
      (secondDensityRatio n (gaussianSmoothingDensity n ν a b) i j x) ^ 2) μ :=
    integrable_finsetSum Finset.univ fun j _ => hi i j
  refine ⟨integrable_finsetSum Finset.univ fun i _ => hisum i, ?_⟩
  rw [integral_finsetSum Finset.univ (fun i _ => hisum i)]
  simp_rw [integral_finsetSum Finset.univ (fun j _ => hi _ j)]
  calc
    _ ≤ ∑ i : Fin n, ∑ j : Fin n, (b⁻¹) ^ 4 * (if i = j then (2 : ℝ) else 1) :=
      Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
        (gaussianSmoothing_secondDensityRatio_memLp n ν i j a b hb).2.2
    _ = _ := by
      have hrow (i : Fin n) : (∑ j : Fin n, (if i = j then (2 : ℝ) else 1)) = (n : ℝ) + 1 := by
        calc
          _ = ∑ j : Fin n, ((1 : ℝ) + if i = j then 1 else 0) := by
            apply Finset.sum_congr rfl
            intro j _
            split_ifs <;> norm_num
          _ = _ := by simp [Finset.sum_add_distrib]
      simp_rw [← Finset.mul_sum, hrow]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

theorem gaussianSmoothing_logHessian_squared_energy_bound (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (a b : ℝ) (hb : 0 < b) :
    Integrable (fun x => matrixHilbertSchmidtSq (densityLogHessian n (gaussianSmoothingDensity n ν a b) x))
      (densityMeasure n (gaussianSmoothingDensity n ν a b)) ∧
    (∫ x, matrixHilbertSchmidtSq (densityLogHessian n (gaussianSmoothingDensity n ν a b) x)
      ∂densityMeasure n (gaussianSmoothingDensity n ν a b)) ≤
        2 * (b⁻¹) ^ 4 * (n : ℝ) * (2 * n + 3) := by
  let ρ := gaussianSmoothingDensity n ν a b
  let μ := densityMeasure n ρ
  let s := gradient (fun x => Real.log (ρ x))
  let Q (x : EuclideanSpace ℝ (Fin n)) : Matrix (Fin n) (Fin n) ℝ :=
    fun i j => secondDensityRatio n ρ i j x
  have hH := gaussianSmoothing_logHessian_squared_energy_integrable n ν a b hb
  have hQ := gaussianSmoothing_secondRatio_squared_energy_bound n ν a b hb
  have hS := gaussianSmoothing_ordinaryScore_density_memLp_four n ν a b hb
  have hpoint (x : EuclideanSpace ℝ (Fin n)) :
      matrixHilbertSchmidtSq (densityLogHessian n ρ x) ≤
        2 * matrixHilbertSchmidtSq (Q x) + 2 * ‖s x‖ ^ 4 := by
    have heq : densityLogHessian n ρ x = fun i j => Q x i j - s x i * s x j := by
      ext i j
      exact densityLogHessian_eq_secondDensityRatio_sub_score_product n ρ
        (gaussianSmoothingDensity_smooth n ν a b) (gaussianSmoothingDensity_pos n ν a b hb) x i j
    rw [heq]
    exact matrixHilbertSchmidtSq_sub_outer_le n (Q x) (s x)
  refine ⟨hH, ?_⟩
  have hm := integral_mono hH ((hQ.1.const_mul 2).add (hS.2.1.const_mul 2)) hpoint
  have hbound : (∫ x, matrixHilbertSchmidtSq (densityLogHessian n ρ x) ∂μ) ≤
      2 * (∫ x, matrixHilbertSchmidtSq (Q x) ∂μ) + 2 * (∫ x, ‖s x‖ ^ 4 ∂μ) := by
    change (∫ x, matrixHilbertSchmidtSq (densityLogHessian n ρ x) ∂μ) ≤
      ∫ x, 2 * matrixHilbertSchmidtSq (Q x) + 2 * ‖s x‖ ^ 4 ∂μ at hm
    have hQi : Integrable (fun x => matrixHilbertSchmidtSq (Q x)) μ := hQ.1
    have hSi : Integrable (fun x => ‖s x‖ ^ 4) μ := hS.2.1
    rw [integral_add (f := fun x => 2 * matrixHilbertSchmidtSq (Q x))
      (g := fun x => 2 * ‖s x‖ ^ 4) (hQi.const_mul 2) (hSi.const_mul 2),
      integral_const_mul, integral_const_mul] at hm
    exact hm
  calc
    _ ≤ _ := hbound
    _ ≤ 2 * ((b⁻¹) ^ 4 * (n : ℝ) * (n + 1)) +
        2 * ((b⁻¹) ^ 4 * ((n : ℝ) * (n + 2))) :=
      add_le_add (mul_le_mul_of_nonneg_left hQ.2 (by norm_num))
        (mul_le_mul_of_nonneg_left hS.2.2 (by norm_num))
    _ = _ := by ring

theorem gaussianSmoothing_ordinary_fisher_energy_bound (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (a b : ℝ) (hb : 0 < b) :
    Integrable (fun x => ‖gradient (fun y => Real.log (gaussianSmoothingDensity n ν a b y)) x‖ ^ 2)
      (densityMeasure n (gaussianSmoothingDensity n ν a b)) ∧
    (∫ x, ‖gradient (fun y => Real.log (gaussianSmoothingDensity n ν a b y)) x‖ ^ 2
      ∂densityMeasure n (gaussianSmoothingDensity n ν a b)) ≤
        1 + (b⁻¹) ^ 4 * ((n : ℝ) * (n + 2)) := by
  let ρ := gaussianSmoothingDensity n ν a b
  let μ := densityMeasure n ρ
  have : IsProbabilityMeasure μ := by
    change IsProbabilityMeasure (densityMeasure n (gaussianSmoothingDensity n ν a b))
    rw [← gaussianSmoothingDensity_law n ν a b hb]
    infer_instance
  let s := gradient (fun x => Real.log (ρ x))
  have hS := gaussianSmoothing_ordinaryScore_density_memLp_four n ν a b hb
  have h2 : MemLp s 2 μ := hS.1.mono_exponent (by norm_num)
  have hsq : Integrable (fun x => ‖s x‖ ^ 2) μ := h2.integrable_norm_pow (by norm_num)
  refine ⟨hsq, ?_⟩
  have h := integral_mono hsq ((integrable_const (1 : ℝ)).add hS.2.1)
    (fun x => by
      change ‖s x‖ ^ 2 ≤ 1 + ‖s x‖ ^ 4
      nlinarith [sq_nonneg (‖s x‖ ^ 2 - 1)])
  have hbound : (∫ x, ‖s x‖ ^ 2 ∂μ) ≤ 1 + ∫ x, ‖s x‖ ^ 4 ∂μ := by
    change (∫ x, ‖s x‖ ^ 2 ∂μ) ≤ ∫ x, 1 + ‖s x‖ ^ 4 ∂μ at h
    rw [integral_add (integrable_const (1 : ℝ)) hS.2.1, integral_const] at h
    simpa only [probReal_univ, one_smul] using h
  exact hbound.trans (add_le_add le_rfl hS.2.2)

end AffineFKProof
