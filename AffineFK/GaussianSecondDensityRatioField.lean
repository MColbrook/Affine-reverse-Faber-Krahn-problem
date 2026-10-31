module

public import AffineFK.GaussianSecondDensityRatioConditional

/-!
# The conditional field for a second Gaussian density derivative

Each fixed ordered coordinate pair has one field, chosen before all
compact tests, with the actual Gaussian conditional representation and
the exact second-moment bound. No input moment or input density is needed.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory TopologicalSpace
open scoped Distributions ENNReal

theorem stdGaussian_quadratic_square_moment (n : ℕ) (i j : Fin n) :
    Integrable (fun g : EuclideanSpace ℝ (Fin n) =>
      (g i * g j - if i = j then 1 else 0) ^ 2)
      (stdGaussian (EuclideanSpace ℝ (Fin n))) ∧
    (∫ g : EuclideanSpace ℝ (Fin n), (g i * g j - if i = j then 1 else 0) ^ 2
      ∂stdGaussian (EuclideanSpace ℝ (Fin n))) = if i = j then (2 : ℝ) else 1 := by
  classical
  have h := stdGaussian_quadratic_pair_covariance n i j i j
  simp only [← pow_two] at h
  refine ⟨h.1, ?_⟩
  by_cases hij : i = j
  · have hh := h.2
    simp [hij] at hh ⊢
    linarith
  · simpa [hij, Ne.symm hij] using h.2

theorem gaussianSmoothing_second_density_field (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (i j : Fin n) (a b : ℝ) (hb : b ≠ 0) :
    ∃ q : EuclideanSpace ℝ (Fin n) → ℝ,
      StronglyMeasurable q ∧
      MemLp q 2 ((ν.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))).map
        (fun p => a • p.1 + b • p.2)) ∧
      (∀ p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n),
        q (a • p.1 + b • p.2) = (b⁻¹) ^ 2 * condExp
          ((inferInstance : MeasurableSpace (EuclideanSpace ℝ (Fin n))).comap
            (fun z : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) => a • z.1 + b • z.2))
          (ν.prod (stdGaussian (EuclideanSpace ℝ (Fin n))))
          (fun z => z.2 i * z.2 j - if i = j then 1 else 0) p) ∧
      (∫ x, (q x) ^ 2 ∂(ν.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))).map
        (fun p => a • p.1 + b • p.2)) ≤ (b⁻¹) ^ 4 * (if i = j then (2 : ℝ) else 1) ∧
      ∀ φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ),
        Integrable (fun x => q x * φ x)
          ((ν.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))).map
            (fun p => a • p.1 + b • p.2)) ∧
        Integrable (partialTest n i (partialTest n j φ))
          ((ν.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))).map
            (fun p => a • p.1 + b • p.2)) ∧
        (∫ x, q x * φ x ∂(ν.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))).map
          (fun p => a • p.1 + b • p.2)) =
          ∫ x, partialTest n i (partialTest n j φ) x
            ∂(ν.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))).map
              (fun p => a • p.1 + b • p.2) := by
  let γ := stdGaussian (EuclideanSpace ℝ (Fin n))
  let μ := ν.prod γ
  let W : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) :=
    fun p => a • p.1 + b • p.2
  let A : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) → ℝ :=
    fun p => p.2 i * p.2 j - if i = j then 1 else 0
  have hW : Measurable W := by fun_prop
  have : IsProbabilityMeasure (μ.map W) := (hasLaw_map hW.aemeasurable).isProbabilityMeasure_iff.mp inferInstance
  have hA : MemLp A 2 μ := (stdGaussian_quadratic_memLp n i j).comp_snd ν
  obtain ⟨q, hq, hq2, hrep, hbound, hpair⟩ :=
    scaled_conditional_scalar_field μ A hA W hW ((b⁻¹) ^ 2)
  have hA2 : Integrable (fun p => (A p) ^ 2) μ := by
    simpa only [Real.norm_eq_abs, sq_abs] using hA.integrable_norm_pow (by norm_num)
  have hmoment : (∫ p, (A p) ^ 2 ∂μ) = if i = j then (2 : ℝ) else 1 := by
    rw [integral_prod _ hA2]
    have hG := (stdGaussian_quadratic_square_moment n i j).2
    change (∫ u, (∫ g : EuclideanSpace ℝ (Fin n),
      (g i * g j - if i = j then 1 else 0) ^ 2 ∂γ) ∂ν) = _
    rw [hG]
    simp
  refine ⟨q, hq, hq2, hrep, ?_, ?_⟩
  · calc
      _ ≤ ((b⁻¹) ^ 2) ^ 2 * (∫ p, (A p) ^ 2 ∂μ) := hbound
      _ = _ := by rw [hmoment]; ring
  · intro φ
    have hφ : MemLp φ 2 (μ.map W) :=
      (Lp.memLp (testFunctionToL2 (μ.map W) φ)).ae_eq (testFunctionToL2_coe (μ.map W) φ)
    have hp := hpair φ φ.continuous.stronglyMeasurable hφ
    have hG := product_gaussian_second_integration_by_parts n ν i j a b hb φ
    have hd : MemLp (partialTest n i (partialTest n j φ)) 2 (μ.map W) :=
      (Lp.memLp (testFunctionToL2 (μ.map W) (partialTest n i (partialTest n j φ)))).ae_eq
        (testFunctionToL2_coe (μ.map W) (partialTest n i (partialTest n j φ)))
    refine ⟨hp.1, hd.integrable (by norm_num), ?_⟩
    calc
      _ = (b⁻¹) ^ 2 * (∫ p, A p * φ (W p) ∂μ) := hp.2.2
      _ = (b⁻¹) ^ 2 * (b ^ 2 * (∫ p, partialTest n i (partialTest n j φ) (W p) ∂μ)) := by
        rw [hG.2.2]
      _ = ∫ p, partialTest n i (partialTest n j φ) (W p) ∂μ := by
        rw [← mul_assoc, ← mul_pow, inv_mul_cancel₀ hb, one_pow, one_mul]
      _ = _ := (integral_map hW.aemeasurable
        (partialTest n i (partialTest n j φ)).continuous.aestronglyMeasurable).symm

end AffineFKProof
