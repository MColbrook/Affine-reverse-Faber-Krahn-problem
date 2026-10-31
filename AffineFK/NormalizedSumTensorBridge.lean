module

public import AffineFK.NormalizedSumSteinIdentity
public import AffineFK.ConditionalTensorContraction
public import AffineFK.VectorSteinIdentity

/-!
# The conditional tensor satisfies the normalized-sum Stein identity

The actual summation map is measurable, its coordinate second moments are
finite, and the tensor representation is paired against genuine second
partials before changing variables to the sum's law. All scalar and vector
test identities use the same supplied tensor field.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory TopologicalSpace
open scoped Distributions RealInnerProductSpace

theorem normalizedSum_measurable
    {Ω : Type*} [MeasurableSpace Ω] (n m : ℕ)
    (U : Fin m → Ω → EuclideanSpace ℝ (Fin n)) (hU : ∀ ℓ, Measurable (U ℓ)) :
    Measurable (normalizedSum n m U) :=
  (Finset.measurable_fun_sum Finset.univ (fun ℓ _hℓ => hU ℓ)).const_smul ((Real.sqrt (m : ℝ))⁻¹)

theorem normalized_sum_coordinate_memLp
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (n m : ℕ) (ν : Measure (EuclideanSpace ℝ (Fin n)))
    (U : Fin m → Ω → EuclideanSpace ℝ (Fin n)) (hU : ∀ ℓ, HasLaw (U ℓ) ν μ)
    (hUmeas : ∀ ℓ, Measurable (U ℓ)) (i : Fin n)
    (hxi : MemLp (fun x : EuclideanSpace ℝ (Fin n) => x i) 2 ν) :
    MemLp (fun x : EuclideanSpace ℝ (Fin n) => x i) 2 (μ.map (normalizedSum n m U)) := by
  let a := (Real.sqrt (m : ℝ))⁻¹
  have hsum : MemLp (fun ω => ∑ ℓ, U ℓ ω i) 2 μ :=
    memLp_finsetSum Finset.univ (fun ℓ _hℓ => (hU ℓ).memLp_fun_comp hxi)
  have hcoord (ω : Ω) : normalizedSum n m U ω i = a * ∑ ℓ, U ℓ ω i := by
    change (a • ∑ ℓ, U ℓ ω) i = a * ∑ ℓ, U ℓ ω i
    rw [PiLp.smul_apply, smul_eq_mul]
    congr 1
    simpa only [coordinateFunctional_apply] using
      map_sum (coordinateFunctional n i) (fun ℓ : Fin m => U ℓ ω) Finset.univ
  have hmem : MemLp (fun ω => normalizedSum n m U ω i) 2 μ := by
    apply (hsum.const_smul a).ae_eq
    exact Filter.Eventually.of_forall fun ω => (hcoord ω).symm
  have hc : Continuous (fun x : EuclideanSpace ℝ (Fin n) => x i) := by
    have heq : (coordinateFunctional n i : EuclideanSpace ℝ (Fin n) → ℝ) = (fun x => x i) :=
      funext (coordinateFunctional_apply n i)
    rw [← heq]
    exact (coordinateFunctional n i).continuous
  apply (memLp_map_measure_iff hc.aestronglyMeasurable
    (normalizedSum_measurable n m U hUmeas).aemeasurable).mpr
  simpa only [Function.comp_def] using hmem

theorem tensor_coordinate_sum
    {ι : Type*} [Fintype ι] (n : ℕ)
    (A : ι → EuclideanSpace ℝ (Fin n × Fin n × Fin n)) (p : Fin n × Fin n × Fin n) :
    (∑ ℓ, A ℓ) p = ∑ ℓ, A ℓ p := by
  have h := map_sum (innerSL ℝ (EuclideanSpace.basisFun (Fin n × Fin n × Fin n) ℝ p)) A Finset.univ
  change ⟪EuclideanSpace.basisFun (Fin n × Fin n × Fin n) ℝ p, ∑ ℓ, A ℓ⟫ =
    ∑ ℓ, ⟪EuclideanSpace.basisFun (Fin n × Fin n × Fin n) ℝ p, A ℓ⟫ at h
  simpa only [EuclideanSpace.basisFun_inner] using h

theorem sum_tensor_partial_contraction
    (n m : ℕ) (A : Fin m → EuclideanSpace ℝ (Fin n × Fin n × Fin n)) (i : Fin n)
    (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ)) (x : EuclideanSpace ℝ (Fin n)) :
    (∑ j : Fin n, ∑ k : Fin n,
      (∑ ℓ, A ℓ) (i, j, k) * partialTest n k (partialTest n j φ) x) =
      ∑ ℓ, ∑ j : Fin n, ∑ k : Fin n, A ℓ (i, j, k) * partialTest n k (partialTest n j φ) x := by
  simp_rw [tensor_coordinate_sum, Finset.sum_mul]
  calc
    _ = ∑ j : Fin n, ∑ ℓ : Fin m, ∑ k : Fin n,
        A ℓ (i, j, k) * partialTest n k (partialTest n j φ) x := by
      apply Finset.sum_congr rfl
      intro j _hj
      exact Finset.sum_comm
    _ = _ := Finset.sum_comm

theorem normalized_sum_tensor_identity_of_representation
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (n m : ℕ) (hm : 0 < m) (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (U : Fin m → Ω → EuclideanSpace ℝ (Fin n)) (hU : ∀ ℓ, HasLaw (U ℓ) ν μ)
    (hUmeas : ∀ ℓ, Measurable (U ℓ)) (hind : iIndepFun U μ)
    (T : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n × Fin n × Fin n))
    (hT : MemLp T 2 ν)
    (hxi : ∀ i : Fin n, MemLp (fun x : EuclideanSpace ℝ (Fin n) => x i) 2 ν)
    (hidentity : ∀ (i : Fin n) (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ)),
      (∫ x, x i * φ x ∂ν) - (∫ x, partialTest n i φ x ∂ν) =
        ∫ x, tensorPartialContraction n T i φ x ∂ν)
    (Tm : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n × Fin n × Fin n))
    (hTm : MemLp Tm 2 (μ.map (normalizedSum n m U)))
    (hrep : ∀ ω, Tm (normalizedSum n m U ω) = (m : ℝ) ^ (-(3 : ℝ) / 2) •
      condExp ((inferInstance : MeasurableSpace (EuclideanSpace ℝ (Fin n))).comap (normalizedSum n m U)) μ
        (fun ω => ∑ ℓ, T (U ℓ ω)) ω) :
    (∀ (i : Fin n) (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ)),
      (∫ x, x i * φ x ∂μ.map (normalizedSum n m U)) -
        (∫ x, partialTest n i φ x ∂μ.map (normalizedSum n m U)) =
          ∫ x, tensorPartialContraction n Tm i φ x ∂μ.map (normalizedSum n m U)) ∧
    (∀ F : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), EuclideanSpace ℝ (Fin n)),
      Integrable (fun x => ⟪x, F x⟫ - vectorDivergence n F x) (μ.map (normalizedSum n m U)) ∧
      Integrable (vectorHessianContraction n Tm F) (μ.map (normalizedSum n m U)) ∧
      (∫ x, ⟪x, F x⟫ - vectorDivergence n F x ∂μ.map (normalizedSum n m U)) =
        ∫ x, vectorHessianContraction n Tm F x ∂μ.map (normalizedSum n m U)) := by
  let W := normalizedSum n m U
  have hW : Measurable W := normalizedSum_measurable n m U hUmeas
  have hWlaw : HasLaw W (μ.map W) μ := hasLaw_map hW.aemeasurable
  let : IsProbabilityMeasure (μ.map W) := hWlaw.isProbabilityMeasure_iff.mp inferInstance
  have hWxi (i : Fin n) : MemLp (fun x : EuclideanSpace ℝ (Fin n) => x i) 2 (μ.map W) :=
    normalized_sum_coordinate_memLp μ n m ν U hU hUmeas i (hxi i)
  have hsum : MemLp (fun ω => ∑ ℓ, T (U ℓ ω)) 2 μ :=
    memLp_finsetSum Finset.univ (fun ℓ _hℓ => (hU ℓ).memLp_fun_comp hT)
  have hcomp (i : Fin n) (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ)) :
      (∫ x, x i * φ x ∂μ.map W) - (∫ x, partialTest n i φ x ∂μ.map W) =
        ∫ x, tensorPartialContraction n Tm i φ x ∂μ.map W := by
    have hraw := normalized_sum_raw_stein_identity μ n m hm ν U hU hind T hT i (hxi i) (hidentity i) φ
    have hcond := conditional_tensor_contraction_pairing μ n W hW (fun ω => ∑ ℓ, T (U ℓ ω)) hsum
      Tm ((m : ℝ) ^ (-(3 : ℝ) / 2)) hrep i φ
    have hsum_int :
        (∫ ω, ∑ j : Fin n, ∑ k : Fin n,
          (∑ ℓ, T (U ℓ ω)) (i, j, k) * partialTest n k (partialTest n j φ) (W ω) ∂μ) =
          ∫ ω, ∑ ℓ, ∑ j : Fin n, ∑ k : Fin n,
            T (U ℓ ω) (i, j, k) * partialTest n k (partialTest n j φ) (W ω) ∂μ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun ω => sum_tensor_partial_contraction n m (fun ℓ => T (U ℓ ω)) i φ (W ω)
    have hfirst : Integrable (fun x => x i * φ x) (μ.map W) :=
      (hWxi i).integrable_mul (testFunction_memLp_two n (μ.map W) φ)
    have hderiv : Integrable (partialTest n i φ) (μ.map W) :=
      (testFunction_memLp_two n (μ.map W) (partialTest n i φ)).integrable (by norm_num)
    have hright : Integrable (tensorPartialContraction n Tm i φ) (μ.map W) :=
      tensorPartialContraction_integrable n (μ.map W) Tm hTm i φ
    have hfirstMap : (∫ ω, W ω i * φ (W ω) ∂μ) = ∫ x, x i * φ x ∂μ.map W := by
      simpa only [Function.comp_def] using hWlaw.integral_comp hfirst.aestronglyMeasurable
    have hderivMap : (∫ ω, partialTest n i φ (W ω) ∂μ) = ∫ x, partialTest n i φ x ∂μ.map W := by
      simpa only [Function.comp_def] using hWlaw.integral_comp hderiv.aestronglyMeasurable
    have hrightMap : (∫ ω, tensorPartialContraction n Tm i φ (W ω) ∂μ) =
        ∫ x, tensorPartialContraction n Tm i φ x ∂μ.map W := by
      simpa only [Function.comp_def] using hWlaw.integral_comp hright.aestronglyMeasurable
    calc
      _ = (∫ ω, W ω i * φ (W ω) ∂μ) - (∫ ω, partialTest n i φ (W ω) ∂μ) := by
        rw [hfirstMap, hderivMap]
      _ = (m : ℝ) ^ (-(3 : ℝ) / 2) * (∫ ω, ∑ ℓ, ∑ j : Fin n, ∑ k : Fin n,
          T (U ℓ ω) (i, j, k) * partialTest n k (partialTest n j φ) (W ω) ∂μ) := hraw.2.2.2
      _ = ∫ ω, tensorPartialContraction n Tm i φ (W ω) ∂μ := by
        rw [← hsum_int]
        exact hcond.2.2.symm
      _ = _ := hrightMap
  exact ⟨hcomp, fun F => component_identity_implies_vector_identity n (μ.map W) hWxi Tm hTm hcomp F⟩

end AffineFKProof
