module

public import AffineFK.SteinSumVariance
public import Mathlib.Probability.HasLaw
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Transport of Stein-tensor moments to independent copies

The common law is an equality of actual pushforward measures. Square
integrability, centring, independence and second moments of T(U_i) are derived
from this law and the hypotheses on T. The conditioning variable is the actual
normalised sum of the U_i. Construction of T and its differential identity
remain separate mathematical assertions.

The proof reuses Mathlib's HasLaw change-of-variables results (Etienne Marion)
and almost-everywhere measurable composition of independent random variables
(Rémy Degenne and the Mathlib probability contributors), under Apache-2.0.
-/

public section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

/-- The Euclidean norm on three-index coefficients is the
Hilbert--Schmidt tensor norm used in the manuscript. -/
theorem third_order_tensor_norm_sq (n : ℕ)
    (A : EuclideanSpace ℝ (Fin n × Fin n × Fin n)) :
    ‖A‖ ^ 2 = ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n, (A (i, j, k)) ^ 2 := by
  simp only [EuclideanSpace.real_norm_sq_eq, Fintype.sum_prod_type]

/-- The conditional-sum coefficient agrees with m^(-3/2), for positive m. -/
theorem neg_three_halves_eq_inv_sqrt (m : ℕ) (hm : 0 < m) :
    (m : ℝ) ^ (-(3 : ℝ) / 2) = (m : ℝ)⁻¹ * (Real.sqrt (m : ℝ))⁻¹ := by
  have hmR : 0 < (m : ℝ) := Nat.cast_pos.mpr hm
  rw [show -(3 : ℝ) / 2 = -(1 + (1 / 2 : ℝ)) by norm_num,
    Real.rpow_neg, Real.rpow_add hmR, Real.rpow_one, ← Real.sqrt_eq_rpow]
  simp only [mul_inv_rev, mul_comm]
  exact hmR.le

/-- An even measurable density with respect to a reflection-invariant measure
defines a reflection-invariant measure. -/
theorem even_density_neg_invariant
    {X : Type*} [AddGroup X] [MeasurableSpace X] [MeasurableNeg X]
    (μ : Measure X) [Measure.IsNegInvariant μ]
    (ρ : X → ℝ≥0∞) (hρ : Measurable ρ) (heven : ∀ x, ρ (-x) = ρ x) :
    Measure.IsNegInvariant (μ.withDensity ρ) := by
  constructor
  change (μ.withDensity ρ).map Neg.neg = μ.withDensity ρ
  ext s hs
  rw [Measure.map_apply measurable_neg hs,
    withDensity_apply _ (measurable_neg hs), withDensity_apply _ hs]
  have hmap := setLIntegral_map (μ := μ) hs hρ measurable_neg
  rw [Measure.map_neg_eq_self] at hmap
  calc
    _ = ∫⁻ x in Neg.neg ⁻¹' s, ρ (-x) ∂μ := by simp_rw [heven]
    _ = _ := hmap.symm

/-- An L2 tensor that is almost-everywhere odd under an even probability law
is integrable and has zero mean. -/
theorem odd_tensor_integral_zero
    {X H : Type*} [AddGroup X] [MeasurableSpace X] [MeasurableNeg X]
    [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
    (ν : Measure X) [IsProbabilityMeasure ν] [Measure.IsNegInvariant ν]
    (T : X → H) (hT : MemLp T 2 ν) (hodd : ∀ᵐ x ∂ν, T (-x) = -T x) :
    Integrable T ν ∧ (∫ x, T x ∂ν) = 0 := by
  refine ⟨hT.integrable (by norm_num), ?_⟩
  have h : (∫ x, T x ∂ν) = -(∫ x, T x ∂ν) := by
    calc
      _ = ∫ x, T (-x) ∂ν := (integral_neg_eq_self T ν).symm
      _ = ∫ x, -T x ∂ν := integral_congr_ae hodd
      _ = _ := integral_neg T
  have ht : (2 : ℝ) • (∫ x, T x ∂ν) = 0 := by
    calc
      _ = (∫ x, T x ∂ν) + (∫ x, T x ∂ν) := two_smul ℝ _
      _ = (∫ x, T x ∂ν) + -(∫ x, T x ∂ν) := congrArg (fun v => (∫ x, T x ∂ν) + v) h
      _ = 0 := add_neg_cancel _
  exact (smul_eq_zero.mp ht).resolve_left (by norm_num)

/-- A common law transports the actual tensor, its L2 membership, mean and
second moment, without assuming these facts separately for each copy. -/
theorem hasLaw_tensor_moments
    {Ω X H : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ν : Measure X) (U : Ω → X) (hU : HasLaw U ν μ)
    (T : X → H) (hT : MemLp T 2 ν) :
    MemLp (fun ω => T (U ω)) 2 μ ∧
      (∫ ω, T (U ω) ∂μ) = ∫ x, T x ∂ν ∧
      (∫ ω, ‖T (U ω)‖ ^ 2 ∂μ) = ∫ x, ‖T x‖ ^ 2 ∂ν := by
  refine ⟨hU.memLp_fun_comp hT, ?_, ?_⟩
  · exact hU.integral_comp hT.aestronglyMeasurable
  · exact hU.integral_comp (hT.aestronglyMeasurable.norm.pow 2)

/-- Pairwise independence is preserved by an L2 tensor evaluated at copies
with a common law; no global measurable representative of T is assumed. -/
theorem pairwise_independent_tensor_copies
    {Ω X H : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    [NormedAddCommGroup H] [NormedSpace ℝ H] [MeasurableSpace H] [BorelSpace H]
    (μ : Measure Ω) (ν : Measure X) (m : ℕ) (U : Fin m → Ω → X)
    (hU : ∀ i, HasLaw (U i) ν μ)
    (hind : Pairwise (fun i j => IndepFun (U i) (U j) μ))
    (T : X → H) (hT : MemLp T 2 ν) :
    Pairwise (fun i j => IndepFun (fun ω => T (U i ω)) (fun ω => T (U j ω)) μ) := by
  intro i j hij
  apply (hind hij).comp₀ (hU i).aemeasurable (hU j).aemeasurable
  · rw [(hU i).map_eq]
    exact hT.aestronglyMeasurable.aemeasurable
  · rw [(hU j).map_eq]
    exact hT.aestronglyMeasurable.aemeasurable

/-- The exact second moment of the sum of centred tensors evaluated at
independent copies equals m times the original tensor's second moment. -/
theorem independent_tensor_copies_second_moment
    {Ω X H : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [MeasurableSpace H] [BorelSpace H]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ν : Measure X)
    (m : ℕ) (U : Fin m → Ω → X) (hU : ∀ i, HasLaw (U i) ν μ)
    (hind : Pairwise (fun i j => IndepFun (U i) (U j) μ))
    (T : X → H) (hT : MemLp T 2 ν) (hmean : ∫ x, T x ∂ν = 0) :
    (∫ ω, ‖∑ i, T (U i ω)‖ ^ 2 ∂μ) =
      (m : ℝ) * (∫ x, ‖T x‖ ^ 2 ∂ν) := by
  have hcopies := fun i => hasLaw_tensor_moments μ ν (U i) (hU i) T hT
  rw [independent_centered_sum_second_moment μ m (fun i ω => T (U i ω))
    (fun i => (hcopies i).1)
    (pairwise_independent_tensor_copies μ ν m U hU hind T hT)
    (fun i => (hcopies i).2.1.trans hmean)]
  simp only [(hcopies _).2.2, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]

/-- For actual independent copies U_i, the conditional tensor is a measurable
L2 function of W_m = m^(-1/2) sum U_i and has the exact M/m^2 bound. -/
theorem normalized_tensor_copies_law_second_moment
    {Ω E H : Type*} [mΩ : MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [SecondCountableTopology E]
    [mE : MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [MeasurableSpace H] [BorelSpace H]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ν : Measure E)
    (m : ℕ) (hm : 0 < m) (U : Fin m → Ω → E)
    (hU : ∀ i, HasLaw (U i) ν μ) (hUmeas : ∀ i, Measurable (U i))
    (hind : Pairwise (fun i j => IndepFun (U i) (U j) μ))
    (T : E → H) (hT : MemLp T 2 ν) (hmean : ∫ x, T x ∂ν = 0)
    (M : ℝ) (hbound : (∫ x, ‖T x‖ ^ 2 ∂ν) ≤ M) :
    ∃ Tm : E → H, StronglyMeasurable Tm ∧
      MemLp Tm 2 (μ.map (fun ω => (Real.sqrt (m : ℝ))⁻¹ • ∑ i, U i ω)) ∧
      (∀ ω, Tm ((Real.sqrt (m : ℝ))⁻¹ • ∑ i, U i ω) =
        ((m : ℝ)⁻¹ * (Real.sqrt (m : ℝ))⁻¹) •
          (condExp (mE.comap (fun ω => (Real.sqrt (m : ℝ))⁻¹ • ∑ i, U i ω)) μ
            (fun ω => ∑ i, T (U i ω))) ω) ∧
      (∫ z, ‖Tm z‖ ^ 2 ∂μ.map (fun ω => (Real.sqrt (m : ℝ))⁻¹ • ∑ i, U i ω)) ≤
        M / (m : ℝ) ^ 2 := by
  have hcopies := fun i => hasLaw_tensor_moments μ ν (U i) (hU i) T hT
  have hW : Measurable (fun ω => (Real.sqrt (m : ℝ))⁻¹ • ∑ i, U i ω) :=
    (Finset.measurable_fun_sum Finset.univ (fun i _hi => hUmeas i)).const_smul _
  exact normalized_conditional_sum_law_second_moment μ m hm (fun i ω => T (U i ω))
    (fun i => (hcopies i).1)
    (pairwise_independent_tensor_copies μ ν m U hU hind T hT)
    (fun i => (hcopies i).2.1.trans hmean) M
    (fun i => (hcopies i).2.2.trans_le hbound) _ hW

/-- The size and representation clauses of the normalised-sum lemma, with
actual third-order coefficients, the exact P(P-1)n constant, and m^(-3/2).
The original tensor's existence and differential identity are not premises
silently supplied by this second-moment argument. -/
theorem normalized_third_order_tensor_copies
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (n : ℕ) (ν : Measure (EuclideanSpace ℝ (Fin n))) [Measure.IsNegInvariant ν]
    (m : ℕ) (hm : 0 < m) (U : Fin m → Ω → EuclideanSpace ℝ (Fin n))
    (hU : ∀ i, HasLaw (U i) ν μ) (hUmeas : ∀ i, Measurable (U i))
    (hind : iIndepFun U μ)
    (T : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n × Fin n × Fin n))
    (hT : MemLp T 2 ν) (hodd : ∀ᵐ x ∂ν, T (-x) = -T x)
    (P : ℝ) (hbound :
      (∫ x, ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n, (T x (i, j, k)) ^ 2 ∂ν) ≤
        P * (P - 1) * (n : ℝ)) :
    ∃ Tm : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n × Fin n × Fin n),
      StronglyMeasurable Tm ∧
      MemLp Tm 2 (μ.map (fun ω => (Real.sqrt (m : ℝ))⁻¹ • ∑ i, U i ω)) ∧
      (∀ ω, Tm ((Real.sqrt (m : ℝ))⁻¹ • ∑ i, U i ω) =
        (m : ℝ) ^ (-(3 : ℝ) / 2) •
          (condExp (MeasurableSpace.comap (fun ω => (Real.sqrt (m : ℝ))⁻¹ • ∑ i, U i ω)
            inferInstance) μ (fun ω => ∑ i, T (U i ω))) ω) ∧
      (∫ z, ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n, (Tm z (i, j, k)) ^ 2
        ∂μ.map (fun ω => (Real.sqrt (m : ℝ))⁻¹ • ∑ i, U i ω)) ≤
        P * (P - 1) * (n : ℝ) / (m : ℝ) ^ 2 := by
  letI : IsProbabilityMeasure ν := (hU ⟨0, hm⟩).isProbabilityMeasure_iff.mp inferInstance
  have hnormbound : (∫ x, ‖T x‖ ^ 2 ∂ν) ≤ P * (P - 1) * (n : ℝ) := by
    simpa only [third_order_tensor_norm_sq] using hbound
  obtain ⟨Tm, hmeas, hLp, hrep, hsize⟩ :=
    normalized_tensor_copies_law_second_moment μ ν m hm U hU hUmeas
      (fun _i _j hij => hind.indepFun hij) T hT
      (odd_tensor_integral_zero ν T hT hodd).2 (P * (P - 1) * (n : ℝ)) hnormbound
  refine ⟨Tm, hmeas, hLp, ?_, ?_⟩
  · intro ω
    rw [neg_three_halves_eq_inv_sqrt m hm]
    exact hrep ω
  · simpa only [third_order_tensor_norm_sq] using hsize

end AffineFKProof
