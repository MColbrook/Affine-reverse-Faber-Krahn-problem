module

public import Mathlib.Probability.Independence.Integration
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.FactorsThrough
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# Second moments in the normalised-sum Stein construction

The cross terms are evaluated from actual independence and zero means.
Conditional expectation is Mathlib's Bochner conditional expectation.
The existence and differential identity of the original Stein tensor are
separate obligations.

The proof reuses independent bilinear-integral factorisation (Martin Zinkevich,
Vincent Beffara and Etienne Marion), the L2 inner-product integral (Rémy
Degenne), conditional Jensen (Rémy Degenne and Kexing Ying), and Doob--Dynkin
factorisation (Etienne Marion), from Mathlib's Apache-2.0 library.
-/

public section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory
open scoped BigOperators RealInnerProductSpace ENNReal

/-- Independent centred square-integrable Hilbert-valued random variables have
zero expected inner product. -/
theorem independent_centered_integral_inner
    {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X Y : Ω → E) (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ)
    (hind : IndepFun X Y μ) (hmeanX : ∫ ω, X ω ∂μ = 0)
    (hmeanY : ∫ ω, Y ω ∂μ = 0) :
    (∫ ω, ⟪X ω, Y ω⟫ ∂μ) = 0 := by
  have h := hind.integral_bilin
    (MemLp.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2) hX)
    (MemLp.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2) hY) (innerSL ℝ)
  change (∫ ω, ⟪X ω, Y ω⟫ ∂μ) = ⟪∫ ω, X ω ∂μ, ∫ ω, Y ω ∂μ⟫ at h
  simpa only [hmeanX, hmeanY, inner_zero_left] using h

/-- Every off-diagonal cross term vanishes for a finite pairwise independent
centred family, with all integrability obligations discharged from L2. -/
theorem independent_centered_sum_second_moment
    {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (m : ℕ) (T : Fin m → Ω → E) (hLp : ∀ i, MemLp (T i) 2 μ)
    (hind : Pairwise (fun i j => IndepFun (T i) (T j) μ))
    (hmean : ∀ i, ∫ ω, T i ω ∂μ = 0) :
    (∫ ω, ‖∑ i, T i ω‖ ^ 2 ∂μ) =
      ∑ i, ∫ ω, ‖T i ω‖ ^ 2 ∂μ := by
  have hinner (i j : Fin m) :
      Integrable (fun ω => ⟪T i ω, T j ω⟫) μ := by
    apply (L2.integrable_inner (𝕜 := ℝ)
      ((hLp i).toLp (T i)) ((hLp j).toLp (T j))).congr
    filter_upwards [(hLp i).coeFn_toLp, (hLp j).coeFn_toLp] with ω hi hj
    rw [hi, hj]
  have hexpand (ω : Ω) :
      ‖∑ i, T i ω‖ ^ 2 = ∑ i, ∑ j, ⟪T i ω, T j ω⟫ := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [sum_inner, inner_sum]
    exact Finset.sum_comm
  simp_rw [hexpand]
  rw [integral_finsetSum _ (fun i _hi =>
    integrable_finsetSum _ (fun j _hj => hinner i j))]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [integral_finsetSum _ (fun j _hj => hinner i j)]
  rw [Finset.sum_eq_single i]
  · simp only [real_inner_self_eq_norm_sq]
  · intro j _hj hji
    exact independent_centered_integral_inner μ (T i) (T j) (hLp i) (hLp j)
      (hind hji.symm) (hmean i) (hmean j)
  · simp

/-- Conditional expectation contracts the actual second-moment integral. -/
theorem conditional_second_moment_le
    {Ω E : Type*} [mΩ : MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (m : MeasurableSpace Ω) (_hm : m ≤ mΩ)
    (f : Ω → E) (hf : MemLp f 2 μ) :
    (∫ ω, ‖(condExp m μ f) ω‖ ^ 2 ∂μ) ≤ ∫ ω, ‖f ω‖ ^ 2 ∂μ := by
  let : MeasurableSpace Ω := mΩ
  have hi := (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mp hf
  simpa only [Real.rpow_two] using
    (integral_norm_condExp_rpow_le (m := m) (p := (2 : ℝ))
      (by norm_num) (by simpa only [Real.rpow_two] using hi))

/-- Conditional Jensen and independence give the squared-norm bound for a
scaled conditional sum, with the expectation and integrals interpreted in L2. -/
theorem conditioned_independent_sum_second_moment_le
    {Ω E : Type*} [mΩ : MeasurableSpace Ω]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (s : MeasurableSpace Ω) (hs : s ≤ mΩ)
    (m : ℕ) (T : Fin m → Ω → E) (hLp : ∀ i, MemLp (T i) 2 μ)
    (hind : Pairwise (fun i j => IndepFun (T i) (T j) μ))
    (hmean : ∀ i, ∫ ω, T i ω ∂μ = 0) (c : ℝ) :
    (∫ ω, ‖c • (condExp s μ (fun x => ∑ i, T i x)) ω‖ ^ 2 ∂μ) ≤
      c ^ 2 * (∑ i, ∫ ω, ‖T i ω‖ ^ 2 ∂μ) := by
  let : MeasurableSpace Ω := mΩ
  have hsum : MemLp (fun ω => ∑ i, T i ω) 2 μ := by
    simpa using memLp_finsetSum Finset.univ (fun i _hi => hLp i)
  have hcontract := conditional_second_moment_le μ s hs _ hsum
  rw [independent_centered_sum_second_moment μ m T hLp hind hmean] at hcontract
  simp_rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  rw [integral_const_mul]
  exact mul_le_mul_of_nonneg_left hcontract (sq_nonneg c)

/-- The m-to-the-minus-two decay in the manuscript's conditional Stein-tensor
sum. Pairwise independence and centring are hypotheses on the actual random
tensors; their second moments are bounded individually by M. -/
theorem normalized_conditional_sum_second_moment_le
    {Ω E : Type*} [mΩ : MeasurableSpace Ω]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (s : MeasurableSpace Ω) (hs : s ≤ mΩ)
    (m : ℕ) (hm : 0 < m) (T : Fin m → Ω → E)
    (hLp : ∀ i, MemLp (T i) 2 μ)
    (hind : Pairwise (fun i j => IndepFun (T i) (T j) μ))
    (hmean : ∀ i, ∫ ω, T i ω ∂μ = 0)
    (M : ℝ) (hbound : ∀ i, (∫ ω, ‖T i ω‖ ^ 2 ∂μ) ≤ M) :
    (∫ ω,
      ‖((m : ℝ)⁻¹ * (Real.sqrt (m : ℝ))⁻¹) •
        (condExp s μ (fun x => ∑ i, T i x)) ω‖ ^ 2 ∂μ) ≤
      M / (m : ℝ) ^ 2 := by
  let : MeasurableSpace Ω := mΩ
  let c := (m : ℝ)⁻¹ * (Real.sqrt (m : ℝ))⁻¹
  have hmR : 0 < (m : ℝ) := Nat.cast_pos.mpr hm
  have hc : c ^ 2 * (m : ℝ) = 1 / (m : ℝ) ^ 2 := by
    dsimp [c]
    rw [mul_pow, inv_pow, inv_pow, Real.sq_sqrt hmR.le]
    field_simp
  calc
    _ ≤ c ^ 2 * (∑ i, ∫ ω, ‖T i ω‖ ^ 2 ∂μ) :=
      conditioned_independent_sum_second_moment_le μ s hs m T hLp hind hmean c
    _ ≤ c ^ 2 * ((m : ℝ) * M) := by
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg c)
      calc
        _ ≤ ∑ _i : Fin m, M := Finset.sum_le_sum (fun i _hi => hbound i)
        _ = _ := by simp
    _ = _ := by
      rw [← mul_assoc, hc]
      ring

/-- A square-integrable conditional expectation given W has an actual strongly
measurable, square-integrable representative as a function of W. -/
theorem conditional_expectation_factor
    {Ω X E : Type*} [mΩ : MeasurableSpace Ω] [mX : MeasurableSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f : Ω → E) (hf : MemLp f 2 μ) (W : Ω → X) (hW : Measurable W) :
    ∃ g : X → E, StronglyMeasurable g ∧ MemLp g 2 (μ.map W) ∧
      ∀ ω, g (W ω) = (condExp (mX.comap W) μ f) ω := by
  obtain ⟨g, hg, heq⟩ :=
    (stronglyMeasurable_condExp (m := mX.comap W) (μ := μ) (f := f)).exists_eq_measurable_comp
  refine ⟨g, hg, ?_, ?_⟩
  · apply (memLp_map_measure_iff hg.aestronglyMeasurable hW.aemeasurable).mpr
    rw [← heq]
    exact MemLp.condExp (by norm_num) hf
  · intro ω
    exact (congrFun heq ω).symm

/-- The conditional tensor in the normalised-sum construction exists as an L2
function on the law of W and has the manuscript's exact m-to-the-minus-two
second-moment bound. This proves the size and representation assertions;
the second-order differential Stein identity is a separate assertion. -/
theorem normalized_conditional_sum_law_second_moment
    {Ω X E : Type*} [mΩ : MeasurableSpace Ω] [mX : MeasurableSpace X]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (m : ℕ) (hm : 0 < m) (T : Fin m → Ω → E)
    (hLp : ∀ i, MemLp (T i) 2 μ)
    (hind : Pairwise (fun i j => IndepFun (T i) (T j) μ))
    (hmean : ∀ i, ∫ ω, T i ω ∂μ = 0)
    (M : ℝ) (hbound : ∀ i, (∫ ω, ‖T i ω‖ ^ 2 ∂μ) ≤ M)
    (W : Ω → X) (hW : Measurable W) :
    ∃ Tm : X → E, StronglyMeasurable Tm ∧ MemLp Tm 2 (μ.map W) ∧
      (∀ ω, Tm (W ω) =
        ((m : ℝ)⁻¹ * (Real.sqrt (m : ℝ))⁻¹) •
          (condExp (mX.comap W) μ (fun x => ∑ i, T i x)) ω) ∧
      (∫ z, ‖Tm z‖ ^ 2 ∂μ.map W) ≤ M / (m : ℝ) ^ 2 := by
  have hsum : MemLp (fun ω => ∑ i, T i ω) 2 μ := by
    simpa using memLp_finsetSum Finset.univ (fun i _hi => hLp i)
  obtain ⟨g, hg, hgLp, hgcomp⟩ :=
    conditional_expectation_factor μ (fun x => ∑ i, T i x) hsum W hW
  let c := (m : ℝ)⁻¹ * (Real.sqrt (m : ℝ))⁻¹
  let Tm : X → E := fun z => c • g z
  have hTm : StronglyMeasurable Tm := hg.const_smul c
  have hTmLp : MemLp Tm 2 (μ.map W) := hgLp.const_smul c
  refine ⟨Tm, hTm, hTmLp, ?_, ?_⟩
  · intro ω
    exact congrArg (fun z : E => c • z) (hgcomp ω)
  · have hnorm : AEStronglyMeasurable (fun z => ‖Tm z‖ ^ 2) (μ.map W) := by
      have heq : (fun z => ‖Tm z‖ ^ 2) =
          ((fun z => ‖Tm z‖) * (fun z => ‖Tm z‖)) := by
        funext z
        simp only [pow_two, Pi.mul_apply]
      rw [heq]
      exact (hTm.norm.mul hTm.norm).aestronglyMeasurable
    calc
      _ = ∫ ω, ‖Tm (W ω)‖ ^ 2 ∂μ := integral_map hW.aemeasurable hnorm
      _ = ∫ ω, ‖c • (condExp (mX.comap W) μ (fun x => ∑ i, T i x)) ω‖ ^ 2 ∂μ := by
        apply integral_congr_ae
        filter_upwards [] with ω
        simp only [Tm, hgcomp ω]
      _ ≤ _ := normalized_conditional_sum_second_moment_le μ (mX.comap W)
        hW.comap_le m hm T hLp hind hmean M hbound

end AffineFKProof
