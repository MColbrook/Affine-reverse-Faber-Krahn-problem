module

public import Mathlib.Analysis.Distribution.TestFunction
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator
public import Mathlib.Tactic.NormNum

/-!
# The weighted Sobolev graph

The completion of compactly supported smooth functions in the weighted H1
norm is realised as the closure of their value-gradient pairs in the Hilbert
product of two genuine L2 spaces. The value and gradient maps are continuous
linear maps. The Poincare inequality extends to this completion and its closed
mean-zero subspace. Weak-derivative identification, injectivity of the value map
and cutoff approximation are additional assertions.

This construction reuses Mathlib's test functions and derivative maps (Luigi
Massacci and Anatole Dedecker), Hilbert products (Moritz Doll), Lp embeddings
of bounded continuous functions, and Riesz duality.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory TopologicalSpace InnerProductSpace
open scoped Distributions ENNReal RealInnerProductSpace

/-- The ambient Hilbert product for the weighted H1 graph norm. -/
abbrev SobolevAmbient {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E]
    (ν : Measure E) := WithLp 2 (Lp ℝ 2 ν × Lp E 2 ν)

/-- A test function as an element of the actual weighted L2 space. -/
def testFunctionToL2
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (ν : Measure E) [IsFiniteMeasure ν] :
    𝓓((⊤ : Opens E), F) →L[ℝ] Lp F 2 ν :=
  (BoundedContinuousFunction.toLp 2 ν ℝ).comp
    (TestFunction.toBoundedContinuousFunctionCLM ℝ)

/-- The gradient of a scalar test function, as a vector-valued test function. -/
def testFunctionGradient
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] :
    𝓓((⊤ : Opens E), ℝ) →L[ℝ] 𝓓((⊤ : Opens E), E) :=
  (TestFunction.postcompCLM (toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap).comp
    (TestFunction.fderivCLM ℝ ⊤ ⊤)

theorem testFunctionGradient_apply
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (f : 𝓓((⊤ : Opens E), ℝ)) (x : E) :
    testFunctionGradient f x = gradient f x := by
  change (toDual ℝ E).symm ((TestFunction.fderivCLM ℝ ⊤ ⊤ f) x) = gradient f x
  rw [TestFunction.fderivCLM_apply_of_le f (by simp)]
  rfl

theorem testFunctionToL2_coe
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (ν : Measure E) [IsFiniteMeasure ν] (f : 𝓓((⊤ : Opens E), F)) :
    testFunctionToL2 ν f =ᵐ[ν] f := by
  exact BoundedContinuousFunction.coeFn_toLp 2 ν ℝ
    (TestFunction.toBoundedContinuousFunctionCLM ℝ f)

/-- The actual value-gradient pair of a compactly supported smooth function. -/
def smoothGradientPair
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (ν : Measure E) [IsFiniteMeasure ν] :
    𝓓((⊤ : Opens E), ℝ) →L[ℝ] SobolevAmbient ν :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ (Lp ℝ 2 ν) (Lp E 2 ν)).symm.toContinuousLinearMap.comp
    ((testFunctionToL2 ν).prod ((testFunctionToL2 ν).comp testFunctionGradient))

/-- The H1 completion, represented by its value and gradient coordinates. -/
def weightedSobolevGraph
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (ν : Measure E) [IsFiniteMeasure ν] : Submodule ℝ (SobolevAmbient ν) :=
  (smoothGradientPair ν).range.topologicalClosure

theorem weightedSobolevGraph_isClosed
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (ν : Measure E) [IsFiniteMeasure ν] :
    IsClosed (weightedSobolevGraph ν : Set (SobolevAmbient ν)) := by
  exact Submodule.isClosed_topologicalClosure _

instance weightedSobolevGraph_completeSpace
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (ν : Measure E) [IsFiniteMeasure ν] : CompleteSpace (weightedSobolevGraph ν) :=
  (weightedSobolevGraph_isClosed ν).completeSpace_coe

/-- The value coordinate of an element of the weighted H1 completion. -/
def sobolevValue
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (ν : Measure E) [IsFiniteMeasure ν] : weightedSobolevGraph ν →L[ℝ] Lp ℝ 2 ν :=
  (WithLp.fstL 2 ℝ (Lp ℝ 2 ν) (Lp E 2 ν)).comp (weightedSobolevGraph ν).subtypeL

/-- The gradient coordinate of an element of the weighted H1 completion. -/
def sobolevGradient
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (ν : Measure E) [IsFiniteMeasure ν] : weightedSobolevGraph ν →L[ℝ] Lp E 2 ν :=
  (WithLp.sndL 2 ℝ (Lp ℝ 2 ν) (Lp E 2 ν)).comp (weightedSobolevGraph ν).subtypeL

theorem sobolev_graph_norm_sq
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (ν : Measure E) [IsFiniteMeasure ν] (v : weightedSobolevGraph ν) :
    ‖v‖ ^ 2 = ‖sobolevValue ν v‖ ^ 2 + ‖sobolevGradient ν v‖ ^ 2 := by
  change ‖(v : SobolevAmbient ν)‖ ^ 2 =
    ‖(v : SobolevAmbient ν).fst‖ ^ 2 + ‖(v : SobolevAmbient ν).snd‖ ^ 2
  exact WithLp.prod_norm_sq_eq_of_L2 _

theorem smoothGradientPair_mem
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (ν : Measure E) [IsFiniteMeasure ν] (f : 𝓓((⊤ : Opens E), ℝ)) :
    smoothGradientPair ν f ∈ weightedSobolevGraph ν := by
  apply (smoothGradientPair ν).range.le_topologicalClosure
  exact ⟨f, rfl⟩

/-- The integral functional on L2 for a finite measure, represented by the
constant-one element through the Hilbert inner product. -/
def l2Mean {X : Type*} [MeasurableSpace X]
    (ν : Measure X) [IsFiniteMeasure ν] : Lp ℝ 2 ν →L[ℝ] ℝ :=
  innerSL ℝ (Lp.const 2 ν (1 : ℝ))

theorem l2Mean_apply {X : Type*} [MeasurableSpace X]
    (ν : Measure X) [IsFiniteMeasure ν] (f : Lp ℝ 2 ν) :
    l2Mean ν f = ∫ x, f x ∂ν := by
  change ⟪Lp.const 2 ν (1 : ℝ), f⟫ = _
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_const 2 ν (1 : ℝ)] with x hx
  change f x * (Lp.const 2 ν (1 : ℝ)) x = f x
  rw [hx]
  simp only [Function.const_apply, mul_one]

theorem l2_norm_sq_integral
    {X F : Type*} [MeasurableSpace X]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (ν : Measure X) (f : Lp F 2 ν) :
    ‖f‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 ∂ν := by
  calc
    _ = ⟪f, f⟫ := (real_inner_self_eq_norm_sq f).symm
    _ = ∫ x, ⟪f x, f x⟫ ∂ν := L2.inner_def f f
    _ = _ := by simp_rw [real_inner_self_eq_norm_sq]

theorem testFunctionToL2_norm_sq
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (ν : Measure E) [IsFiniteMeasure ν] (f : 𝓓((⊤ : Opens E), F)) :
    ‖testFunctionToL2 ν f‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 ∂ν := by
  rw [l2_norm_sq_integral]
  apply integral_congr_ae
  filter_upwards [testFunctionToL2_coe ν f] with x hx
  rw [hx]

theorem testFunctionToL2_mean
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (ν : Measure E) [IsFiniteMeasure ν] (f : 𝓓((⊤ : Opens E), ℝ)) :
    l2Mean ν (testFunctionToL2 ν f) = ∫ x, f x ∂ν := by
  rw [l2Mean_apply]
  exact integral_congr_ae (testFunctionToL2_coe ν f)

/-- The graph embedding has exactly the norm used to define H1 in the paper. -/
theorem smoothGradientPair_norm_sq
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (ν : Measure E) [IsFiniteMeasure ν] (f : 𝓓((⊤ : Opens E), ℝ)) :
    ‖smoothGradientPair ν f‖ ^ 2 =
      (∫ x, (f x) ^ 2 ∂ν) + (∫ x, ‖gradient f x‖ ^ 2 ∂ν) := by
  rw [WithLp.prod_norm_sq_eq_of_L2]
  change ‖testFunctionToL2 ν f‖ ^ 2 +
    ‖testFunctionToL2 ν (testFunctionGradient f)‖ ^ 2 = _
  simp_rw [testFunctionToL2_norm_sq, testFunctionGradient_apply, Real.norm_eq_abs, sq_abs]

/-- Test-function pairs are dense in the constructed Hilbert completion. -/
theorem smoothGradientPair_denseRange
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (ν : Measure E) [IsFiniteMeasure ν] :
    DenseRange (fun f : 𝓓((⊤ : Opens E), ℝ) =>
      (⟨smoothGradientPair ν f, smoothGradientPair_mem ν f⟩ : weightedSobolevGraph ν)) := by
  rw [Metric.denseRange_iff]
  intro v ε hε
  obtain ⟨y, ⟨f, rfl⟩, hdist⟩ := Metric.mem_closure_iff.mp v.property ε hε
  exact ⟨f, hdist⟩

theorem smoothGradientPair_fst
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (ν : Measure E) [IsFiniteMeasure ν] (f : 𝓓((⊤ : Opens E), ℝ)) :
    (smoothGradientPair ν f).fst = testFunctionToL2 ν f := by
  rfl

theorem smoothGradientPair_snd
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (ν : Measure E) [IsFiniteMeasure ν] (f : 𝓓((⊤ : Opens E), ℝ)) :
    (smoothGradientPair ν f).snd = testFunctionToL2 ν (testFunctionGradient f) := by
  rfl

/-- The Poincare inequality extends from actual test-function pairs to their
H1 completion by continuity of both quadratic expressions. -/
theorem weighted_poincare_extension
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (ν : Measure E) [IsProbabilityMeasure ν] (P : ℝ)
    (hP : ∀ f : 𝓓((⊤ : Opens E), ℝ),
      ‖testFunctionToL2 ν f‖ ^ 2 - (l2Mean ν (testFunctionToL2 ν f)) ^ 2 ≤
        P * ‖testFunctionToL2 ν (testFunctionGradient f)‖ ^ 2)
    (v : weightedSobolevGraph ν) :
    ‖sobolevValue ν v‖ ^ 2 - (l2Mean ν (sobolevValue ν v)) ^ 2 ≤
      P * ‖sobolevGradient ν v‖ ^ 2 := by
  let J : SobolevAmbient ν →L[ℝ] Lp ℝ 2 ν := WithLp.fstL 2 ℝ _ _
  let D : SobolevAmbient ν →L[ℝ] Lp E 2 ν := WithLp.sndL 2 ℝ _ _
  let M : SobolevAmbient ν →L[ℝ] ℝ := (l2Mean ν).comp J
  have hclosed : IsClosed {w : SobolevAmbient ν | ‖J w‖ ^ 2 - (M w) ^ 2 ≤ P * ‖D w‖ ^ 2} :=
    isClosed_le ((J.continuous.norm.pow 2).sub (M.continuous.pow 2))
      (continuous_const.mul (D.continuous.norm.pow 2))
  have hincl : ((smoothGradientPair ν).range : Set (SobolevAmbient ν)) ⊆
      {w : SobolevAmbient ν | ‖J w‖ ^ 2 - (M w) ^ 2 ≤ P * ‖D w‖ ^ 2} := by
    rintro w ⟨f, rfl⟩
    exact hP f
  have hv : (v : SobolevAmbient ν) ∈
      closure ((smoothGradientPair ν).range : Set (SobolevAmbient ν)) := v.property
  exact (closure_minimal hincl hclosed) hv

/-- The genuine closed mean-zero subspace of the H1 completion. -/
def weightedSobolevMeanZero
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (ν : Measure E) [IsFiniteMeasure ν] : Submodule ℝ (weightedSobolevGraph ν) :=
  ((l2Mean ν).comp (sobolevValue ν)).ker

instance weightedSobolevMeanZero_completeSpace
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (ν : Measure E) [IsFiniteMeasure ν] : CompleteSpace (weightedSobolevMeanZero ν) :=
  ((l2Mean ν).comp (sobolevValue ν)).isClosed_ker.completeSpace_coe

def meanZeroValue
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (ν : Measure E) [IsFiniteMeasure ν] : weightedSobolevMeanZero ν →L[ℝ] Lp ℝ 2 ν :=
  (sobolevValue ν).comp (weightedSobolevMeanZero ν).subtypeL

def meanZeroGradient
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (ν : Measure E) [IsFiniteMeasure ν] : weightedSobolevMeanZero ν →L[ℝ] Lp E 2 ν :=
  (sobolevGradient ν).comp (weightedSobolevMeanZero ν).subtypeL

theorem meanZeroValue_mean
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (ν : Measure E) [IsFiniteMeasure ν] (v : weightedSobolevMeanZero ν) :
    l2Mean ν (meanZeroValue ν v) = 0 := by
  exact v.property

theorem meanZero_graph_norm_sq
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (ν : Measure E) [IsFiniteMeasure ν] (v : weightedSobolevMeanZero ν) :
    ‖v‖ ^ 2 = ‖meanZeroValue ν v‖ ^ 2 + ‖meanZeroGradient ν v‖ ^ 2 := by
  exact sobolev_graph_norm_sq ν v.val

theorem meanZero_poincare
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (ν : Measure E) [IsProbabilityMeasure ν] (P : ℝ)
    (hP : ∀ f : 𝓓((⊤ : Opens E), ℝ),
      ‖testFunctionToL2 ν f‖ ^ 2 - (l2Mean ν (testFunctionToL2 ν f)) ^ 2 ≤
        P * ‖testFunctionToL2 ν (testFunctionGradient f)‖ ^ 2)
    (v : weightedSobolevMeanZero ν) :
    ‖meanZeroValue ν v‖ ^ 2 ≤ P * ‖meanZeroGradient ν v‖ ^ 2 := by
  have h := weighted_poincare_extension ν P hP v.val
  change ‖meanZeroValue ν v‖ ^ 2 - (l2Mean ν (meanZeroValue ν v)) ^ 2 ≤
    P * ‖meanZeroGradient ν v‖ ^ 2 at h
  simpa only [meanZeroValue_mean, zero_pow (by norm_num : (2 : ℕ) ≠ 0), sub_zero] using h

end AffineFKProof
