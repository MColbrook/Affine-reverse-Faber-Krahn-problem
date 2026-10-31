module

public import AffineFK.GaussianPoincareOU
public import AffineFK.PoincareConvolutionNormalized
public import Mathlib.Basic.ENNReal.Operations
public import Mathlib.Basic.ENNReal.Inv

/-!
# The least Poincare constant and its inheritance inequalities

The constant is the actual extended nonnegative infimum of all admissible
constants for compact smooth scalar tests. The proved smooth L2 extension
shows these tests have the same admissible constants as smooth functions
whose values and gradients belong to L2. An empty admissible set gives
infinity. Inheritance below concerns this least constant, rather than an
arbitrary number assumed to satisfy the desired conclusion.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory TopologicalSpace
open scoped Distributions ENNReal NNReal RealInnerProductSpace ContDiff

/-- The canonical completeness proof for finite-dimensional Euclidean space.
Naming this genuine Mathlib instance proof keeps elaboration independent of
the compiler's context-dependent sharing of generated auxiliary proofs. -/
theorem poincare_euclidean_completeSpace (n : ℕ) :
    CompleteSpace (EuclideanSpace ℝ (Fin n)) :=
  PiLp.completeSpace (p := (2 : ℝ≥0∞)) (β := fun _ : Fin n => ℝ)

/-- A genuine variance-gradient inequality for every compact smooth test. -/
def AdmissiblePoincareConstant (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) (P : ℝ≥0) : Prop :=
  ∀ f : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ),
    (∫ x, (f x - ∫ y, f y ∂ν) ^ 2 ∂ν) ≤
      (P : ℝ) * (∫ x, ‖@gradient ℝ (EuclideanSpace ℝ (Fin n)) _ _ _
        (poincare_euclidean_completeSpace n) f x‖ ^ 2 ∂ν)

/-- The least admissible nonnegative Poincare constant; infinity if none exists. -/
def poincareConstant (n : ℕ) (ν : Measure (EuclideanSpace ℝ (Fin n))) : ℝ≥0∞ :=
  ⨅ (P : ℝ≥0) (_ : AdmissiblePoincareConstant n ν P), (P : ℝ≥0∞)

theorem poincareConstant_le_of_admissible (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) (P : ℝ≥0)
    (hP : AdmissiblePoincareConstant n ν P) :
    poincareConstant n ν ≤ (P : ℝ≥0∞) :=
  iInf₂_le P hP

theorem admissiblePoincareConstant_smooth_L2 (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (P : ℝ≥0) (hP : AdmissiblePoincareConstant n ν P)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ContDiff ℝ ∞ f)
    (hfL2 : MemLp f 2 ν) (hgL2 : MemLp (gradient f) 2 ν) :
    (∫ x, (f x - ∫ y, f y ∂ν) ^ 2 ∂ν) ≤
      (P : ℝ) * (∫ x, ‖gradient f x‖ ^ 2 ∂ν) :=
  poincareSmoothExtension n ν P hP f hf hfL2 hgL2

theorem poincareConstant_convolution (n : ℕ)
    (ν η : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν] [IsProbabilityMeasure η] :
    poincareConstant n ((ν.prod η).map (fun p => p.1 + p.2)) ≤
      poincareConstant n ν + poincareConstant n η := by
  change _ ≤ (⨅ (P : ℝ≥0) (_ : AdmissiblePoincareConstant n ν P), (P : ℝ≥0∞)) +
    (⨅ (Q : ℝ≥0) (_ : AdmissiblePoincareConstant n η Q), (Q : ℝ≥0∞))
  simp_rw [ENNReal.iInf_add, ENNReal.add_iInf]
  refine le_iInf fun P => le_iInf fun hP => le_iInf fun Q => le_iInf fun hQ => ?_
  exact (poincareConstant_le_of_admissible n _ (P + Q)
    (poincareConvolution n ν η P Q P.coe_nonneg Q.coe_nonneg hP hQ)).trans_eq (by simp)

theorem poincareConstant_stdGaussian_le_one (n : ℕ) :
    poincareConstant n (stdGaussian (EuclideanSpace ℝ (Fin n))) ≤ 1 := by
  simpa using poincareConstant_le_of_admissible n (stdGaussian (EuclideanSpace ℝ (Fin n)))
    1 (fun f => by simpa using stdGaussian_poincare n f)

theorem poincareConstant_normalized_copies
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (n m : ℕ) (hm : 0 < m)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (U : Fin m → Ω → EuclideanSpace ℝ (Fin n))
    (hU : ∀ i, HasLaw (U i) ν μ) (hind : iIndepFun U μ) :
    poincareConstant n (μ.map (normalizedSum n m U)) ≤ poincareConstant n ν := by
  refine le_iInf fun P => le_iInf fun hP => ?_
  exact poincareConstant_le_of_admissible n _ P
    (poincareConvolution_normalized_copies μ n m hm ν U hU hind P P.coe_nonneg hP)

end AffineFKProof
