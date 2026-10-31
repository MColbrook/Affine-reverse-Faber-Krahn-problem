module

public import AffineFK.BridgeBrownianRealization

/-!
# Genuine finite-dimensional Gaussianity of the Brownian realization

Each finite family is the sum of two independent Gaussian vectors:
the actual bridge evaluations and a finite linear image of the actual
standard Gaussian endpoint. Independence is the product-measure theorem.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Pointwise BigOperators Topology RealInnerProductSpace

theorem bridgeBrownianPath_gaussian_process (n : ℕ) :
    IsGaussianProcess (fun q : Icc (0 : ℝ) 1 × Fin n =>
      fun p : BridgeBrownianSample n => bridgeBrownianPath n p q.1 q.2)
      (bridgeBrownianProductMeasure n) := by
  classical
  constructor
  intro I
  let X : (∀ j : ℕ, Fin (2 ^ j) → EuclideanSpace ℝ (Fin n)) → I → ℝ :=
    fun ω q => bridgeContinuousSeries n ω q.1.1 q.1.2
  let Y : EuclideanSpace ℝ (Fin n) → I → ℝ := fun z q => (q.1.1 : ℝ) * z q.1.2
  have hX : HasGaussianLaw X (bridgeCoefficientMeasure n) :=
    (bridgeContinuousSeries_gaussian_process n).hasGaussianLaw I
  have hY : HasGaussianLaw Y (stdGaussian (EuclideanSpace ℝ (Fin n))) := by
    let L : EuclideanSpace ℝ (Fin n) →L[ℝ] (I → ℝ) :=
      ContinuousLinearMap.pi (fun q => (q.1.1 : ℝ) • coordinateFunctional n q.1.2)
    convert (IsGaussian.hasGaussianLaw_id
      (μ := stdGaussian (EuclideanSpace ℝ (Fin n)))).map L using 1
    ext z q
    simp [Y, L, coordinateFunctional_apply]
  have hXp : HasGaussianLaw (fun p : BridgeBrownianSample n => X p.1)
      (bridgeBrownianProductMeasure n) := by
    letI := hX.isGaussian_map
    exact ((show HasLaw X ((bridgeCoefficientMeasure n).map X) (bridgeCoefficientMeasure n)
      from ⟨hX.aemeasurable, rfl⟩).comp
        (measurePreserving_fst (μ := bridgeCoefficientMeasure n)
          (ν := stdGaussian (EuclideanSpace ℝ (Fin n)))).hasLaw).hasGaussianLaw
  have hYp : HasGaussianLaw (fun p : BridgeBrownianSample n => Y p.2)
      (bridgeBrownianProductMeasure n) := by
    letI := hY.isGaussian_map
    exact ((show HasLaw Y ((stdGaussian (EuclideanSpace ℝ (Fin n))).map Y)
      (stdGaussian (EuclideanSpace ℝ (Fin n))) from ⟨hY.aemeasurable, rfl⟩).comp
        (measurePreserving_snd (μ := bridgeCoefficientMeasure n)
          (ν := stdGaussian (EuclideanSpace ℝ (Fin n)))).hasLaw).hasGaussianLaw
  have hind : IndepFun (fun p : BridgeBrownianSample n => X p.1)
      (fun p : BridgeBrownianSample n => Y p.2) (bridgeBrownianProductMeasure n) :=
    indepFun_prod₀ hX.aemeasurable hY.aemeasurable
  have hsum := (hind.hasGaussianLaw hXp hYp).add
  change HasGaussianLaw (fun p : BridgeBrownianSample n => fun q : I =>
    bridgeContinuousSeries n p.1 q.1.1 q.1.2 + (q.1.1 : ℝ) * p.2 q.1.2)
    (bridgeBrownianProductMeasure n)
  exact hsum

theorem bridgeBrownianLaw_gaussian_process (n : ℕ) :
    IsGaussianProcess (fun q : Icc (0 : ℝ) 1 × Fin n =>
      fun f : C(Icc (0 : ℝ) 1, EuclideanSpace ℝ (Fin n)) => f q.1 q.2)
      (bridgeBrownianLaw n) := by
  constructor
  intro I
  have hG := (bridgeBrownianPath_gaussian_process n).hasGaussianLaw I
  let g : C(Icc (0 : ℝ) 1, EuclideanSpace ℝ (Fin n)) → I → ℝ :=
    fun f q => f q.1.1 q.1.2
  have hg : Measurable g := by fun_prop
  refine ⟨hg.aemeasurable, ?_⟩
  change IsGaussian ((bridgeBrownianLaw n).map g)
  rw [bridgeBrownianLaw, Measure.map_map hg (bridgeBrownianPath_measurable n)]
  exact hG.isGaussian_map

end AffineFKProof
