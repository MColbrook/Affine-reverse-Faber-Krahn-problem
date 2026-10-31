module

public import AffineFK.ConvolutionScoreRegression
public import AffineFK.GaussianRelativeScoreRegression
public import AffineFK.GaussianSmoothingIsotropy
public import AffineFK.PoincareConstantLinearMap
public import AffineFK.OrnsteinUhlenbeckScales
public import AffineFK.OUEntropyContraction

/-!
# Actual positive-time OU score regression

Original isotropy and an original least-Poincare bound supply the true
smoothed domains. The actual relative-score derivatives differ by exactly
the ordinary logarithmic Hessians: the identity matrices cancel.
No score moment, derivative integrability or output Poincare premise is
assumed in the final one-sided regression theorem.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory TopologicalSpace Matrix
open scoped ContDiff RealInnerProductSpace ENNReal NNReal Matrix.Norms.L2Operator

theorem gaussianRelativeScore_derivativeMatrix_difference (n : ℕ)
    (f g : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ContDiff ℝ ∞ f) (hfpos : ∀ x, 0 < f x)
    (hg : ContDiff ℝ ∞ g) (hgpos : ∀ x, 0 < g x)
    (x y : EuclideanSpace ℝ (Fin n)) :
    vectorPoincareDerivativeMatrix n (gaussianRelativeScore n f) x -
      vectorPoincareDerivativeMatrix n (gaussianRelativeScore n g) y =
      densityLogHessian n f x - densityLogHessian n g y := by
  ext i j
  change gradient (fun z => gaussianRelativeScore n f z i) x j -
      gradient (fun z => gaussianRelativeScore n g z i) y j = _
  rw [gaussianRelativeScore_component_gradient n f hf hfpos i x,
    gaussianRelativeScore_component_gradient n g hg hgpos i y]
  simp only [PiLp.add_apply]
  change (gradient (fun z => gradient (fun w => Real.log (f w)) z i) x j +
      (EuclideanSpace.basisFun (Fin n) ℝ i) j) -
    (gradient (fun z => gradient (fun w => Real.log (g w)) z i) y j +
      (EuclideanSpace.basisFun (Fin n) ℝ i) j) =
      gradient (fun z => gradient (fun w => Real.log (f w)) z i) x j -
        gradient (fun z => gradient (fun w => Real.log (g w)) z i) y j
  ring

theorem vectorPoincareDerivativeMatrix_hilbertSchmidtSq (n : ℕ)
    (r : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (x : EuclideanSpace ℝ (Fin n)) :
    matrixHilbertSchmidtSq (vectorPoincareDerivativeMatrix n r x) =
      ∑ i : Fin n, ‖gradient (fun y => r y i) x‖ ^ 2 := by
  simp only [matrixHilbertSchmidtSq, vectorPoincareDerivativeMatrix, EuclideanSpace.real_norm_sq_eq]

theorem poincareConstant_OU_le_original_bound (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (P : ℝ≥0) (hPone : 1 ≤ P) (hP : poincareConstant n ν ≤ (P : ℝ≥0∞))
    (t : ℝ) (ht : 0 ≤ t) : poincareConstant n (ouInitialLaw n ν t) ≤ (P : ℝ≥0∞) := by
  have hc : 0 ≤ Real.exp (-2 * t) := (Real.exp_pos _).le
  have hd : 0 ≤ 1 - Real.exp (-2 * t) := sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by linarith))
  have hPone' : (1 : ℝ) ≤ (P : ℝ) := hPone
  calc
    _ ≤ ENNReal.ofReal (Real.exp (-2 * t)) * poincareConstant n ν +
        ENNReal.ofReal (1 - Real.exp (-2 * t)) := poincareConstant_OU n ν t ht
    _ ≤ ENNReal.ofReal (Real.exp (-2 * t)) * (P : ℝ≥0∞) +
        ENNReal.ofReal (1 - Real.exp (-2 * t)) := add_le_add (mul_le_mul_right hP _) le_rfl
    _ = ENNReal.ofReal (Real.exp (-2 * t) * (P : ℝ) + (1 - Real.exp (-2 * t))) := by
      rw [← ENNReal.ofReal_coe_nnreal (p := P), ← ENNReal.ofReal_mul hc,
        ← ENNReal.ofReal_add (mul_nonneg hc P.coe_nonneg) hd]
    _ ≤ ENNReal.ofReal (P : ℝ) := ENNReal.ofReal_le_ofReal (by nlinarith)
    _ = (P : ℝ≥0∞) := ENNReal.ofReal_coe_nnreal

theorem ou_relativeScore_product_regression (n : ℕ)
    (ν η : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν] [IsProbabilityMeasure η]
    (hmean : ∀ i : Fin n, (∫ x : EuclideanSpace ℝ (Fin n), x i ∂ν) = 0)
    (hsecond : ∀ i j : Fin n, (∫ x : EuclideanSpace ℝ (Fin n), x i * x j ∂ν) =
      if i = j then (1 : ℝ) else 0)
    (P : ℝ≥0) (hPone : 1 ≤ P) (hP : poincareConstant n ν ≤ (P : ℝ≥0∞))
    (t : ℝ) (ht : 0 < t) :
    let ρ : Measure (EuclideanSpace ℝ (Fin n)) → EuclideanSpace ℝ (Fin n) → ℝ :=
      fun κ => gaussianSmoothingDensity n κ (Real.exp (-t)) (Real.sqrt (1 - Real.exp (-2 * t)))
    ((∫ x, ‖gaussianRelativeScore n (ρ ν) x‖ ^ 2 ∂densityMeasure n (ρ ν)) +
      (∫ y, matrixHilbertSchmidtSq (vectorPoincareDerivativeMatrix n (gaussianRelativeScore n (ρ η)) y)
        ∂densityMeasure n (ρ η))) / (P : ℝ) ≤
      ∫ p, matrixHilbertSchmidtSq (densityLogHessian n (ρ ν) p.1 - densityLogHessian n (ρ η) p.2)
        ∂(densityMeasure n (ρ ν)).prod (densityMeasure n (ρ η)) := by
  let E := EuclideanSpace ℝ (Fin n)
  let c := Real.exp (-t)
  let d := Real.sqrt (1 - Real.exp (-2 * t))
  let ρ : Measure E → E → ℝ := fun κ => gaussianSmoothingDensity n κ c d
  have hd : 0 < d := (ou_smoothing_scale_domain t ht).2.1
  have hν : ouInitialLaw n ν t = densityMeasure n (ρ ν) := gaussianSmoothingDensity_law n ν c d hd
  have hη : ouInitialLaw n η t = densityMeasure n (ρ η) := gaussianSmoothingDensity_law n η c d hd
  let : IsProbabilityMeasure (densityMeasure n (ρ ν)) := by rw [← hν]; infer_instance
  let : IsProbabilityMeasure (densityMeasure n (ρ η)) := by rw [← hη]; infer_instance
  have hout := gaussianSmoothing_density_isotropy n ν hmean hsecond c d hd (ou_smoothing_scale_domain t ht).2.2
  have hX : MemLp (id : E → E) 2 (densityMeasure n (ρ ν)) :=
    memLp_piLp_iff.mpr fun i => (hout.1 i).1
  have hs : MemLp (gradient (fun x => Real.log (ρ ν x))) 2 (densityMeasure n (ρ ν)) :=
    (gaussianSmoothing_ordinaryScore_density_memLp_four n ν c d hd).1.mono_exponent (by norm_num)
  have hr : MemLp (gaussianRelativeScore n (ρ ν)) 2 (densityMeasure n (ρ ν)) := hs.add hX
  have hPout : poincareConstant n (densityMeasure n (ρ ν)) ≤ (P : ℝ≥0∞) := by
    rw [← hν]
    exact poincareConstant_OU_le_original_bound n ν P hPone hP t ht.le
  have hreg := (weakRelativeScore_product_regression n (densityMeasure n (ρ ν)) (densityMeasure n (ρ η))
    P (lt_of_lt_of_le zero_lt_one hPone) hPout (fun i => (hout.1 i).2.2) (fun i j => (hout.2 i j).2)
    (gaussianRelativeScore n (ρ ν)) (gaussianRelativeScore n (ρ η)) hr
    (fun F => (gaussianRelativeScore_vector_pairing n (ρ ν) (gaussianSmoothingDensity_smooth n ν c d)
      (gaussianSmoothingDensity_pos n ν c d hd) F).2.2)
    (gaussianRelativeScore_smooth n (ρ ν) (gaussianSmoothingDensity_smooth n ν c d)
      (gaussianSmoothingDensity_pos n ν c d hd))
    (gaussianSmoothing_relativeScore_component_gradient_memLp n ν c d hd)
    (gaussianSmoothing_relativeScore_component_gradient_memLp n η c d hd)).2
  have hfun (p : E × E) := gaussianRelativeScore_derivativeMatrix_difference n (ρ ν) (ρ η)
    (gaussianSmoothingDensity_smooth n ν c d) (gaussianSmoothingDensity_pos n ν c d hd)
    (gaussianSmoothingDensity_smooth n η c d) (gaussianSmoothingDensity_pos n η c d hd) p.1 p.2
  simpa only [hfun] using hreg

end AffineFKProof
