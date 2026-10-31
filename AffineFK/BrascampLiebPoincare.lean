module

public import AffineFK.ChafaiBrascampLieb.Analysis.CorrespondenceBrascampLieb
public import AffineFK.StrongConvexInverseHessian
public import AffineFK.GaussianSmoothedScoreHessianSymmetry
public import AffineFK.PoincareConstant

/-!
# Unit-curvature Gibbs Poincare inequality

The actual global Brascamp--Lieb variance theorem is due to Djalil Chafai's
MIT-licensed formalization, pinned at commit
a1b2ba84e7dad8ba11b5c49a18b986a762a00a41. Its original sources, licence,
rc3 proof-body compatibility changes and import-only integration receipt
are retained under vendor/ and AffineFK/ChafaiBrascampLieb/.

The matrix lower bound below is the actual component Hessian minus the
identity. It gives positive definiteness and the inverse quadratic bound;
the variance conclusion is not an input. Supported or nonsmooth potentials
require a separate approximation argument.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory TopologicalSpace InnerProductSpace
open scoped Distributions ContDiff RealInnerProductSpace Matrix BigOperators ENNReal

theorem brascampLieb_gradient_coordinates (n : ℕ)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    GinibrePoincare.correspondenceBrascampLiebGradient f
      (EuclideanSpace.basisFun (Fin n) ℝ) x = fun i => gradient f x i := by
  funext i
  exact (gradient_coordinate_eq_fderiv n f x i).symm

theorem brascampLieb_hessian_coordinates (n : ℕ)
    (W : EuclideanSpace ℝ (Fin n) → ℝ) (hW : ContDiff ℝ ∞ W)
    (x : EuclideanSpace ℝ (Fin n)) :
    GinibrePoincare.correspondenceBrascampLiebHessian W
      (EuclideanSpace.basisFun (Fin n) ℝ) x =
      fun i j => gradient (fun y => gradient W y i) x j := by
  ext i j
  change fderiv ℝ (fun y => fderiv ℝ W y (EuclideanSpace.basisFun (Fin n) ℝ i)) x
    (EuclideanSpace.basisFun (Fin n) ℝ j) = _
  have heq : (fun y => fderiv ℝ W y (EuclideanSpace.basisFun (Fin n) ℝ i)) =
      fun y => gradient W y i :=
    funext fun y => (gradient_coordinate_eq_fderiv n W y i).symm
  rw [heq]
  exact (gradient_coordinate_eq_fderiv n _ x j).symm

theorem brascampLieb_unit_curvature_compact_variance (n : ℕ)
    (W : EuclideanSpace ℝ (Fin n) → ℝ) (hW : ContDiff ℝ ∞ W)
    (hWi : Integrable (fun x => Real.exp (-W x)))
    (hMass : (∫ x, Real.exp (-W x)) = 1)
    (hcurv : ∀ x, Matrix.PosSemidef
      (Matrix.of (fun i j : Fin n => gradient (fun y => gradient W y i) x j) -
        (1 : Matrix (Fin n) (Fin n) ℝ)))
    (f : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ)) :
    (∫ x, (f x - ∫ y, f y ∂densityMeasure n (fun z => Real.exp (-W z))) ^ 2
      ∂densityMeasure n (fun z => Real.exp (-W z))) ≤
      ∫ x, ‖gradient f x‖ ^ 2 ∂densityMeasure n (fun z => Real.exp (-W z)) := by
  let b := EuclideanSpace.basisFun (Fin n) ℝ
  let μ := GinibrePoincare.correspondenceBrascampLiebMeasure W
  letI := GinibrePoincare.correspondenceBrascampLieb_finite_measure W hWi
  have hW2 : ContDiff ℝ 2 W := hW.of_le (by simp)
  have hf1 : ContDiff ℝ 1 f := f.contDiff.of_le (by simp)
  have hpos (x) : (GinibrePoincare.correspondenceBrascampLiebHessian W b x).PosDef := by
    rw [brascampLieb_hessian_coordinates n W hW]
    exact strongConvex_matrix_posDef _ (hcurv x)
  have hfL2 : MemLp f 2 μ :=
    f.continuous.memLp_of_hasCompactSupport f.hasCompactSupport
  have hfE : Integrable (GinibrePoincare.correspondenceBrascampLiebInverseEnergy W f b) μ :=
    GinibrePoincare.correspondenceBrascampLieb_integrable_compact W _ hW.continuous
      (GinibrePoincare.correspondenceBrascampLieb_inverse_energy_continuous W f b hW2 hf1 hpos)
      (GinibrePoincare.correspondenceBrascampLieb_inverse_energy_compact W f b f.hasCompactSupport)
  have hgL2 : MemLp (gradient f) 2 μ := by
    have h := (testFunctionGradient f).continuous.memLp_of_hasCompactSupport
      (μ := μ) (p := (2 : ℝ≥0∞)) (testFunctionGradient f).hasCompactSupport
    have heq : (testFunctionGradient f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) =
        gradient f := funext fun x => testFunctionGradient_apply f x
    simpa only [heq] using! h
  have hg : Integrable (fun x => ‖gradient f x‖ ^ 2) μ := hgL2.integrable_norm_pow (by norm_num)
  have hb (x) : GinibrePoincare.correspondenceBrascampLiebInverseEnergy W f b x ≤
      ‖gradient f x‖ ^ 2 := by
    unfold GinibrePoincare.correspondenceBrascampLiebInverseEnergy
    rw [brascampLieb_gradient_coordinates n f x, brascampLieb_hessian_coordinates n W hW x]
    exact (strongConvex_inverse_quadratic_bound _ (hcurv x) _).trans_eq
      (EuclideanSpace.real_norm_sq_eq (gradient f x)).symm
  have hBL := GinibrePoincare.correspondenceBrascampLieb_probability_variance W f b
    hW2 hWi hMass hpos hf1 hfL2 hfE
  exact hBL.trans (integral_mono hfE hg hb)

theorem brascampLieb_unit_curvature_poincareConstant_le_one (n : ℕ)
    (W : EuclideanSpace ℝ (Fin n) → ℝ) (hW : ContDiff ℝ ∞ W)
    (hWi : Integrable (fun x => Real.exp (-W x)))
    (hMass : (∫ x, Real.exp (-W x)) = 1)
    (hcurv : ∀ x, Matrix.PosSemidef
      (Matrix.of (fun i j : Fin n => gradient (fun y => gradient W y i) x j) -
        (1 : Matrix (Fin n) (Fin n) ℝ))) :
    poincareConstant n (densityMeasure n (fun x => Real.exp (-W x))) ≤ 1 := by
  apply (poincareConstant_le_of_admissible n _ 1)
  intro f
  simpa only [NNReal.coe_one, one_mul] using
    brascampLieb_unit_curvature_compact_variance n W hW hWi hMass hcurv f

end AffineFKProof
