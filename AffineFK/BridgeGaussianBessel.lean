module

public import AffineFK.BridgeCoefficientCovariance
public import Mathlib.Analysis.InnerProductSpace.Orthonormal
public import Mathlib.MeasureTheory.Function.L2Space

/-!
# Dimension-free Gaussian Bessel estimates

The actual standard Gaussian coordinate functions are orthonormal in L2.
Mathlib's proved finite Bessel inequality then bounds their correlations
with any L2 function, including the sharper centred variance bound.
No differentiability or boundedness assumption on that function is needed.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators RealInnerProductSpace

theorem bridgeGaussian_coordinate_memLp (n : ℕ) (i : Fin n) :
    MemLp (fun x : EuclideanSpace ℝ (Fin n) => x i) 2
      (stdGaussian (EuclideanSpace ℝ (Fin n))) := by
  simpa only [coordinateFunctional_apply, Function.comp_def, id_eq] using
    ((IsGaussian.hasGaussianLaw_id (μ := stdGaussian (EuclideanSpace ℝ (Fin n)))).map
      (coordinateFunctional n i)).memLp_two

def bridgeGaussianCoordinateL2 (n : ℕ) (i : Fin n) :
    Lp ℝ 2 (stdGaussian (EuclideanSpace ℝ (Fin n))) :=
  (bridgeGaussian_coordinate_memLp n i).toLp (fun x => x i)

theorem bridgeGaussianCoordinateL2_coe (n : ℕ) (i : Fin n) :
    (bridgeGaussianCoordinateL2 n i : EuclideanSpace ℝ (Fin n) → ℝ) =ᵐ[
      stdGaussian (EuclideanSpace ℝ (Fin n))] fun x => x i :=
  MemLp.coeFn_toLp (bridgeGaussian_coordinate_memLp n i)

theorem bridgeGaussianCoordinateL2_inner (n : ℕ) (i j : Fin n) :
    ⟪bridgeGaussianCoordinateL2 n i, bridgeGaussianCoordinateL2 n j⟫ =
      if i = j then 1 else 0 := by
  rw [L2.inner_def]
  calc
    _ = ∫ x : EuclideanSpace ℝ (Fin n), x i * x j
        ∂stdGaussian (EuclideanSpace ℝ (Fin n)) := by
      apply integral_congr_ae
      filter_upwards [bridgeGaussianCoordinateL2_coe n i,
        bridgeGaussianCoordinateL2_coe n j] with x hi hj
      simp [hi, hj, mul_comm]
    _ = _ := bridgeGaussian_coordinate_cross_moment n i j

theorem bridgeGaussianCoordinateL2_orthonormal (n : ℕ) :
    Orthonormal ℝ (bridgeGaussianCoordinateL2 n) := by
  classical
  rw [orthonormal_iff_ite]
  exact bridgeGaussianCoordinateL2_inner n

theorem bridgeRealL2_norm_toLp_sq {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f : X → ℝ) (hf : MemLp f 2 μ) :
    ‖hf.toLp f‖ ^ 2 = ∫ x, (f x)^2 ∂μ := by
  calc
    _ = ⟪hf.toLp f, hf.toLp f⟫ := (real_inner_self_eq_norm_sq _).symm
    _ = ∫ x, ⟪hf.toLp f x, hf.toLp f x⟫ ∂μ := L2.inner_def _ _
    _ = ∫ x, (f x)^2 ∂μ := by
      apply integral_congr_ae
      filter_upwards [MemLp.coeFn_toLp hf] with x hx
      simp [hx, pow_two]

theorem bridgeGaussian_coordinate_bessel (n : ℕ)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : MemLp f 2 (stdGaussian (EuclideanSpace ℝ (Fin n)))) :
    (∑ i : Fin n, (∫ x, x i * f x ∂stdGaussian (EuclideanSpace ℝ (Fin n)))^2) ≤
      ∫ x, (f x)^2 ∂stdGaussian (EuclideanSpace ℝ (Fin n)) := by
  have h := (bridgeGaussianCoordinateL2_orthonormal n).sum_inner_products_le
    (s := Finset.univ) (hf.toLp f)
  have hi (i : Fin n) : ⟪bridgeGaussianCoordinateL2 n i, hf.toLp f⟫ =
      ∫ x, x i * f x ∂stdGaussian (EuclideanSpace ℝ (Fin n)) := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [bridgeGaussianCoordinateL2_coe n i, MemLp.coeFn_toLp hf] with x hi hf
    simp [hi, hf, mul_comm]
  simpa only [hi, Real.norm_eq_abs, sq_abs,
    bridgeRealL2_norm_toLp_sq] using h

theorem bridgeGaussian_coordinate_bessel_variance (n : ℕ)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : MemLp f 2 (stdGaussian (EuclideanSpace ℝ (Fin n)))) :
    (∑ i : Fin n, (∫ x, x i * f x ∂stdGaussian (EuclideanSpace ℝ (Fin n)))^2) ≤
      (∫ x, (f x)^2 ∂stdGaussian (EuclideanSpace ℝ (Fin n))) -
        (∫ x, f x ∂stdGaussian (EuclideanSpace ℝ (Fin n)))^2 := by
  let μ := stdGaussian (EuclideanSpace ℝ (Fin n))
  let m : ℝ := ∫ x, f x ∂μ
  let g : EuclideanSpace ℝ (Fin n) → ℝ := fun x => f x - m
  have hgf : MemLp g 2 μ := hf.sub (memLp_const m)
  have hif : Integrable f μ := hf.integrable (by norm_num)
  have hisq : Integrable (fun x => (f x)^2) μ :=
    (memLp_two_iff_integrable_sq hf.aestronglyMeasurable).mp hf
  have hcross (i : Fin n) : (∫ x, x i * g x ∂μ) = ∫ x, x i * f x ∂μ := by
    have hic := (bridgeGaussian_coordinate_memLp n i).integrable (by norm_num)
    have hip : Integrable (fun x => x i * f x) μ :=
      (bridgeGaussian_coordinate_memLp n i).integrable_mul hf
    have him : Integrable (fun x : EuclideanSpace ℝ (Fin n) => x i * m) μ :=
      hic.mul_const m
    change (∫ x, x i * (f x - m) ∂μ) = _
    simp_rw [mul_sub]
    rw [integral_sub hip him, integral_mul_const]
    rw [show (∫ x : EuclideanSpace ℝ (Fin n), x i ∂μ) = 0 from
      bridgeGaussian_coordinate_mean n i]
    simp
  have hvariance : (∫ x, (g x)^2 ∂μ) = (∫ x, (f x)^2 ∂μ) - m^2 := by
    have him : Integrable (fun x => (2*m)*f x) μ := hif.const_mul (2*m)
    have hid : Integrable (fun x => (f x)^2 - (2*m)*f x) μ := hisq.sub him
    have hic : Integrable (fun _ : EuclideanSpace ℝ (Fin n) => m^2) μ := integrable_const _
    have he : (fun x => (g x)^2) = fun x => (f x)^2 - (2*m)*f x + m^2 := by
      funext x
      dsimp [g]
      ring
    rw [he, integral_add hid hic, integral_sub hisq him, integral_const_mul]
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
    change (∫ x, (f x)^2 ∂μ) - (2*m)*m + m^2 = _
    ring
  have hb := bridgeGaussian_coordinate_bessel n g hgf
  change (∑ i : Fin n, (∫ x, x i * g x ∂μ)^2) ≤ (∫ x, (g x)^2 ∂μ) at hb
  simpa only [hcross, hvariance] using hb

end AffineFKProof
