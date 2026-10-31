module

public import AffineFK.OrdinaryFisherLinearMapEnergy
public import AffineFK.PoincareSmoothExtension

/-!
# The actual normalized scalar L2 dilation

This is the genuine Jacobian-normalized linear pullback. Its exact L2
isometry and scalar coefficient limits are prerequisites for passing the
constructed inward H0 approximants to the original H1 value.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory TopologicalSpace InnerProductSpace Filter
open scoped Distributions RealInnerProductSpace Topology

def supportDilationLinearEquiv (n : ℕ) (a : ℝ) (ha : a ≠ 0) :
    EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n) :=
  (LinearEquiv.smulOfNeZero ℝ (EuclideanSpace ℝ (Fin n)) a ha).toContinuousLinearEquiv

theorem supportDilationLinearEquiv_symm_apply (n : ℕ) (a : ℝ) (ha : a ≠ 0)
    (x : EuclideanSpace ℝ (Fin n)) :
    (supportDilationLinearEquiv n a ha).symm x = a⁻¹ • x := rfl

theorem supportDilation_jacobian (n : ℕ) (a : ℝ) (ha : 0 < a) :
    ordinaryFisherLinearJacobian n (supportDilationLinearEquiv n a ha.ne') = (a⁻¹) ^ n := by
  change |LinearMap.det (a⁻¹ • (LinearMap.id : EuclideanSpace ℝ (Fin n) →ₗ[ℝ]
    EuclideanSpace ℝ (Fin n)))| = _
  rw [LinearMap.det_smul, LinearMap.det_id, finrank_euclideanSpace_fin, mul_one,
    abs_of_nonneg (pow_nonneg (inv_nonneg.mpr ha.le) n)]

def supportDilationL2 (n : ℕ) (a : ℝ) (ha : a ≠ 0) :
    Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) →L[ℝ]
      Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
  Real.sqrt (ordinaryFisherLinearJacobian n (supportDilationLinearEquiv n a ha)) •
    ordinaryFisherLinearPullbackLp n (supportDilationLinearEquiv n a ha) ℝ

theorem supportDilationL2_coe (n : ℕ) (a : ℝ) (ha : a ≠ 0)
    (f : Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    supportDilationL2 n a ha f =ᵐ[volume] fun x =>
      Real.sqrt (ordinaryFisherLinearJacobian n (supportDilationLinearEquiv n a ha)) * f (a⁻¹ • x) := by
  let A := supportDilationLinearEquiv n a ha
  let c := Real.sqrt (ordinaryFisherLinearJacobian n A)
  filter_upwards [Lp.coeFn_smul c (ordinaryFisherLinearPullbackLp n A ℝ f),
    ordinaryFisherLinearPullbackLp_coe n A f] with x hs hp
  change (c • ordinaryFisherLinearPullbackLp n A ℝ f : Lp ℝ 2 volume) x = _
  rw [hs]
  change c * ordinaryFisherLinearPullbackLp n A ℝ f x = _
  rw [hp]
  rfl

theorem supportDilationL2_norm (n : ℕ) (a : ℝ) (ha : a ≠ 0)
    (f : Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    ‖supportDilationL2 n a ha f‖ = ‖f‖ := by
  let A := supportDilationLinearEquiv n a ha
  have heq : (∫ x, ‖supportDilationL2 n a ha f x‖ ^ 2) =
      ∫ x, ‖Real.sqrt (ordinaryFisherLinearJacobian n A) • f (A.symm x)‖ ^ 2 := by
    apply integral_congr_ae
    filter_upwards [supportDilationL2_coe n a ha f] with x hx
    rw [hx]
    rfl
  have hsquare : ‖supportDilationL2 n a ha f‖ ^ 2 = ‖f‖ ^ 2 := by
    calc
      _ = ∫ x, ‖supportDilationL2 n a ha f x‖ ^ 2 := l2_norm_sq_integral volume _
      _ = _ := heq
      _ = ∫ x, ‖f x‖ ^ 2 := (ordinaryFisherLinear_scaled_pullback_energy n A f).2
      _ = _ := (l2_norm_sq_integral volume f).symm
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsquare

theorem supportDilationL2_norm_sub (n : ℕ) (a : ℝ) (ha : a ≠ 0)
    (f g : Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    ‖supportDilationL2 n a ha f - supportDilationL2 n a ha g‖ = ‖f - g‖ := by
  rw [← map_sub, supportDilationL2_norm]

theorem supportDilation_sqrt_jacobian_bound (n : ℕ) (a : ℝ) (ha : (1 / 2 : ℝ) ≤ a) :
    Real.sqrt (ordinaryFisherLinearJacobian n
      (supportDilationLinearEquiv n a (by linarith))) ≤ Real.sqrt ((2 : ℝ) ^ n) := by
  have ha0 : 0 < a := by linarith
  rw [supportDilation_jacobian n a ha0]
  apply Real.sqrt_le_sqrt
  have hi : a⁻¹ ≤ (2 : ℝ) := by
    rw [inv_eq_one_div]
    exact (div_le_iff₀ ha0).mpr (by linarith)
  exact pow_le_pow_left₀ (inv_nonneg.mpr ha0.le) hi n

theorem supportDilation_sqrt_jacobian_tendsto (n : ℕ) (a : ℕ → ℝ)
    (ha : ∀ k, 0 < a k) (hlim : Tendsto a atTop (𝓝 1)) :
    Tendsto (fun k => Real.sqrt (ordinaryFisherLinearJacobian n
      (supportDilationLinearEquiv n (a k) (ha k).ne'))) atTop (𝓝 1) := by
  simp_rw [supportDilation_jacobian n _ (ha _)]
  have hpow := (hlim.inv₀ (by norm_num : (1 : ℝ) ≠ 0)).pow n
  simpa only [Function.comp_def, inv_one, one_pow, Real.sqrt_one] using
    Real.continuous_sqrt.continuousAt.tendsto.comp hpow

end AffineFKProof
