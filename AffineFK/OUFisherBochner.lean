module

public import AffineFK.OUSpatialProductCalculus
public import AffineFK.GaussianHessianL2Calculus

/-!
# The pointwise OU Fisher-energy identity

The Euclidean Bochner formula and actual OU product rule give the local
identity underlying Fisher dissipation. Smoothness and strict positivity
of the density are the only assumptions. There is no assumed time
equation, integrability, or integrated dissipation conclusion.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open InnerProductSpace
open scoped ContDiff RealInnerProductSpace

def euclideanDilation (n : ℕ) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ∑ i, x i * euclideanPartial n i f x

theorem euclideanDilation_smooth (n : ℕ)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (euclideanDilation n f) := by
  apply ContDiff.sum
  intro i _
  exact (euclidean_coordinate_smooth n i).mul (euclideanPartial_smooth n i f hf)

theorem euclideanPartial_dilation (n : ℕ) (i : Fin n)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ContDiff ℝ ∞ f)
    (x : EuclideanSpace ℝ (Fin n)) :
    euclideanPartial n i (euclideanDilation n f) x =
      euclideanPartial n i f x +
        ∑ k, x k * euclideanPartial n i (euclideanPartial n k f) x := by
  unfold euclideanDilation
  rw [euclideanPartial_sum n i _ (fun k =>
    (euclidean_coordinate_smooth n k).mul (euclideanPartial_smooth n k f hf))]
  simp_rw [euclideanPartial_mul n i _ _ (euclidean_coordinate_smooth n _)
    (euclideanPartial_smooth n _ f hf), euclideanPartial_coordinate]
  simp only [Finset.sum_add_distrib, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ring

theorem euclideanGradient_dilation_cross (n : ℕ)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ContDiff ℝ ∞ f)
    (x : EuclideanSpace ℝ (Fin n)) :
    2 * (∑ i, euclideanPartial n i f x *
      (∑ k, x k * euclideanPartial n i (euclideanPartial n k f) x)) =
      ∑ k, x k * euclideanPartial n k (euclideanGradientSq n f) x := by
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  rw [euclideanPartial_gradientSq n k f hf, Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [euclideanPartial_commute n k i f hf]
  ring

theorem ouDensitySpatialOperator_log_ratio_partial (n : ℕ) (i : Fin n)
    (ρ : EuclideanSpace ℝ (Fin n) → ℝ) (hρ : ContDiff ℝ ∞ ρ)
    (hρpos : ∀ x, 0 < ρ x) (x : EuclideanSpace ℝ (Fin n)) :
    euclideanPartial n i (fun y => ouDensitySpatialOperator n ρ y / ρ y) x =
      euclideanPartial n i (euclideanLaplacian n (fun y => Real.log (ρ y))) x +
      euclideanPartial n i (euclideanGradientSq n (fun y => Real.log (ρ y))) x +
      euclideanPartial n i (fun y => Real.log (ρ y)) x +
      ∑ k, x k * euclideanPartial n i
        (euclideanPartial n k (fun y => Real.log (ρ y))) x := by
  let v := fun y => Real.log (ρ y)
  have hv : ContDiff ℝ ∞ v := hρ.log (fun y => (hρpos y).ne')
  have h : (fun y => ouDensitySpatialOperator n ρ y / ρ y) =
      fun y => euclideanLaplacian n v y + euclideanGradientSq n v y +
        (n : ℝ) + euclideanDilation n v y :=
    funext (ouDensitySpatialOperator_log_ratio n ρ hρ hρpos)
  rw [h, euclideanPartial_add n i _ _
    (((euclideanLaplacian_smooth n v hv).add (euclideanGradientSq_smooth n v hv)).add contDiff_const)
    (euclideanDilation_smooth n v hv),
    euclideanPartial_add n i _ _
      ((euclideanLaplacian_smooth n v hv).add (euclideanGradientSq_smooth n v hv)) contDiff_const,
    euclideanPartial_add n i _ _ (euclideanLaplacian_smooth n v hv)
      (euclideanGradientSq_smooth n v hv),
    euclideanPartial_const, euclideanPartial_dilation n i v hv]
  dsimp only [v]
  ring

theorem ou_fisher_bochner_coordinate_identity (n : ℕ)
    (ρ : EuclideanSpace ℝ (Fin n) → ℝ) (hρ : ContDiff ℝ ∞ ρ)
    (hρpos : ∀ x, 0 < ρ x) (x : EuclideanSpace ℝ (Fin n)) :
    2 * ρ x * (∑ i, euclideanPartial n i (fun y => Real.log (ρ y)) x *
      euclideanPartial n i (fun y => ouDensitySpatialOperator n ρ y / ρ y) x) +
      euclideanGradientSq n (fun y => Real.log (ρ y)) x * ouDensitySpatialOperator n ρ x =
      ouDensitySpatialOperator n (fun y => ρ y * euclideanGradientSq n (fun z => Real.log (ρ z)) y) x +
      2 * ρ x * euclideanGradientSq n (fun y => Real.log (ρ y)) x -
      2 * ρ x * (∑ i, ∑ k, (euclideanPartial n i
        (euclideanPartial n k (fun y => Real.log (ρ y))) x) ^ 2) := by
  let v := fun y => Real.log (ρ y)
  have hv : ContDiff ℝ ∞ v := hρ.log (fun y => (hρpos y).ne')
  have hcross := euclideanGradient_dilation_cross n v hv x
  have hsum : (∑ i, euclideanPartial n i v x *
      euclideanPartial n i (fun y => ouDensitySpatialOperator n ρ y / ρ y) x) =
      (∑ i, euclideanPartial n i v x * euclideanPartial n i (euclideanLaplacian n v) x) +
      (∑ i, euclideanPartial n i v x * euclideanPartial n i (euclideanGradientSq n v) x) +
      euclideanGradientSq n v x +
      ∑ i, euclideanPartial n i v x * (∑ k, x k * euclideanPartial n i (euclideanPartial n k v) x) := by
    simp_rw [ouDensitySpatialOperator_log_ratio_partial n _ ρ hρ hρpos,
      mul_add, Finset.sum_add_distrib]
    rfl
  have hgrad : (∑ i, euclideanPartial n i ρ x * euclideanPartial n i (euclideanGradientSq n v) x) =
      ρ x * ∑ i, euclideanPartial n i v x * euclideanPartial n i (euclideanGradientSq n v) x := by
    simp_rw [logDensity_partial_mul n _ ρ hρ hρpos]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hop := ouDensitySpatialOperator_mul n ρ (euclideanGradientSq n v) hρ
    (euclideanGradientSq_smooth n v hv) x
  rw [euclidean_bochner_identity n v hv, hgrad] at hop
  change 2 * ρ x * (∑ i, euclideanPartial n i v x *
    euclideanPartial n i (fun y => ouDensitySpatialOperator n ρ y / ρ y) x) +
    euclideanGradientSq n v x * ouDensitySpatialOperator n ρ x = _
  rw [hsum, hop]
  have hcrossρ := congrArg (fun z : ℝ => ρ x * z) hcross
  dsimp only [v] at hcrossρ ⊢
  nlinarith only [hcrossρ]

theorem ou_fisher_bochner_identity (n : ℕ)
    (ρ : EuclideanSpace ℝ (Fin n) → ℝ) (hρ : ContDiff ℝ ∞ ρ)
    (hρpos : ∀ x, 0 < ρ x) (x : EuclideanSpace ℝ (Fin n)) :
    2 * (∑ i, gradient (fun y => Real.log (ρ y)) x i *
      gradient (fun y => ouDensitySpatialOperator n ρ y / ρ y) x i) * ρ x +
      ‖gradient (fun y => Real.log (ρ y)) x‖ ^ 2 * ouDensitySpatialOperator n ρ x =
      ouDensitySpatialOperator n (fun y => ‖gradient (fun z => Real.log (ρ z)) y‖ ^ 2 * ρ y) x +
      2 * (‖gradient (fun y => Real.log (ρ y)) x‖ ^ 2 * ρ x) -
      2 * ρ x * matrixHilbertSchmidtSq (densityLogHessian n ρ x) := by
  have h := ou_fisher_bochner_coordinate_identity n ρ hρ hρpos x
  have hfun : (fun y => ρ y * euclideanGradientSq n (fun z => Real.log (ρ z)) y) =
      fun y => ‖gradient (fun z => Real.log (ρ z)) y‖ ^ 2 * ρ y := by
    funext y
    rw [euclideanGradientSq_eq_norm]
    ring
  have hmatrix : (∑ i, ∑ k, (euclideanPartial n i
      (euclideanPartial n k (fun y => Real.log (ρ y))) x) ^ 2) =
      matrixHilbertSchmidtSq (densityLogHessian n ρ x) := by
    unfold matrixHilbertSchmidtSq densityLogHessian
    simp_rw [funext (euclideanPartial_eq_gradient n _ (fun y => Real.log (ρ y))),
      euclideanPartial_eq_gradient]
    exact Finset.sum_comm
  rw [hfun, hmatrix] at h
  simp only [euclideanPartial_eq_gradient, euclideanGradientSq_eq_norm] at h
  nlinarith [h]

end AffineFKProof
