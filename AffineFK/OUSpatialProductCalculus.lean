module

public import AffineFK.EuclideanBochner
public import AffineFK.OUDensityPDECalculus

/-!
# Product and logarithmic formulae for the actual OU density operator

The density operator is the divergence-form operator already used in the
OU equation. Its product rule and logarithmic formula follow from actual
coordinate differentiation, with no PDE or integration hypothesis.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open InnerProductSpace
open scoped ContDiff RealInnerProductSpace

theorem euclidean_coordinate_smooth (n : ℕ) (i : Fin n) :
    ContDiff ℝ ∞ (fun x : EuclideanSpace ℝ (Fin n) => x i) := by
  have h : (fun x : EuclideanSpace ℝ (Fin n) => x i) = coordinateFunctional n i :=
    funext fun x => (coordinateFunctional_apply n i x).symm
  rw [h]
  exact (coordinateFunctional n i).contDiff

theorem euclideanPartial_second_mul (n : ℕ) (i : Fin n)
    (f g : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (x : EuclideanSpace ℝ (Fin n)) :
    euclideanPartial n i (euclideanPartial n i (fun y => f y * g y)) x =
      f x * euclideanPartial n i (euclideanPartial n i g) x +
      g x * euclideanPartial n i (euclideanPartial n i f) x +
      2 * euclideanPartial n i f x * euclideanPartial n i g x := by
  have h : euclideanPartial n i (fun y => f y * g y) =
      fun y => f y * euclideanPartial n i g y + g y * euclideanPartial n i f y :=
    funext (euclideanPartial_mul n i f g hf hg)
  rw [h, euclideanPartial_add n i _ _ (hf.mul (euclideanPartial_smooth n i g hg))
    (hg.mul (euclideanPartial_smooth n i f hf)),
    euclideanPartial_mul n i _ _ hf (euclideanPartial_smooth n i g hg),
    euclideanPartial_mul n i _ _ hg (euclideanPartial_smooth n i f hf)]
  ring

theorem euclideanLaplacian_mul (n : ℕ)
    (f g : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (x : EuclideanSpace ℝ (Fin n)) :
    euclideanLaplacian n (fun y => f y * g y) x =
      f x * euclideanLaplacian n g x + g x * euclideanLaplacian n f x +
      2 * ∑ i, euclideanPartial n i f x * euclideanPartial n i g x := by
  unfold euclideanLaplacian
  simp_rw [euclideanPartial_second_mul n _ f g hf hg]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, mul_assoc]

theorem ouDensitySpatialOperator_eq_laplacian (n : ℕ)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ContDiff ℝ ∞ f)
    (x : EuclideanSpace ℝ (Fin n)) :
    ouDensitySpatialOperator n f x = euclideanLaplacian n f x + (n : ℝ) * f x +
      ∑ i, x i * euclideanPartial n i f x := by
  change (∑ i : Fin n, (euclideanPartial n i (euclideanPartial n i f) x +
    euclideanPartial n i (fun y => y i * f y) x)) = _
  simp only [euclideanPartial_mul n _ _ _ (euclidean_coordinate_smooth n _) hf,
    euclideanPartial_coordinate, ite_true, mul_one,
    Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, euclideanLaplacian]
  ring

theorem ouDensitySpatialOperator_mul (n : ℕ)
    (f g : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (x : EuclideanSpace ℝ (Fin n)) :
    ouDensitySpatialOperator n (fun y => f y * g y) x =
      g x * ouDensitySpatialOperator n f x + f x * euclideanLaplacian n g x +
      2 * (∑ i, euclideanPartial n i f x * euclideanPartial n i g x) +
      f x * ∑ i, x i * euclideanPartial n i g x := by
  rw [ouDensitySpatialOperator_eq_laplacian n _ (hf.mul hg),
    euclideanLaplacian_mul n f g hf hg, ouDensitySpatialOperator_eq_laplacian n f hf]
  simp_rw [euclideanPartial_mul n _ f g hf hg]
  have h : (∑ i, x i * (f x * euclideanPartial n i g x + g x * euclideanPartial n i f x)) =
      f x * (∑ i, x i * euclideanPartial n i g x) +
      g x * ∑ i, x i * euclideanPartial n i f x := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [h]
  ring

theorem logDensity_partial_mul (n : ℕ) (i : Fin n)
    (ρ : EuclideanSpace ℝ (Fin n) → ℝ) (hρ : ContDiff ℝ ∞ ρ)
    (hρpos : ∀ x, 0 < ρ x) (x : EuclideanSpace ℝ (Fin n)) :
    euclideanPartial n i ρ x =
      ρ x * euclideanPartial n i (fun y => Real.log (ρ y)) x := by
  rw [euclideanPartial_eq_gradient n i (fun y => Real.log (ρ y)),
    log_density_gradient_coordinate n ρ hρ hρpos]
  unfold euclideanPartial
  field_simp [(hρpos x).ne']

theorem logDensity_second_partial (n : ℕ) (i : Fin n)
    (ρ : EuclideanSpace ℝ (Fin n) → ℝ) (hρ : ContDiff ℝ ∞ ρ)
    (hρpos : ∀ x, 0 < ρ x) (x : EuclideanSpace ℝ (Fin n)) :
    euclideanPartial n i (euclideanPartial n i ρ) x = ρ x *
      (euclideanPartial n i (euclideanPartial n i (fun y => Real.log (ρ y))) x +
        (euclideanPartial n i (fun y => Real.log (ρ y)) x) ^ 2) := by
  have hv := hρ.log (fun y => (hρpos y).ne')
  have h : euclideanPartial n i ρ =
      fun y => ρ y * euclideanPartial n i (fun z => Real.log (ρ z)) y :=
    funext (logDensity_partial_mul n i ρ hρ hρpos)
  rw [h, euclideanPartial_mul n i _ _ hρ (euclideanPartial_smooth n i _ hv),
    logDensity_partial_mul n i ρ hρ hρpos]
  ring

theorem ouDensitySpatialOperator_log_ratio (n : ℕ)
    (ρ : EuclideanSpace ℝ (Fin n) → ℝ) (hρ : ContDiff ℝ ∞ ρ)
    (hρpos : ∀ x, 0 < ρ x) (x : EuclideanSpace ℝ (Fin n)) :
    ouDensitySpatialOperator n ρ x / ρ x =
      euclideanLaplacian n (fun y => Real.log (ρ y)) x +
      euclideanGradientSq n (fun y => Real.log (ρ y)) x + (n : ℝ) +
      ∑ i, x i * euclideanPartial n i (fun y => Real.log (ρ y)) x := by
  have hL : euclideanLaplacian n ρ x = ρ x *
      (euclideanLaplacian n (fun y => Real.log (ρ y)) x +
        euclideanGradientSq n (fun y => Real.log (ρ y)) x) := by
    unfold euclideanLaplacian euclideanGradientSq
    simp_rw [logDensity_second_partial n _ ρ hρ hρpos]
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib, pow_two]
  rw [ouDensitySpatialOperator_eq_laplacian n ρ hρ, hL]
  simp_rw [logDensity_partial_mul n _ ρ hρ hρpos]
  apply (div_eq_iff (hρpos x).ne').mpr
  have hsum : (∑ i, x i * (ρ x * euclideanPartial n i (fun y => Real.log (ρ y)) x)) =
      ρ x * ∑ i, x i * euclideanPartial n i (fun y => Real.log (ρ y)) x := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hsum]
  ring

end AffineFKProof
