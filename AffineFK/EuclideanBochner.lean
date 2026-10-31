module

public import AffineFK.EuclideanPartialCalculus
public import AffineFK.MatrixHilbertSchmidt

/-!
# The Euclidean Bochner identity in coordinates

All derivatives below are the actual Frechet derivatives. The third
derivatives commute by the proved Schwarz theorem; no jet relation or
Bochner conclusion is assumed. The Hilbert--Schmidt term is the explicit
sum of squared matrix entries.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open InnerProductSpace
open scoped ContDiff RealInnerProductSpace

def euclideanLaplacian (n : ℕ) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ∑ i, euclideanPartial n i (euclideanPartial n i f) x

def euclideanGradientSq (n : ℕ) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ∑ i, euclideanPartial n i f x * euclideanPartial n i f x

theorem euclideanGradientSq_eq_norm (n : ℕ)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    euclideanGradientSq n f x = ‖gradient f x‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp only [euclideanGradientSq, euclideanPartial_eq_gradient, pow_two]

theorem euclideanGradientSq_smooth (n : ℕ)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (euclideanGradientSq n f) := by
  apply ContDiff.sum
  intro i _
  exact (euclideanPartial_smooth n i f hf).mul (euclideanPartial_smooth n i f hf)

theorem euclideanLaplacian_smooth (n : ℕ)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (euclideanLaplacian n f) := by
  apply ContDiff.sum
  intro i _
  exact euclideanPartial_smooth n i _ (euclideanPartial_smooth n i f hf)

theorem euclideanPartial_gradientSq (n : ℕ) (i : Fin n)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ContDiff ℝ ∞ f)
    (x : EuclideanSpace ℝ (Fin n)) :
    euclideanPartial n i (euclideanGradientSq n f) x =
      2 * ∑ k, euclideanPartial n k f x * euclideanPartial n i (euclideanPartial n k f) x := by
  unfold euclideanGradientSq
  rw [euclideanPartial_sum n i _ (fun k =>
    (euclideanPartial_smooth n k f hf).mul (euclideanPartial_smooth n k f hf))]
  simp_rw [euclideanPartial_mul n i _ _ (euclideanPartial_smooth n _ f hf)
    (euclideanPartial_smooth n _ f hf)]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by ring

theorem euclideanPartial_third_diagonal_commute (n : ℕ) (i k : Fin n)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ContDiff ℝ ∞ f)
    (x : EuclideanSpace ℝ (Fin n)) :
    euclideanPartial n i (euclideanPartial n i (euclideanPartial n k f)) x =
      euclideanPartial n k (euclideanPartial n i (euclideanPartial n i f)) x := by
  have h : euclideanPartial n i (euclideanPartial n k f) =
      euclideanPartial n k (euclideanPartial n i f) :=
    funext (euclideanPartial_commute n k i f hf)
  rw [h]
  exact euclideanPartial_commute n k i _ (euclideanPartial_smooth n i f hf) x

theorem euclideanPartial_second_gradientSq (n : ℕ) (i : Fin n)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ContDiff ℝ ∞ f)
    (x : EuclideanSpace ℝ (Fin n)) :
    euclideanPartial n i (euclideanPartial n i (euclideanGradientSq n f)) x =
      2 * ∑ k, ((euclideanPartial n i (euclideanPartial n k f) x) ^ 2 +
        euclideanPartial n k f x *
          euclideanPartial n k (euclideanPartial n i (euclideanPartial n i f)) x) := by
  have h : euclideanPartial n i (euclideanGradientSq n f) =
      fun y => 2 * ∑ k, euclideanPartial n k f y * euclideanPartial n i (euclideanPartial n k f) y :=
    funext (euclideanPartial_gradientSq n i f hf)
  rw [h, euclideanPartial_mul n i _ _ contDiff_const
    (ContDiff.sum fun k _ => (euclideanPartial_smooth n k f hf).mul
      (euclideanPartial_smooth n i _ (euclideanPartial_smooth n k f hf))),
    euclideanPartial_const, mul_zero, add_zero,
    euclideanPartial_sum n i _ (fun k => (euclideanPartial_smooth n k f hf).mul
      (euclideanPartial_smooth n i _ (euclideanPartial_smooth n k f hf)))]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  rw [euclideanPartial_mul n i _ _ (euclideanPartial_smooth n k f hf)
    (euclideanPartial_smooth n i _ (euclideanPartial_smooth n k f hf)),
    euclideanPartial_third_diagonal_commute n i k f hf]
  ring

theorem euclidean_bochner_identity (n : ℕ)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ContDiff ℝ ∞ f)
    (x : EuclideanSpace ℝ (Fin n)) :
    euclideanLaplacian n (euclideanGradientSq n f) x =
      2 * (∑ k, euclideanPartial n k f x * euclideanPartial n k (euclideanLaplacian n f) x) +
      2 * ∑ i, ∑ k, (euclideanPartial n i (euclideanPartial n k f) x) ^ 2 := by
  have hD (k : Fin n) : euclideanPartial n k (euclideanLaplacian n f) x =
      ∑ i, euclideanPartial n k (euclideanPartial n i (euclideanPartial n i f)) x :=
    euclideanPartial_sum n k _ (fun i => euclideanPartial_smooth n i _
      (euclideanPartial_smooth n i f hf)) x
  have hmix : (∑ i, ∑ k, euclideanPartial n k f x *
      euclideanPartial n k (euclideanPartial n i (euclideanPartial n i f)) x) =
      ∑ k, euclideanPartial n k f x * euclideanPartial n k (euclideanLaplacian n f) x := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    rw [hD, Finset.mul_sum]
  change (∑ i, euclideanPartial n i (euclideanPartial n i (euclideanGradientSq n f)) x) = _
  simp_rw [euclideanPartial_second_gradientSq n _ f hf, Finset.sum_add_distrib]
  rw [← Finset.mul_sum, Finset.sum_add_distrib, hmix]
  ring

end AffineFKProof
