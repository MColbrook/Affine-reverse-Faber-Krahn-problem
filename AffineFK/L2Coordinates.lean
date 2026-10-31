module

public import AffineFK.SobolevCoordinates

/-!
# Coordinates of actual Euclidean-valued L2 functions

The continuous coordinate functionals act on genuine L2 spaces. Their means
are the inner products with constant basis vectors, and Parseval's identity
holds after integration. These facts provide the scalar sources for the
second Poisson equations.

Reused Mathlib results include continuous-linear-map composition on Lp,
Bochner finite sums, and Parseval's identity for orthonormal bases.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory InnerProductSpace
open scoped RealInnerProductSpace

def l2Coordinate
    {X : Type*} [MeasurableSpace X] (n : ℕ) (ν : Measure X)
    (j : Fin n) : Lp (EuclideanSpace ℝ (Fin n)) 2 ν →L[ℝ] Lp ℝ 2 ν :=
  (coordinateFunctional n j).compLpL 2 ν

theorem l2Coordinate_coe
    {X : Type*} [MeasurableSpace X] (n : ℕ) (ν : Measure X)
    (j : Fin n) (g : Lp (EuclideanSpace ℝ (Fin n)) 2 ν) :
    l2Coordinate n ν j g =ᵐ[ν] fun x => (g x) j := by
  filter_upwards [(coordinateFunctional n j).coeFn_compLp g] with x hx
  exact hx.trans (coordinateFunctional_apply n j (g x))

theorem l2Coordinate_mean
    {X : Type*} [MeasurableSpace X] (n : ℕ) (ν : Measure X) [IsFiniteMeasure ν]
    (j : Fin n) (g : Lp (EuclideanSpace ℝ (Fin n)) 2 ν) :
    l2Mean ν (l2Coordinate n ν j g) =
      ⟪g, Lp.const 2 ν (EuclideanSpace.basisFun (Fin n) ℝ j)⟫ := by
  rw [l2Mean_apply, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [l2Coordinate_coe n ν j g,
    Lp.coeFn_const 2 ν (EuclideanSpace.basisFun (Fin n) ℝ j)] with x hx he
  rw [hx, he]
  change (g x) j = ⟪g x, EuclideanSpace.basisFun (Fin n) ℝ j⟫
  rw [real_inner_comm]
  exact (EuclideanSpace.basisFun_inner (Fin n) ℝ (g x) j).symm

theorem l2_const_inner
    {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (ν : Measure X) [IsProbabilityMeasure ν] (v w : E) :
    ⟪Lp.const 2 ν v, Lp.const 2 ν w⟫ = ⟪v, w⟫ := by
  rw [L2.inner_def]
  calc
    _ = ∫ _x, ⟪v, w⟫ ∂ν := by
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_const 2 ν v, Lp.coeFn_const 2 ν w] with x hv hw
      rw [hv, hw]
      rfl
    _ = _ := by simp

/-- Parseval's identity for genuine L2 coordinate classes, with all finite
sum/integral exchanges justified by their L2 second moments. -/
theorem l2Coordinate_norm_sq_sum
    {X : Type*} [MeasurableSpace X] (n : ℕ) (ν : Measure X)
    (g : Lp (EuclideanSpace ℝ (Fin n)) 2 ν) :
    (∑ j : Fin n, ‖l2Coordinate n ν j g‖ ^ 2) = ‖g‖ ^ 2 := by
  have hint (j : Fin n) : Integrable (fun x => ‖(l2Coordinate n ν j g) x‖ ^ 2) ν :=
    (memLp_two_iff_integrable_sq_norm (Lp.memLp (l2Coordinate n ν j g)).aestronglyMeasurable).mp
      (Lp.memLp (l2Coordinate n ν j g))
  simp_rw [l2_norm_sq_integral]
  rw [← integral_finsetSum Finset.univ (fun j _hj => hint j)]
  apply integral_congr_ae
  have hall : ∀ᵐ x ∂ν, ∀ j : Fin n, (l2Coordinate n ν j g) x = (g x) j :=
    (ae_all_iff).mpr fun j => l2Coordinate_coe n ν j g
  filter_upwards [hall] with x hx
  simp_rw [hx, Real.norm_eq_abs, sq_abs]
  have hparseval := (EuclideanSpace.basisFun (Fin n) ℝ).sum_sq_inner_right (g x)
  simpa only [EuclideanSpace.basisFun_inner] using hparseval

end AffineFKProof
