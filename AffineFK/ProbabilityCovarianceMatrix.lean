module

public import AffineFK.PoincareCovarianceBound
public import Mathlib.Analysis.Matrix.Order

/-!
# Actual finite second-moment matrices and their Poincare upper bound

All entries are genuine coordinate integrals of the original law. The
quadratic-form identity is proved by finite L1 summation, so positivity
and the unit Poincare covariance bound are conclusions.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace

def probabilitySecondMomentMatrix (n : ℕ) (ν : Measure (EuclideanSpace ℝ (Fin n))) :
    Matrix (Fin n) (Fin n) ℝ := fun i j => ∫ x, x i * x j ∂ν

theorem probabilitySecondMomentMatrix_quadratic (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n)))
    (hX : MemLp (id : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) 2 ν)
    (v : Fin n → ℝ) :
    v ⬝ᵥ probabilitySecondMomentMatrix n ν *ᵥ v =
      ∫ x : EuclideanSpace ℝ (Fin n), (∑ i : Fin n, v i * x i) ^ 2 ∂ν := by
  have hi (i j : Fin n) : Integrable
      (fun x : EuclideanSpace ℝ (Fin n) => v i * (x i * x j) * v j) ν :=
    (((hX.eval_piLp i).integrable_mul (hX.eval_piLp j)).const_mul (v i)).mul_const (v j)
  have hsum : (∫ x : EuclideanSpace ℝ (Fin n), ∑ i : Fin n, ∑ j : Fin n,
      v i * (x i * x j) * v j ∂ν) =
      ∑ i : Fin n, ∑ j : Fin n, v i * probabilitySecondMomentMatrix n ν i j * v j := by
    calc
      _ = ∑ i : Fin n, ∫ x : EuclideanSpace ℝ (Fin n), ∑ j : Fin n,
          v i * (x i * x j) * v j ∂ν :=
        integral_finsetSum Finset.univ (fun i _ => integrable_finsetSum Finset.univ (fun j _ => hi i j))
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i _
        calc
          _ = ∑ j : Fin n, ∫ x : EuclideanSpace ℝ (Fin n), v i * (x i * x j) * v j ∂ν :=
            integral_finsetSum Finset.univ (fun j _ => hi i j)
          _ = _ := by
            apply Finset.sum_congr rfl
            intro j _
            rw [integral_mul_const, integral_const_mul]
            rfl
  calc
    _ = ∑ i : Fin n, ∑ j : Fin n, v i * probabilitySecondMomentMatrix n ν i j * v j := by
      simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]
    _ = ∫ x : EuclideanSpace ℝ (Fin n), ∑ i : Fin n, ∑ j : Fin n,
        v i * (x i * x j) * v j ∂ν := hsum.symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with x
      simp only [pow_two, Finset.sum_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring

theorem probabilitySecondMomentMatrix_posSemidef (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n)))
    (hX : MemLp (id : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) 2 ν) :
    (probabilitySecondMomentMatrix n ν).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · ext i j
    simp only [probabilitySecondMomentMatrix, Matrix.conjTranspose_apply, star_trivial]
    congr 1
    funext x
    exact mul_comm _ _
  · intro v
    have hv : star v = v := by funext i; exact star_trivial _
    rw [hv]
    rw [probabilitySecondMomentMatrix_quadratic n ν hX v]
    exact integral_nonneg fun x => sq_nonneg _

theorem probabilitySecondMomentMatrix_le_one_of_poincare (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (hX : MemLp (id : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) 2 ν)
    (hmean : ∀ i : Fin n, (∫ x : EuclideanSpace ℝ (Fin n), x i ∂ν) = 0)
    (hP : poincareConstant n ν ≤ 1) :
    (1 - probabilitySecondMomentMatrix n ν).PosSemidef := by
  have hC := probabilitySecondMomentMatrix_posSemidef n ν hX
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · change (1 - probabilitySecondMomentMatrix n ν)ᴴ = 1 - probabilitySecondMomentMatrix n ν
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hC.isHermitian]
  · intro v
    let w : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 v
    have hinner (x : EuclideanSpace ℝ (Fin n)) : ⟪w, x⟫ = ∑ i : Fin n, v i * x i := by
      simp only [EuclideanSpace.inner_eq_star_dotProduct, w, WithLp.ofLp_toLp, star_trivial,
        dotProduct, mul_comm]
    have hmeanw : (∫ x : EuclideanSpace ℝ (Fin n), ⟪w, x⟫ ∂ν) = 0 := by
      simp_rw [hinner]
      calc
        _ = ∑ i : Fin n, ∫ x : EuclideanSpace ℝ (Fin n), v i * x i ∂ν :=
          integral_finsetSum Finset.univ (fun i _ => by
            simpa only [id_eq] using ((hX.eval_piLp i).integrable (by norm_num)).const_mul (v i))
        _ = 0 := by simp only [integral_const_mul, hmean, mul_zero, Finset.sum_const_zero]
    have hsecond := (memLp_two_iff_integrable_sq_norm aestronglyMeasurable_id).mp hX
    have hbound := poincare_linear_variance_bound n ν hsecond 1 hP w
    rw [hmeanw] at hbound
    simp only [sub_zero, NNReal.coe_one, one_mul] at hbound
    simp_rw [hinner] at hbound
    have hnorm : ‖w‖ ^ 2 = v ⬝ᵥ v := by
      change ‖WithLp.toLp 2 v‖ ^ 2 = v ⬝ᵥ v
      rw [EuclideanSpace.real_norm_sq_eq]
      simp only [WithLp.ofLp_toLp, dotProduct, pow_two]
    rw [hnorm] at hbound
    simp only [Matrix.sub_mulVec, Matrix.one_mulVec, dotProduct_sub]
    have hv : star v = v := by funext i; exact star_trivial _
    rw [hv]
    rw [probabilitySecondMomentMatrix_quadratic n ν hX v]
    linarith

end AffineFKProof
