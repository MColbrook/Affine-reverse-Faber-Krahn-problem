module

public import AffineFK.H1GaussianDirectionalMoment

/-! Exact scaling of genuine directional L2 pairings and their Gaussian moment. -/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory InnerProductSpace
open scoped RealInnerProductSpace

theorem l2DirectionalPairing_smul (n : ℕ) (c : ℝ)
    (u : EuclideanSpace ℝ (Fin n))
    (g : Lp (EuclideanSpace ℝ (Fin n)) 2
      (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    l2DirectionalPairing n (c • u) g = c • l2DirectionalPairing n u g := by
  apply Lp.ext
  filter_upwards [l2DirectionalPairing_coe n (c • u) g,
    l2DirectionalPairing_coe n u g,
    Lp.coeFn_smul c (l2DirectionalPairing n u g)] with x hc hu hs
  rw [hc, hs]
  simp only [Pi.smul_apply, hu, real_inner_smul_left, smul_eq_mul]

theorem l2DirectionalPairing_scaled_gaussian_second_moment (n : ℕ) (c : ℝ)
    (g : Lp (EuclideanSpace ℝ (Fin n)) 2
      (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    Integrable (fun u => ‖l2DirectionalPairing n (c • u) g‖^2)
      (stdGaussian (EuclideanSpace ℝ (Fin n))) ∧
      (∫ u, ‖l2DirectionalPairing n (c • u) g‖^2
        ∂stdGaussian (EuclideanSpace ℝ (Fin n))) = c^2 * ‖g‖^2 := by
  have heq (u : EuclideanSpace ℝ (Fin n)) :
      ‖l2DirectionalPairing n (c • u) g‖^2 =
        c^2 * ‖l2DirectionalPairing n u g‖^2 := by
    rw [l2DirectionalPairing_smul, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  obtain ⟨hi, hv⟩ := l2DirectionalPairing_gaussian_second_moment n g
  refine ⟨(hi.const_mul (c^2)).congr
    (Filter.Eventually.of_forall fun u => (heq u).symm), ?_⟩
  rw [integral_congr_ae (Filter.Eventually.of_forall heq), integral_const_mul, hv]

end AffineFKProof
