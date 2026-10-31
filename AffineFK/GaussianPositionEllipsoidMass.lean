module

public import AffineFK.GaussianPositionEllipsoidMap
public import AffineFK.GaussianPositionBallMass

/-!
# The ellipsoid-intersection consequence needed for Gaussian position

The ellipsoid is literally A applied to a positive-radius closed Euclidean
ball. Its volume is one. An actual lower intersection volume supplies the
proved SL image and Gaussian-mass bound. Milman's theorem asserting the
existence of such an ellipsoid uniformly in the dimension is not assumed
as a covariance or Gaussian-mass conclusion and is not proved here.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory Set Metric
open scoped ENNReal

theorem gaussianPosition_ellipsoid_intersection_gaussian_mass (n : ℕ) (hn : 0 < n)
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsCompact K)
    (A : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (R : ℝ) (hR : 0 < R)
    (hvol : volume (A '' closedBall (0 : EuclideanSpace ℝ (Fin n)) R) = 1)
    (c : ℝ) (hc : 0 < c)
    (hinter : ENNReal.ofReal (c ^ n) ≤
      volume (K ∩ (A '' closedBall (0 : EuclideanSpace ℝ (Fin n)) R))) :
    ∃ S : Matrix.SpecialLinearGroup (Fin n) ℝ, ∃ r : ℝ,
      0 < r ∧
      gaussianPositionSLLinear n S '' (A '' closedBall (0 : EuclideanSpace ℝ (Fin n)) R) =
        closedBall (0 : EuclideanSpace ℝ (Fin n)) r ∧
      volume (closedBall (0 : EuclideanSpace ℝ (Fin n)) r) = 1 ∧
      r ^ 2 ≤ (n : ℝ) / 4 ∧
      Real.exp (-gaussianPositionEllipsoidMassExponent c * (n : ℝ)) ≤
        (stdGaussian (EuclideanSpace ℝ (Fin n))).real (gaussianPositionSLLinear n S '' K) := by
  obtain ⟨S, r, hr, hSE, hballvol, hrsq⟩ :=
    gaussianPosition_ellipsoid_to_volume_one_ball n hn A R hR hvol
  let B := gaussianPositionSLLinear n S
  let Eset := A '' closedBall (0 : EuclideanSpace ℝ (Fin n)) R
  have hset : B '' (K ∩ Eset) = B '' K ∩ B '' Eset := by
    ext x
    constructor
    · rintro ⟨y, ⟨hyK, hyE⟩, rfl⟩
      exact ⟨⟨y, hyK, rfl⟩, ⟨y, hyE, rfl⟩⟩
    · rintro ⟨⟨y, hyK, hy⟩, ⟨z, hzE, hz⟩⟩
      have heq : y = z := B.injective (hy.trans hz.symm)
      subst z
      exact ⟨y, ⟨hyK, hzE⟩, hy⟩
  have hintersection_volume : volume (B '' K ∩ closedBall 0 r) = volume (K ∩ Eset) := by
    rw [← hSE, ← hset, Measure.addHaar_image_continuousLinearEquiv, gaussianPositionSLLinear_det]
    simp
  have hnew : ENNReal.ofReal (c ^ n) ≤ volume (B '' K ∩ closedBall 0 r) := by
    rw [hintersection_volume]
    exact hinter
  exact ⟨S, r, hr, hSE, hballvol, hrsq,
    gaussianPosition_mass_lower_of_ball_intersection n (B '' K) (hK.image B.continuous)
      r hr.le hrsq c hc hnew⟩

theorem gaussianPosition_ellipsoid_intersection_gaussian_mass_real (n : ℕ) (hn : 0 < n)
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsCompact K)
    (A : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (R : ℝ) (hR : 0 < R)
    (hvol : volume (A '' closedBall (0 : EuclideanSpace ℝ (Fin n)) R) = 1)
    (c : ℝ) (hc : 0 < c)
    (hinter : c ^ n ≤ (volume (K ∩ (A '' closedBall (0 : EuclideanSpace ℝ (Fin n)) R))).toReal) :
    ∃ S : Matrix.SpecialLinearGroup (Fin n) ℝ,
      Real.exp (-gaussianPositionEllipsoidMassExponent c * (n : ℝ)) ≤
        (stdGaussian (EuclideanSpace ℝ (Fin n))).real (gaussianPositionSLLinear n S '' K) := by
  have hfinite : volume (K ∩ (A '' closedBall (0 : EuclideanSpace ℝ (Fin n)) R)) ≠ ∞ :=
    ne_top_of_le_ne_top (by rw [hvol]; exact ENNReal.one_ne_top) (measure_mono inter_subset_right)
  have hENN : ENNReal.ofReal (c ^ n) ≤ volume (K ∩ (A '' closedBall 0 R)) :=
    (ENNReal.toReal_le_toReal ENNReal.ofReal_ne_top hfinite).mp (by
      simpa only [ENNReal.toReal_ofReal (pow_nonneg hc.le n)] using hinter)
  obtain ⟨S, _r, _hr, _himage, _hvolume, _hrsq, hmass⟩ :=
    gaussianPosition_ellipsoid_intersection_gaussian_mass n hn K hK A R hR hvol c hc hENN
  exact ⟨S, hmass⟩

theorem gaussianPosition_ellipsoid_intersection_mass_positive_exponent (n : ℕ) (hn : 0 < n)
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsCompact K)
    (A : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (R : ℝ) (hR : 0 < R)
    (hvol : volume (A '' closedBall (0 : EuclideanSpace ℝ (Fin n)) R) = 1)
    (c : ℝ) (hc : 0 < c)
    (hinter : c ^ n ≤ (volume (K ∩ (A '' closedBall (0 : EuclideanSpace ℝ (Fin n)) R))).toReal) :
    0 < 1 + |gaussianPositionEllipsoidMassExponent c| ∧
      ∃ S : Matrix.SpecialLinearGroup (Fin n) ℝ,
        Real.exp (-(1 + |gaussianPositionEllipsoidMassExponent c|) * (n : ℝ)) ≤
          (stdGaussian (EuclideanSpace ℝ (Fin n))).real (gaussianPositionSLLinear n S '' K) := by
  obtain ⟨S, hmass⟩ := gaussianPosition_ellipsoid_intersection_gaussian_mass_real
    n hn K hK A R hR hvol c hc hinter
  refine ⟨by positivity, S, ?_⟩
  apply le_trans (Real.exp_le_exp.mpr ?_) hmass
  have hC := le_abs_self (gaussianPositionEllipsoidMassExponent c)
  nlinarith [show (0 : ℝ) ≤ (n : ℝ) from Nat.cast_nonneg n]

end AffineFKProof
