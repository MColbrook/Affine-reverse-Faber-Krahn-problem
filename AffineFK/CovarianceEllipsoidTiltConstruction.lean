module

public import AffineFK.CovarianceEllipsoidTiltCovariance
public import AffineFK.GaussianPositionIntersectionProfile
public import AffineFK.GaussianPositionEllipsoidNormalization

/-!
# A literal origin ellipsoid from an actual tilted Jacobian bound

The tilt, its mean and its positive definite covariance are constructed.
A supplied bound on its genuine mean-map Jacobian determinant gives the
translated covariance ellipsoid. Central maximality of intersection for
the original even convex body removes its translation. The previously
proved volume normalization gives the literal volume-one origin ellipse.
The existence of the small-Jacobian point remains a separate obligation.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory Matrix Set Metric
open scoped ENNReal Pointwise MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace

def covarianceEllipsoidTiltIntersectionBase (b : ℝ) : ℝ :=
  (1/(2*Real.exp 1)) / max (Real.sqrt b⁻¹*covarianceEllipsoidBallVolumeBase) 1

theorem covarianceEllipsoidTiltIntersectionBase_pos (b : ℝ) :
    0 < covarianceEllipsoidTiltIntersectionBase b :=
  div_pos (by positivity) (lt_of_lt_of_le zero_lt_one (le_max_right _ _))

set_option maxHeartbeats 1000000 in
theorem exists_tilt_translated_covariance_ellipsoid (n : ℕ) (hn : 0 < n)
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsCompact K) (hvolume : volume K = 1)
    (heven : ∀ x, -x ∈ K ↔ x ∈ K) (y : EuclideanSpace ℝ (Fin n))
    (hy : y ∈ (n : ℝ) • (innerₗ (EuclideanSpace ℝ (Fin n))).polar K)
    (b : ℝ) (hb : 0 < b)
    (hdet : LinearMap.det ((fderiv ℝ (gradient (gaussianPositionLogLaplace n K)) y) :
      EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)) ≤ (b⁻¹)^n) :
    ∃ A : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n),
      (∀ z, A z = Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)
        (CFC.sqrt (covarianceEllipsoidTiltMatrix n K y)) z) ∧
      (1/2 : ℝ≥0∞) ≤ gaussianPositionTiltLaw n K y
        ((fun x => gradient (gaussianPositionLogLaplace n K) y+x) ''
          (A '' closedBall (0 : EuclideanSpace ℝ (Fin n)) (Real.sqrt (2*(n : ℝ))))) ∧
      (1/(2*Real.exp 1))^n ≤ (volume (K ∩
        ((fun x => gradient (gaussianPositionLogLaplace n K) y+x) ''
          (A '' closedBall (0 : EuclideanSpace ℝ (Fin n)) (Real.sqrt (2*(n : ℝ))))))).toReal ∧
      (volume (A '' closedBall (0 : EuclideanSpace ℝ (Fin n)) (Real.sqrt (2*(n : ℝ))))).toReal ≤
        (Real.sqrt b⁻¹*covarianceEllipsoidBallVolumeBase)^n := by
  have hvol : 0 < volume K := by rw [hvolume]; exact zero_lt_one
  let μ := gaussianPositionTiltLaw n K y
  let m := gradient (gaussianPositionLogLaplace n K) y
  let : IsProbabilityMeasure μ := gaussianPositionTiltLaw_isProbabilityMeasure n K hK hvol y
  have hX := covarianceEllipsoidTilt_identity_memLp n K hK hvol y
  have hM : (covarianceEllipsoidMomentMatrix n μ m).PosDef :=
    covarianceEllipsoidTiltMatrix_posDef n K hK hvol y
  let A := (covarianceWhiteningLinear n (covarianceEllipsoidMomentMatrix n μ m) hM).symm
  let F := A '' closedBall (0 : EuclideanSpace ℝ (Fin n)) (Real.sqrt (2*(n : ℝ)))
  let E := (fun x => m+x) '' F
  have hE : E = covarianceEllipsoidSet n μ m hM := by
    dsimp only [E,F]
    rw [image_image]
    exact (covarianceEllipsoidSet_inverse_image n μ m hM).symm
  have hLaw : μ = densityMeasure n (gaussianPositionTiltDensity n K y) :=
    (gaussianPositionTiltDensity_law n K hK.measurableSet y).symm
  have hsupport : ∀ x, x ∉ K → gaussianPositionTiltDensity n K y x = 0 := by
    intro x hx
    simp only [gaussianPositionTiltDensity,indicator_of_notMem hx]
  have hbound : ∀ x ∈ K, gaussianPositionTiltDensity n K y x ≤ Real.exp (n : ℝ) :=
    fun x hx => (gaussianPositionTiltDensity_dilated_polar_bounds n K hK hvolume heven y hy).2.2 x hx |>.2
  have hdetM : (covarianceEllipsoidMomentMatrix n μ m).det ≤ (b⁻¹)^n := by
    change (covarianceEllipsoidTiltMatrix n K y).det ≤ (b⁻¹)^n
    rw [covarianceEllipsoidTiltMatrix_det_derivative n K hK hvol y]
    exact hdet
  have hEvolume : (volume E).toReal ≤ (Real.sqrt b⁻¹*covarianceEllipsoidBallVolumeBase)^n := by
    rw [hE]
    exact covarianceEllipsoidSet_volume_bound n μ m hM b⁻¹ (inv_nonneg.mpr hb.le) hdetM
  have hFvolume : (volume F).toReal ≤ (Real.sqrt b⁻¹*covarianceEllipsoidBallVolumeBase)^n := by
    rwa [covarianceEllipsoid_translate_volume n m F] at hEvolume
  refine ⟨A,(fun z => covarianceEllipsoid_inverse_sqrt_apply n _ hM z),?_,?_,hFvolume⟩
  · change (1/2 : ℝ≥0∞) ≤ μ E
    rw [hE]
    exact covarianceEllipsoidSet_mass n hn μ hX m hM
  · change (1/(2*Real.exp 1))^n ≤ (volume (K ∩ E)).toReal
    rw [hE]
    exact covarianceEllipsoid_intersection_lower n hn μ hX m hM K hK
      (gaussianPositionTiltDensity n K y) hLaw hsupport hbound

set_option maxHeartbeats 1000000 in
theorem exists_tilt_origin_covariance_ellipsoid (n : ℕ) (hn : 0 < n)
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsCompact K) (hconv : Convex ℝ K)
    (hvolume : volume K = 1) (heven : ∀ x, -x ∈ K ↔ x ∈ K)
    (y : EuclideanSpace ℝ (Fin n))
    (hy : y ∈ (n : ℝ) • (innerₗ (EuclideanSpace ℝ (Fin n))).polar K)
    (b : ℝ) (hb : 0 < b)
    (hdet : LinearMap.det ((fderiv ℝ (gradient (gaussianPositionLogLaplace n K)) y) :
      EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)) ≤ (b⁻¹)^n) :
    ∃ A : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n),
      (1/(2*Real.exp 1))^n ≤
        (volume (K ∩ (A '' closedBall (0 : EuclideanSpace ℝ (Fin n)) (Real.sqrt (2*(n : ℝ)))))).toReal ∧
      (volume (A '' closedBall (0 : EuclideanSpace ℝ (Fin n)) (Real.sqrt (2*(n : ℝ))))).toReal ≤
        (Real.sqrt b⁻¹*covarianceEllipsoidBallVolumeBase)^n := by
  obtain ⟨A,_hRoot,_hMass,hinter,hvol⟩ :=
    exists_tilt_translated_covariance_ellipsoid n hn K hK hvolume heven y hy b hb hdet
  let F := A '' closedBall (0 : EuclideanSpace ℝ (Fin n)) (Real.sqrt (2*(n : ℝ)))
  let m := gradient (gaussianPositionLogLaplace n K) y
  have hFc : IsCompact F := (isCompact_closedBall _ _).image A.continuous
  have hFconv : Convex ℝ F := (convex_closedBall _ _).linear_image A.toLinearMap
  have hFeven : ∀ x, -x ∈ F ↔ x ∈ F := by
    intro x
    constructor
    · rintro ⟨z,hz,hzx⟩
      refine ⟨-z,?_,?_⟩
      · simpa only [mem_closedBall,dist_zero_right,norm_neg] using hz
      · rw [map_neg,hzx,neg_neg]
    · rintro ⟨z,hz,rfl⟩
      refine ⟨-z,?_,A.map_neg z⟩
      simpa only [mem_closedBall,dist_zero_right,norm_neg] using hz
  have hcentral : volume (K ∩ ((fun x => m+x) '' F)) ≤ volume (K ∩ F) := by
    have h := gaussianPositionIntersectionProfile_le_zero n K F hK.measurableSet hFc.measurableSet
      hconv hFconv heven hFeven m
    change volume (K ∩ {x | x-m ∈ F}) ≤ volume (K ∩ F) at h
    rwa [gaussianPosition_intersection_translate_image n K F m] at h
  have hreal := ENNReal.toReal_mono (hK.inter_right hFc.isClosed).measure_ne_top hcentral
  exact ⟨A,hinter.trans hreal,hvol⟩

set_option maxHeartbeats 1000000 in
theorem exists_tilt_volume_one_origin_ellipsoid (n : ℕ) (hn : 0 < n)
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsCompact K) (hconv : Convex ℝ K)
    (hinterior : (interior K).Nonempty) (hvolume : volume K = 1)
    (heven : ∀ x, -x ∈ K ↔ x ∈ K) (y : EuclideanSpace ℝ (Fin n))
    (hy : y ∈ (n : ℝ) • (innerₗ (EuclideanSpace ℝ (Fin n))).polar K)
    (b : ℝ) (hb : 0 < b)
    (hdet : LinearMap.det ((fderiv ℝ (gradient (gaussianPositionLogLaplace n K)) y) :
      EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)) ≤ (b⁻¹)^n) :
    ∃ A : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n),
      volume (A '' closedBall (0 : EuclideanSpace ℝ (Fin n)) (Real.sqrt (2*(n : ℝ)))) = 1 ∧
      (covarianceEllipsoidTiltIntersectionBase b)^n ≤
        (volume (K ∩ (A '' closedBall (0 : EuclideanSpace ℝ (Fin n)) (Real.sqrt (2*(n : ℝ)))))).toReal := by
  obtain ⟨A,hinter,hvol⟩ := exists_tilt_origin_covariance_ellipsoid n hn K hK hconv hvolume heven y hy b hb hdet
  let a := (1/(2*Real.exp 1) : ℝ)
  let B := Real.sqrt b⁻¹*covarianceEllipsoidBallVolumeBase
  let R := Real.sqrt (2*(n : ℝ))
  have ha : 0 < a := by positivity
  have hB : 0 < B := covarianceEllipsoid_volume_base_pos b⁻¹ (inv_pos.mpr hb)
  have hR : 0 < R := Real.sqrt_pos.mpr (mul_pos (by norm_num) (by exact_mod_cast hn))
  have hFc : IsCompact (A '' closedBall (0 : EuclideanSpace ℝ (Fin n)) R) :=
    (isCompact_closedBall _ _).image A.continuous
  have hVol : volume (A '' closedBall (0 : EuclideanSpace ℝ (Fin n)) R) ≤ ENNReal.ofReal (B^n) :=
    (ENNReal.toReal_le_toReal hFc.measure_ne_top ENNReal.ofReal_ne_top).mp
      (by simpa only [ENNReal.toReal_ofReal (pow_nonneg hB.le n)] using hvol)
  have hInt : ENNReal.ofReal (a^n) ≤ volume (K ∩ (A '' closedBall (0 : EuclideanSpace ℝ (Fin n)) R)) :=
    (ENNReal.toReal_le_toReal ENNReal.ofReal_ne_top (hK.inter_right hFc.isClosed).measure_ne_top).mp
      (by simpa only [ENNReal.toReal_ofReal (pow_nonneg ha.le n)] using hinter)
  obtain ⟨A',hNorm,hLower⟩ := gaussianPosition_normalize_origin_ellipsoid n hn K hconv hinterior heven
    A R hR a B ha hB hVol hInt
  have hfinite : volume (K ∩ (A' '' closedBall (0 : EuclideanSpace ℝ (Fin n)) R)) ≠ ∞ :=
    ne_top_of_le_ne_top (by rw [hNorm]; exact ENNReal.one_ne_top) (measure_mono inter_subset_right)
  have hReal := ENNReal.toReal_mono hfinite hLower
  refine ⟨A',hNorm,?_⟩
  have hFinal : (a/max B 1)^n ≤
      (volume (K ∩ (A' '' closedBall (0 : EuclideanSpace ℝ (Fin n)) R))).toReal := by
    simpa only [ENNReal.toReal_ofReal (pow_nonneg
      (div_nonneg ha.le (le_trans zero_le_one (le_max_right B 1))) n)] using hReal
  simpa only [covarianceEllipsoidTiltIntersectionBase,a,B,R] using hFinal

end AffineFKProof
