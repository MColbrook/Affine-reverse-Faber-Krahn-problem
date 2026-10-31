module

public import AffineFK.AffineSpectralReduction
public import AffineFK.GaussianPositionEllipsoidMass
public import AffineFK.SymmetricCovarianceSpectralBound

/-!
# The main affine conclusion from the literal Milman geometric input

The geometric hypothesis concerns only volumes of intersections with
actual volume-one origin ellipsoids. The covariance bound, groundstate,
weighted law and spectral conclusions are derived. Existence of these
ellipsoids with one dimension-independent positive intersection constant
remains the separate Milman theorem; this file does not assert it.

The geometric mass and covariance calculations reuse the genuine
GaussianPositionEllipsoidMass and GaussianPositionMassCovariance proofs.
The final unrestricted reduction reuses the actual special-linear,
translation, scaling and symmetric-subbody arguments with their factor four.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory TopologicalSpace Set Metric
open scoped ENNReal

def UniformVolumeOneEllipsoidIntersection (a : ℝ) : Prop :=
  ∀ (n : ℕ), 0 < n → ∀ K : Set (EuclideanSpace ℝ (Fin n)),
    IsCompact K → Convex ℝ K → (interior K).Nonempty →
    (∀ x, -x ∈ K ↔ x ∈ K) → volume K = 1 →
    ∃ A : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n),
      ∃ R : ℝ, 0 < R ∧ volume (A '' closedBall (0 : EuclideanSpace ℝ (Fin n)) R) = 1 ∧
        a ^ n ≤ (volume (K ∩ (A '' closedBall (0 : EuclideanSpace ℝ (Fin n)) R))).toReal

set_option maxHeartbeats 1000000 in
theorem maximal_gaussian_covariance_of_ellipsoid_intersection (n : ℕ) (hn : 0 < n)
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsCompact K) (hconv : Convex ℝ K)
    (heven : ∀ x, -x ∈ K ↔ x ∈ K) (hvol : volume K = 1)
    (hmax : GaussianPositionMaximal n K)
    (A : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (R : ℝ) (hR : 0 < R) (hvolE : volume (A '' closedBall (0 : EuclideanSpace ℝ (Fin n)) R) = 1)
    (a : ℝ) (ha : 0 < a)
    (hinter : a ^ n ≤ (volume (K ∩ (A '' closedBall (0 : EuclideanSpace ℝ (Fin n)) R))).toReal) :
    ∃ α : ℝ, Real.exp (-2 * (1 + |gaussianPositionEllipsoidMassExponent a|) - 1) ≤ α ∧
      α ≤ 1 ∧ ∀ i j : Fin n,
        (∫ x : EuclideanSpace ℝ (Fin n), x i * x j
          ∂ProbabilityTheory.cond (stdGaussian (EuclideanSpace ℝ (Fin n))) K) =
            if i = j then α else 0 := by
  obtain ⟨_hB, S, hmassS⟩ := gaussianPosition_ellipsoid_intersection_mass_positive_exponent
    n hn K hK A R hR hvolE a ha hinter
  have hmass : Real.exp (-(1 + |gaussianPositionEllipsoidMassExponent a|) * (n : ℝ)) ≤
      (stdGaussian (EuclideanSpace ℝ (Fin n))).real K :=
    hmassS.trans (ENNReal.toReal_mono (measure_ne_top _ _) (hmax S))
  have hKpos : stdGaussian (EuclideanSpace ℝ (Fin n)) K ≠ 0 :=
    gaussianPosition_gaussian_pos_of_volume_pos n K (by rw [hvol]; exact zero_lt_one)
  let : IsProbabilityMeasure (ProbabilityTheory.cond
    (stdGaussian (EuclideanSpace ℝ (Fin n))) K) := cond_isProbabilityMeasure hKpos
  obtain ⟨α,hα,hmean,hcov⟩ := gaussianPosition_cond_covariance n hn K hK hKpos heven hmax
  have hraw (i j : Fin n) :
      (∫ x : EuclideanSpace ℝ (Fin n), x i * x j
        ∂ProbabilityTheory.cond (stdGaussian (EuclideanSpace ℝ (Fin n))) K) =
          if i = j then α else 0 := by
    have h := hcov i j
    rw [covariance_eq_sub (gaussianPosition_cond_coordinate_memLp n K hKpos i)
      (gaussianPosition_cond_coordinate_memLp n K hKpos j), hmean i, hmean j,
      zero_mul, sub_zero] at h
    exact h
  have hsecond (i : Fin n) :
      (∫ x : EuclideanSpace ℝ (Fin n), x i * x i
        ∂ProbabilityTheory.cond (stdGaussian (EuclideanSpace ℝ (Fin n))) K) = α := by
    simpa using hraw i i
  let i : Fin n := ⟨0,hn⟩
  have hupper : α ≤ 1 := by
    rw [← hsecond i]
    exact gaussianPosition_cond_second_moment_le_one n K hK.measurableSet hconv hKpos heven i
  exact ⟨α, gaussianPosition_covariance_lower_of_mass_bound n hn K hK hKpos α hα hsecond
    (1 + |gaussianPositionEllipsoidMassExponent a|) hmass, hupper, hraw⟩

theorem symmetric_gaussian_spectral_bound_of_ellipsoid_intersections
    (a : ℝ) (ha : 0 < a) (hEllipsoid : UniformVolumeOneEllipsoidIntersection a) :
    ∃ C : ℝ, 0 < C ∧ UniformSymmetricGaussianDirichletBound C := by
  let c := Real.exp (-2 * (1 + |gaussianPositionEllipsoidMassExponent a|) - 1)
  have hc : 0 < c := Real.exp_pos _
  have hcOne : c ≤ 1 := Real.exp_le_one_iff.mpr
    (by linarith [abs_nonneg (gaussianPositionEllipsoidMassExponent a)])
  obtain ⟨C,hC,hBound⟩ := uniform_symmetric_body_spectral_bound_of_covariance c hc hcOne
  refine ⟨C,hC,?_⟩
  intro n hn K hK hconv hinterior heven hvol hmax
  obtain ⟨A,R,hR,hvolE,hinter⟩ := hEllipsoid n hn K hK hconv hinterior heven hvol
  obtain ⟨α,hcα,hαOne,hcov⟩ := maximal_gaussian_covariance_of_ellipsoid_intersection
    n hn K hK hconv heven hvol hmax A R hR hvolE a ha hinter
  exact hBound n hn K hK hconv hinterior heven α hcα hαOne hcov

theorem affine_reverse_faber_krahn_of_ellipsoid_intersections
    (hEllipsoid : ∃ a : ℝ, 0 < a ∧ UniformVolumeOneEllipsoidIntersection a) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ), 0 < n →
      ∀ K : Set (EuclideanSpace ℝ (Fin n)), IsCompact K → Convex ℝ K →
      (interior K).Nonempty → ∃ S : Matrix.SpecialLinearGroup (Fin n) ℝ,
        dirichletEigenvalue n ⟨interior (gaussianPositionSLLinear n S '' K),isOpen_interior⟩ ≠ ∞ ∧
        (dirichletEigenvalue n ⟨interior (gaussianPositionSLLinear n S '' K),isOpen_interior⟩).toReal *
          (volume K).toReal ^ ((2 : ℝ) / (n : ℝ)) ≤ C * (n : ℝ) := by
  obtain ⟨a,ha,hEllipsoid⟩ := hEllipsoid
  exact affine_reverse_faber_krahn_conditional
    (symmetric_gaussian_spectral_bound_of_ellipsoid_intersections a ha hEllipsoid)

end AffineFKProof
