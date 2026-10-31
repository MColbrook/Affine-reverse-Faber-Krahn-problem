module

public import AffineFK.GaussianPositionIntegral
public import AffineFK.GaussianPositionCurves
public import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!
# Actual special-linear maximality implies Gaussian moment stationarity

The maximality premise below is the literal maximization problem for the
actual Gaussian measure of special-linear images. It is not a covariance
or stationarity premise. Existence of a maximizer and the universal
M-ellipsoid lower bound remain separate geometric assertions.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology RealInnerProductSpace

def GaussianPositionMaximal (n : ℕ) (K : Set (EuclideanSpace ℝ (Fin n))) : Prop :=
  ∀ S : Matrix.SpecialLinearGroup (Fin n) ℝ,
    stdGaussian (EuclideanSpace ℝ (Fin n)) (gaussianPositionSLLinear n S '' K) ≤
      stdGaussian (EuclideanSpace ℝ (Fin n)) K

theorem gaussianPosition_maximal_stationarity (n : ℕ)
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsCompact K)
    (hmax : GaussianPositionMaximal n K)
    (S : ℝ → Matrix.SpecialLinearGroup (Fin n) ℝ)
    (B : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hS : HasDerivAt (fun t => Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)
      (S t : Matrix (Fin n) (Fin n) ℝ)) B 0)
    (hzero : Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)
      (S 0 : Matrix (Fin n) (Fin n) ℝ) = ContinuousLinearMap.id ℝ _) :
    (∫ x in K, ⟪B x, x⟫ * standardGaussianDensity n x) = 0 := by
  let L : ℝ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
    fun t => Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (S t : Matrix (Fin n) (Fin n) ℝ)
  have hvar := gaussianPositionIntegral_first_variation n K hK L B hS hzero
  have hfun : (fun x => gaussianPositionSLLinear n (S 0) x) = id := by
    funext x
    rw [gaussianPositionSLLinear_apply, hzero, ContinuousLinearMap.id_apply]
    rfl
  have himage : gaussianPositionSLLinear n (S 0) '' K = K := by
    change (fun x => gaussianPositionSLLinear n (S 0) x) '' K = K
    rw [hfun, image_id]
  have htop : ∀ t : ℝ, gaussianPositionIntegral n K (L t) ≤ gaussianPositionIntegral n K (L 0) := by
    intro t
    change (∫ x in K, standardGaussianDensity n (L t x)) ≤
      (∫ x in K, standardGaussianDensity n (L 0 x))
    rw [← gaussianPosition_gaussian_measure_integral n K hK (S t),
      ← gaussianPosition_gaussian_measure_integral n K hK (S 0), himage]
    exact ENNReal.toReal_mono (measure_ne_top _ _) (hmax (S t))
  have hextr : IsLocalMax (fun t => gaussianPositionIntegral n K (L t)) 0 :=
    Eventually.of_forall htop
  exact neg_eq_zero.mp (hextr.hasDerivAt_eq_zero hvar)

theorem gaussianPosition_maximal_offDiagonal (n : ℕ)
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsCompact K)
    (hmax : GaussianPositionMaximal n K) (i j : Fin n) (hij : i ≠ j) :
    (∫ x in K, x i * x j * standardGaussianDensity n x) = 0 := by
  have h := gaussianPosition_maximal_stationarity n K hK hmax
    (gaussianPositionShear n i j hij) _ (gaussianPositionShear_hasDerivAt n i j hij)
    (gaussianPositionShear_zero n i j hij)
  convert h using 1
  apply setIntegral_congr_fun hK.measurableSet
  intro x _
  dsimp only
  rw [real_inner_comm, Matrix.inner_toEuclideanCLM]
  simp [Matrix.single_mulVec_eq, dotProduct_single, mul_comm]

theorem gaussianPosition_maximal_diagonal_variation (n : ℕ)
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsCompact K)
    (hmax : GaussianPositionMaximal n K) (d : Fin n → ℝ) (hd : ∑ i, d i = 0) :
    (∫ x in K, (∑ i, d i * (x i) ^ 2) * standardGaussianDensity n x) = 0 := by
  have h := gaussianPosition_maximal_stationarity n K hK hmax
    (gaussianPositionDiagonal n d hd) _ (gaussianPositionDiagonal_hasDerivAt n d hd)
    (gaussianPositionDiagonal_zero n d hd)
  convert h using 1
  apply setIntegral_congr_fun hK.measurableSet
  intro x _
  dsimp only
  rw [real_inner_comm, Matrix.inner_toEuclideanCLM]
  congr 1
  simp only [dotProduct, Matrix.mulVec, Matrix.diagonal_apply]
  apply Finset.sum_congr rfl
  intro i _
  simp
  ring

theorem gaussianPosition_maximal_diagonal_equal (n : ℕ)
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsCompact K)
    (hmax : GaussianPositionMaximal n K) (i j : Fin n) :
    (∫ x in K, (x i) ^ 2 * standardGaussianDensity n x) =
      ∫ x in K, (x j) ^ 2 * standardGaussianDensity n x := by
  let d : Fin n → ℝ := Pi.single i 1 - Pi.single j 1
  have hd : ∑ k, d k = 0 := by simp [d, Finset.sum_sub_distrib]
  have h := gaussianPosition_maximal_diagonal_variation n K hK hmax d hd
  have heq (x : EuclideanSpace ℝ (Fin n)) :
      (∑ k, d k * (x k) ^ 2) * standardGaussianDensity n x =
        (x i) ^ 2 * standardGaussianDensity n x - (x j) ^ 2 * standardGaussianDensity n x := by
    simp only [d, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
    simp [Pi.single_apply, Finset.sum_ite_eq']
  simp_rw [heq] at h
  have hi : IntegrableOn (fun x : EuclideanSpace ℝ (Fin n) => (x i) ^ 2 * standardGaussianDensity n x) K :=
    ContinuousOn.integrableOn_compact hK
      ((by fun_prop : Continuous (fun x : EuclideanSpace ℝ (Fin n) => (x i) ^ 2)).mul
        (standardGaussianDensity_smooth n).continuous).continuousOn
  have hj : IntegrableOn (fun x : EuclideanSpace ℝ (Fin n) => (x j) ^ 2 * standardGaussianDensity n x) K :=
    ContinuousOn.integrableOn_compact hK
      ((by fun_prop : Continuous (fun x : EuclideanSpace ℝ (Fin n) => (x j) ^ 2)).mul
        (standardGaussianDensity_smooth n).continuous).continuousOn
  rw [integral_sub hi hj] at h
  exact sub_eq_zero.mp h

theorem gaussianPosition_maximal_second_moments (n : ℕ)
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsCompact K)
    (hmax : GaussianPositionMaximal n K) :
    ∃ α : ℝ, 0 ≤ α ∧ ∀ i j : Fin n,
      (∫ x in K, x i * x j ∂stdGaussian (EuclideanSpace ℝ (Fin n))) =
        if i = j then α else 0 := by
  classical
  by_cases hn : 0 < n
  · let i₀ : Fin n := ⟨0, hn⟩
    refine ⟨∫ x in K, (x i₀) ^ 2 ∂stdGaussian (EuclideanSpace ℝ (Fin n)),
      integral_nonneg (fun _ => sq_nonneg _), ?_⟩
    intro i j
    rw [gaussianPosition_gaussian_set_integral n K hK.measurableSet]
    by_cases hij : i = j
    · subst j
      simp only [← pow_two]
      rw [gaussianPosition_gaussian_set_integral n K hK.measurableSet]
      exact gaussianPosition_maximal_diagonal_equal n K hK hmax i i₀
    · rw [ite_eq_right hij]
      exact gaussianPosition_maximal_offDiagonal n K hK hmax i j hij
  · have hzero : n = 0 := Nat.eq_zero_of_not_pos hn
    subst n
    refine ⟨0, le_rfl, ?_⟩
    intro i
    exact Fin.elim0 i

end AffineFKProof
