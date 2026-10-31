module

public import AffineFK.H1DirectionalTranslation
public import Mathlib.Probability.Distributions.Gaussian.Multivariate

/-!
# Exact Gaussian second moment of actual L2 directional pairings

The standard Gaussian covariance is the genuine Mathlib theorem.
Joint integrability is established before Fubini; only the given vector
field's actual L2 norm enters, with no dimension factor or fourth moment.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory InnerProductSpace
open scoped RealInnerProductSpace

theorem standardGaussian_directional_second_moment (n : ℕ)
    (w : EuclideanSpace ℝ (Fin n)) :
    Integrable (fun u => (⟪u, w⟫)^2) (stdGaussian (EuclideanSpace ℝ (Fin n))) ∧
      (∫ u, (⟪u, w⟫)^2 ∂stdGaussian (EuclideanSpace ℝ (Fin n))) = ‖w‖^2 := by
  let E := EuclideanSpace ℝ (Fin n)
  let L := toDual ℝ E w
  have hL : MemLp L 2 (stdGaussian E) := IsGaussian.memLp_dual (stdGaussian E) L 2 (by simp)
  have hi : Integrable (fun u => (L u)^2) (stdGaussian E) :=
    (memLp_two_iff_integrable_sq hL.aestronglyMeasurable).mp hL
  have hm : (∫ u, (L u)^2 ∂stdGaussian E) = ‖w‖^2 := by
    have hv := variance_dual_stdGaussian L
    have hLn : ‖L‖ = ‖w‖ := (toDual ℝ E).norm_map w
    rw [hLn] at hv
    rw [variance_eq_sub hL, integral_strongDual_stdGaussian] at hv
    simpa only [Pi.pow_apply, zero_pow (by decide : 2 ≠ 0), sub_zero,
      LinearIsometryEquiv.norm_map] using hv
  constructor
  · simpa only [L, toDual_apply_apply, real_inner_comm] using! hi
  · simpa only [L, toDual_apply_apply, real_inner_comm] using! hm

theorem l2DirectionalPairing_gaussian_second_moment (n : ℕ)
    (g : Lp (EuclideanSpace ℝ (Fin n)) 2
      (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    Integrable (fun u => ‖l2DirectionalPairing n u g‖^2)
      (stdGaussian (EuclideanSpace ℝ (Fin n))) ∧
      (∫ u, ‖l2DirectionalPairing n u g‖^2
        ∂stdGaussian (EuclideanSpace ℝ (Fin n))) = ‖g‖^2 := by
  let E := EuclideanSpace ℝ (Fin n)
  let γ := stdGaussian E
  let F : E × E → ℝ := fun p => (⟪p.1, g p.2⟫)^2
  have hFm : AEStronglyMeasurable F (γ.prod volume) := by
    exact (continuous_fst.stronglyMeasurable.inner
      ((Lp.stronglyMeasurable g).comp_measurable measurable_snd)).pow 2 |>.aestronglyMeasurable
  have hFn (x : E) : (∫ u, ‖F (u,x)‖ ∂γ) = ‖g x‖^2 := by
    calc
      _ = ∫ u, (⟪u, g x⟫)^2 ∂γ := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun u => Real.norm_of_nonneg (sq_nonneg _)
      _ = _ := (standardGaussian_directional_second_moment n (g x)).2
  have hF : Integrable F (γ.prod volume) := by
    apply (integrable_prod_iff' hFm).mpr
    refine ⟨Filter.Eventually.of_forall
      (fun x => (standardGaussian_directional_second_moment n (g x)).1), ?_⟩
    have hg := (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable g)).mp (Lp.memLp g)
    exact hg.congr (Filter.Eventually.of_forall fun x => (hFn x).symm)
  have hpair (u : E) : ‖l2DirectionalPairing n u g‖^2 = ∫ x, F (u,x) := by
    rw [l2_norm_sq_integral]
    apply integral_congr_ae
    filter_upwards [l2DirectionalPairing_coe n u g] with x hx
    rw [hx, Real.norm_eq_abs, sq_abs]
  refine ⟨hF.integral_prod_left.congr
    (Filter.Eventually.of_forall fun u => (hpair u).symm), ?_⟩
  calc
    _ = ∫ u, ∫ x, F (u,x) ∂volume ∂γ := integral_congr_ae (Filter.Eventually.of_forall hpair)
    _ = ∫ x, ∫ u, F (u,x) ∂γ := integral_integral_swap hF
    _ = ∫ x, ‖g x‖^2 := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x =>
        (standardGaussian_directional_second_moment n (g x)).2
    _ = _ := (l2_norm_sq_integral volume g).symm

end AffineFKProof
