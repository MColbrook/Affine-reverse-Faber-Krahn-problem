module

public import AffineFK.OUDensityPDEGradient
public import Mathlib.Analysis.Calculus.FDeriv.CompCLM

/-!
# Spatial differentiation of the actual Gaussian time-kernel integral

The differentiated integrand is the actual Gaussian derivative evaluated
on its actual time velocity. Its spatial derivative is dominated locally
by a constant times 1+norm(u), using the proved second Gaussian derivative
bound. This is the mixed-calculus step; no equality of mixed time/space
derivatives or Fisher dissipation identity is assumed.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory Filter Set
open scoped ContDiff Topology

def ouDensityPDETimeKernel (n : ℕ) (a r d : ℝ)
    (x u : EuclideanSpace ℝ (Fin n)) : ℝ :=
  fderiv ℝ (standardGaussianDensity n) (r • (x - a • u))
    (r • (a • u) + d • (x - a • u))

theorem ouDensityPDETimeKernel_hasFDerivAt (n : ℕ) (a r d : ℝ)
    (x u : EuclideanSpace ℝ (Fin n)) :
    HasFDerivAt (fun y => ouDensityPDETimeKernel n a r d y u)
      (r • (fderiv ℝ (fderiv ℝ (standardGaussianDensity n)) (r • (x - a • u))).flip
        (r • (a • u) + d • (x - a • u)) +
      d • fderiv ℝ (standardGaussianDensity n) (r • (x - a • u))) x := by
  let E := EuclideanSpace ℝ (Fin n)
  have hz : HasFDerivAt (fun y : E => r • (y - a • u))
      (r • ContinuousLinearMap.id ℝ E) x := ((hasFDerivAt_id x).sub_const (a • u)).const_smul r
  have hv : HasFDerivAt (fun y : E => r • (a • u) + d • (y - a • u))
      (d • ContinuousLinearMap.id ℝ E) x :=
    (((hasFDerivAt_id x).sub_const (a • u)).const_smul d).const_add (r • (a • u))
  have hk : ContDiff ℝ ∞ (fderiv ℝ (standardGaussianDensity n)) :=
    (standardGaussianDensity_smooth n).fderiv_right (by simp)
  have h := (((hk.differentiable (by simp)).differentiableAt
    (x := r • (x - a • u))).hasFDerivAt.comp x hz).clm_apply hv
  convert! h using 1
  ext w
  simp only [add_apply, smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, map_smul, smul_eq_mul,
    Function.comp_apply]
  dsimp only [E] at *
  exact add_comm _ _

theorem ouDensityPDE_time_kernel_integral_hasFDerivAt (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (hU : Integrable (fun u : EuclideanSpace ℝ (Fin n) => u) ν)
    (a r d : ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    Integrable (fun u => fderiv ℝ (fun y => ouDensityPDETimeKernel n a r d y u) x) ν ∧
    HasFDerivAt (fun y => ∫ u, ouDensityPDETimeKernel n a r d y u ∂ν)
      (∫ u, fderiv ℝ (fun y => ouDensityPDETimeKernel n a r d y u) x ∂ν) x := by
  let E := EuclideanSpace ℝ (Fin n)
  let k := standardGaussianDensity n
  let F : E → E → ℝ := ouDensityPDETimeKernel n a r d
  have hk : ContDiff ℝ ∞ (fderiv ℝ k) := (standardGaussianDensity_smooth n).fderiv_right (by simp)
  have hFamily : ContDiff ℝ ∞ (Function.uncurry (fun u y : E => F y u)) :=
    (hk.comp (by fun_prop)).clm_apply (by fun_prop)
  have hF (y : E) : Continuous (F y) := hFamily.continuous.comp (continuous_id.prodMk continuous_const)
  have hF' (y : E) : ContDiff ℝ ∞ (fun u => fderiv ℝ (fun z => F z u) y) :=
    hFamily.fderiv contDiff_const (by simp)
  obtain ⟨K₁, hK₁, hKb₁⟩ := standardGaussianDensity_iteratedFDeriv_bound n 1
  obtain ⟨K₂, hK₂, hKb₂⟩ := standardGaussianDensity_iteratedFDeriv_bound n 2
  have h1 (z : E) : ‖fderiv ℝ k z‖ ≤ K₁ := by simpa only [norm_iteratedFDeriv_one] using hKb₁ z
  have h2 (z : E) : ‖fderiv ℝ (fderiv ℝ k) z‖ ≤ K₂ := by
    have h := hKb₂ z
    rw [← norm_iteratedFDeriv_fderiv, norm_iteratedFDeriv_one] at h
    exact h
  have hnorm (y u : E) : ‖fderiv ℝ (fun z => F z u) y‖ ≤
      K₂ * ‖r‖ * ‖r • (a • u) + d • (y - a • u)‖ + K₁ * ‖d‖ := by
    rw [(ouDensityPDETimeKernel_hasFDerivAt n a r d y u).fderiv]
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro w
    let z := r • (y - a • u)
    let v := r • (a • u) + d • (y - a • u)
    have hd : ‖fderiv ℝ k z w‖ ≤ K₁ * ‖w‖ :=
      ((fderiv ℝ k z).le_opNorm w).trans (mul_le_mul_of_nonneg_right (h1 z) (norm_nonneg _))
    have hdd : ‖fderiv ℝ (fderiv ℝ k) z w v‖ ≤ (K₂ * ‖w‖) * ‖v‖ := by
      exact ((fderiv ℝ (fderiv ℝ k) z w).le_opNorm v).trans
        (mul_le_mul_of_nonneg_right (((fderiv ℝ (fderiv ℝ k) z).le_opNorm w).trans
          (mul_le_mul_of_nonneg_right (h2 z) (norm_nonneg _))) (norm_nonneg _))
    change ‖r * fderiv ℝ (fderiv ℝ k) z w v + d * fderiv ℝ k z w‖ ≤ _
    calc
      _ ≤ ‖r * fderiv ℝ (fderiv ℝ k) z w v‖ + ‖d * fderiv ℝ k z w‖ := norm_add_le _ _
      _ = ‖r‖ * ‖fderiv ℝ (fderiv ℝ k) z w v‖ + ‖d‖ * ‖fderiv ℝ k z w‖ := by rw [norm_mul, norm_mul]
      _ ≤ ‖r‖ * ((K₂ * ‖w‖) * ‖v‖) + ‖d‖ * (K₁ * ‖w‖) :=
        add_le_add (mul_le_mul_of_nonneg_left hdd (norm_nonneg _))
          (mul_le_mul_of_nonneg_left hd (norm_nonneg _))
      _ = _ := by ring
  let M := ‖x‖ + 1
  have hM : 0 ≤ M := by dsimp [M]; positivity
  let V : E → ℝ := fun u => ‖r‖ * (‖a‖ * ‖u‖) + ‖d‖ * (M + ‖a‖ * ‖u‖)
  let bound : E → ℝ := fun u => K₂ * ‖r‖ * V u + K₁ * ‖d‖
  have hVint : Integrable V ν :=
    ((hU.norm.const_mul ‖a‖).const_mul ‖r‖).add
      (((integrable_const M).add (hU.norm.const_mul ‖a‖)).const_mul ‖d‖)
  have hbint : Integrable bound ν := (hVint.const_mul (K₂ * ‖r‖)).add (integrable_const _)
  have hV (y u : E) (hy : ‖y‖ ≤ M) : ‖r • (a • u) + d • (y - a • u)‖ ≤ V u := by
    have hsub : ‖y - a • u‖ ≤ M + ‖a‖ * ‖u‖ :=
      (norm_sub_le _ _).trans (add_le_add hy (by rw [norm_smul]))
    calc
      _ ≤ ‖r • (a • u)‖ + ‖d • (y - a • u)‖ := norm_add_le _ _
      _ = ‖r‖ * (‖a‖ * ‖u‖) + ‖d‖ * ‖y - a • u‖ := by simp only [norm_smul]
      _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_left hsub (norm_nonneg _))
  have hFt : Integrable (F x) ν := by
    apply (hVint.const_mul K₁).mono' (hF x).aestronglyMeasurable
    exact Filter.Eventually.of_forall fun u => by
      exact ((fderiv ℝ k (r • (x - a • u))).le_opNorm _).trans
        ((mul_le_mul_of_nonneg_right (h1 _) (norm_nonneg _)).trans
          (mul_le_mul_of_nonneg_left (hV x u (by dsimp [M]; linarith [norm_nonneg x])) hK₁))
  have hFint' : Integrable (fun u => fderiv ℝ (fun z => F z u) x) ν := by
    apply hbint.mono' (hF' x).continuous.aestronglyMeasurable
    exact Filter.Eventually.of_forall fun u =>
      (hnorm x u).trans (add_le_add
        (mul_le_mul_of_nonneg_left (hV x u (by dsimp [M]; linarith [norm_nonneg x]))
          (mul_nonneg hK₂ (norm_nonneg _))) le_rfl)
  refine ⟨hFint', ?_⟩
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F' := fun y u => fderiv ℝ (fun z => F z u) y)
    (s := Metric.ball x 1) (bound := bound) (Metric.ball_mem_nhds x (by norm_num))
  · exact Filter.Eventually.of_forall fun y => (hF y).aestronglyMeasurable
  · exact hFt
  · exact (hF' x).continuous.aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun u y hy => by
      have hyM : ‖y‖ ≤ M := by
        have hy' : ‖y - x‖ ≤ 1 := by simpa only [Metric.mem_ball, dist_eq_norm] using le_of_lt hy
        calc
          ‖y‖ = ‖(y - x) + x‖ := by rw [sub_add_cancel]
          _ ≤ ‖y - x‖ + ‖x‖ := norm_add_le _ _
          _ ≤ 1 + ‖x‖ := add_le_add hy' le_rfl
          _ = M := by dsimp [M]; ring
      exact (hnorm y u).trans (add_le_add
        (mul_le_mul_of_nonneg_left (hV y u hyM) (mul_nonneg hK₂ (norm_nonneg _))) le_rfl)
  · exact hbint
  · exact Filter.Eventually.of_forall fun u y _ =>
      (ouDensityPDETimeKernel_hasFDerivAt n a r d y u).differentiableAt.hasFDerivAt

end AffineFKProof
