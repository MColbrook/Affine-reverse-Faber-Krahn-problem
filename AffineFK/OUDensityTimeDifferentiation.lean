module

public import AffineFK.OUDensityTimeScales
public import AffineFK.AffineProductIntegrability
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Probability.Distributions.Gaussian.Fernique

/-!
# Differentiating actual OU test expectations at positive time

Dominated differentiation is applied under the actual independent product
law. A compact smooth test has bounded first Frechet derivative, and the
dominating function uses only the first moments of the two inputs. The
Gaussian first moment is supplied by Mathlib's Fernique theorem. No time
derivative of a density, entropy identity or tail hypothesis is assumed.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory TopologicalSpace Filter Set
open scoped Distributions Topology

theorem ou_test_expectation_hasDerivAt (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (hU : Integrable (fun u : EuclideanSpace ℝ (Fin n) => u) ν)
    (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ))
    (t : ℝ) (ht : 0 < t) :
    Integrable (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      fderiv ℝ φ (Real.exp (-t) • p.1 + Real.sqrt (1 - Real.exp (-2 * t)) • p.2)
        ((-Real.exp (-t)) • p.1 +
          (Real.exp (-2 * t) / Real.sqrt (1 - Real.exp (-2 * t))) • p.2))
      (ν.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))) ∧
    HasDerivAt (fun s : ℝ => ∫ p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n),
      φ (Real.exp (-s) • p.1 + Real.sqrt (1 - Real.exp (-2 * s)) • p.2)
        ∂ν.prod (stdGaussian (EuclideanSpace ℝ (Fin n))))
      (∫ p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n),
        fderiv ℝ φ (Real.exp (-t) • p.1 + Real.sqrt (1 - Real.exp (-2 * t)) • p.2)
          ((-Real.exp (-t)) • p.1 +
            (Real.exp (-2 * t) / Real.sqrt (1 - Real.exp (-2 * t))) • p.2)
        ∂ν.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))) t := by
  let E := EuclideanSpace ℝ (Fin n)
  let γ := stdGaussian E
  let μ := ν.prod γ
  let a : ℝ → ℝ := fun s => Real.exp (-s)
  let b : ℝ → ℝ := fun s => Real.sqrt (1 - Real.exp (-2 * s))
  let da : ℝ → ℝ := fun s => -Real.exp (-s)
  let db : ℝ → ℝ := fun s => Real.exp (-2 * s) / b s
  let W : ℝ → E × E → E := fun s p => a s • p.1 + b s • p.2
  let V : ℝ → E × E → E := fun s p => da s • p.1 + db s • p.2
  let Dφ : 𝓓((⊤ : Opens E), E →L[ℝ] ℝ) := TestFunction.fderivCLM ℝ ⊤ ⊤ φ
  have hD : ∀ x : E, Dφ x = fderiv ℝ φ x := by
    intro x
    exact congrFun (TestFunction.fderivCLM_apply_of_le φ (by simp)) x
  let K : ℝ := ‖TestFunction.toBoundedContinuousFunctionCLM ℝ Dφ‖
  have hK : 0 ≤ K := norm_nonneg _
  have hD_bound (x : E) : ‖Dφ x‖ ≤ K :=
    (TestFunction.toBoundedContinuousFunctionCLM ℝ Dφ).norm_coe_le_norm x
  let A : ℝ := ‖da t‖ + 1
  let B : ℝ := ‖db t‖ + 1
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hcont := ou_scale_derivatives_continuousAt t ht
  have hda : ContinuousAt da t := hcont.1
  have hdb : ContinuousAt db t := hcont.2
  have hAn : ∀ᶠ s in 𝓝 t, ‖da s‖ < A :=
    hda.norm.eventually (gt_mem_nhds (lt_add_one ‖da t‖))
  have hBn : ∀ᶠ s in 𝓝 t, ‖db s‖ < B :=
    hdb.norm.eventually (gt_mem_nhds (lt_add_one ‖db t‖))
  let S : Set ℝ := {s | 0 < s ∧ ‖da s‖ ≤ A ∧ ‖db s‖ ≤ B}
  have hS : S ∈ 𝓝 t := by
    filter_upwards [lt_mem_nhds ht, hAn, hBn] with s hs ha hb
    exact ⟨hs, ha.le, hb.le⟩
  let F : ℝ → E × E → ℝ := fun s p => φ (W s p)
  let F' : ℝ → E × E → ℝ := fun s p => Dφ (W s p) (V s p)
  have hW (s : ℝ) : Continuous (W s) := by dsimp [W]; fun_prop
  have hV (s : ℝ) : Continuous (V s) := by dsimp [V]; fun_prop
  have hF (s : ℝ) : Continuous (F s) := φ.continuous.comp (hW s)
  have hF' (s : ℝ) : Continuous (F' s) :=
    (Dφ.continuous.comp (hW s)).clm_apply (hV s)
  have hFt : Integrable (F t) μ := by
    simpa only [one_mul] using integrable_fst_mul_test_comp n ν γ
      (fun _ => (1 : ℝ)) (integrable_const 1) (W t) (hW t) φ
  have hG : Integrable (fun g : E => g) γ := IsGaussian.integrable_id
  let bound : E × E → ℝ := fun p => K * (A * ‖p.1‖ + B * ‖p.2‖)
  have hbound_int : Integrable bound μ :=
    (((hU.norm.comp_fst γ).const_mul A).add ((hG.norm.comp_snd ν).const_mul B)).const_mul K
  have hbound : ∀ᵐ p ∂μ, ∀ s ∈ S, ‖F' s p‖ ≤ bound p := by
    exact Filter.Eventually.of_forall fun p s hs => by
      calc
        ‖F' s p‖ ≤ ‖Dφ (W s p)‖ * ‖V s p‖ := (Dφ (W s p)).le_opNorm _
        _ ≤ K * ‖V s p‖ := mul_le_mul_of_nonneg_right (hD_bound _) (norm_nonneg _)
        _ ≤ K * (‖da s • p.1‖ + ‖db s • p.2‖) :=
          mul_le_mul_of_nonneg_left (norm_add_le _ _) hK
        _ = K * (‖da s‖ * ‖p.1‖ + ‖db s‖ * ‖p.2‖) := by rw [norm_smul, norm_smul]
        _ ≤ bound p := mul_le_mul_of_nonneg_left
          (add_le_add (mul_le_mul_of_nonneg_right hs.2.1 (norm_nonneg _))
            (mul_le_mul_of_nonneg_right hs.2.2 (norm_nonneg _))) hK
  have hdiff : ∀ᵐ p ∂μ, ∀ s ∈ S, HasDerivAt (F · p) (F' s p) s := by
    exact Filter.Eventually.of_forall fun p s hs => by
      have hdφ : HasFDerivAt φ (fderiv ℝ φ (W s p)) (W s p) :=
        (φ.contDiff.differentiable (by simp)).differentiableAt.hasFDerivAt
      simpa only [Function.comp_def, F, F', hD, W, V, a, b, da, db] using
        hdφ.comp_hasDerivAt s (ou_affine_curve_hasDerivAt n p.1 p.2 s hs.1)
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le hS
    (Filter.Eventually.of_forall fun s => (hF s).aestronglyMeasurable)
    hFt (hF' t).aestronglyMeasurable hbound hbound_int hdiff
  simpa only [F, F', hD] using h

end AffineFKProof
