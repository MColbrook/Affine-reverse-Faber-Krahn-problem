module

public import AffineFK.GaussianPositionIntegral
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.Topology.MetricSpace.Sequences
public import Mathlib.Topology.Algebra.Order.Field
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Gaussian integral decay along escaping linear maps

After normalization, an escaping sequence has a nonzero operator limit
along a subsequence. The kernel of this limit has Lebesgue measure zero.
Outside that kernel the images escape to infinity, and actual Gaussian
decay and dominated convergence give decay of the fixed-domain integral.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology

theorem gaussianPosition_density_tendsto_zero_of_norm_atTop (n : ℕ)
    (x : ℕ → EuclideanSpace ℝ (Fin n))
    (hx : Tendsto (fun k => ‖x k‖) atTop atTop) :
    Tendsto (fun k => standardGaussianDensity n (x k)) atTop (𝓝 0) := by
  obtain ⟨C, _hC, hbound⟩ := standardGaussianDensity_weighted_bound n 1
  have hden : Tendsto (fun k => 1 + ‖x k‖) atTop atTop := tendsto_const_nhds.add_atTop hx
  have hupper : Tendsto (fun k => C / (1 + ‖x k‖)) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero, Function.comp_def] using
      (tendsto_inv_atTop_zero.comp hden).const_mul C
  apply squeeze_zero (fun k => (standardGaussianDensity_pos n (x k)).le) _ hupper
  intro k
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < 1 + ‖x k‖)).mpr
  have h := hbound (x k)
  rw [pow_one, Real.norm_of_nonneg (standardGaussianDensity_pos n (x k)).le] at h
  simpa only [mul_comm] using h

theorem gaussianPosition_point_norm_escape (n : ℕ)
    (A : ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (B : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hA : Tendsto (fun k => ‖A k‖) atTop atTop)
    (hN : Tendsto (fun k => ‖A k‖⁻¹ • A k) atTop (𝓝 B))
    (x : EuclideanSpace ℝ (Fin n)) (hx : B x ≠ 0) :
    Tendsto (fun k => ‖A k x‖) atTop atTop := by
  have hpoint : Tendsto (fun k => (‖A k‖⁻¹ • A k) x) atTop (𝓝 (B x)) :=
    ((ContinuousLinearMap.apply ℝ (EuclideanSpace ℝ (Fin n)) x).continuous.tendsto B).comp hN
  have hprod := hA.atTop_mul_pos (norm_pos_iff.mpr hx) hpoint.norm
  apply hprod.congr'
  filter_upwards [hA.eventually_gt_atTop 0] with k hk
  rw [smul_apply, norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr hk)]
  rw [← mul_assoc, mul_inv_cancel₀ hk.ne', one_mul]

theorem gaussianPosition_integral_escape (n : ℕ)
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsCompact K)
    (A : ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (B : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) (hB : B ≠ 0)
    (hA : Tendsto (fun k => ‖A k‖) atTop atTop)
    (hN : Tendsto (fun k => ‖A k‖⁻¹ • A k) atTop (𝓝 B)) :
    Tendsto (fun k => gaussianPositionIntegral n K (A k)) atTop (𝓝 0) := by
  have hker : B.toLinearMap.ker ≠ ⊤ := by
    intro h
    apply hB
    apply ContinuousLinearMap.ext
    intro x
    have hx : x ∈ B.toLinearMap.ker := by rw [h]; trivial
    exact hx
  have hnull : (volume : Measure (EuclideanSpace ℝ (Fin n))) {x | B x = 0} = 0 :=
    Measure.addHaar_submodule volume B.toLinearMap.ker hker
  have hae : ∀ᵐ x ∂volume, B x ≠ 0 := by
    apply ae_iff.mpr
    simpa only [not_not] using hnull
  have hpoint : ∀ᵐ x ∂volume.restrict K,
      Tendsto (fun k => standardGaussianDensity n (A k x)) atTop (𝓝 (0 : ℝ)) := by
    filter_upwards [ae_restrict_of_ae hae] with x hx
    exact gaussianPosition_density_tendsto_zero_of_norm_atTop n _
      (gaussianPosition_point_norm_escape n A B hA hN x hx)
  obtain ⟨C, _, hbound⟩ := standardGaussianDensity_iteratedFDeriv_bound n 0
  have hbound' (x : EuclideanSpace ℝ (Fin n)) : ‖standardGaussianDensity n x‖ ≤ C := by
    simpa only [norm_iteratedFDeriv_zero] using hbound x
  have hi : Integrable (fun _ : EuclideanSpace ℝ (Fin n) => C) (volume.restrict K) :=
    ContinuousOn.integrableOn_compact hK continuousOn_const
  have h := tendsto_integral_of_dominated_convergence (fun _ : EuclideanSpace ℝ (Fin n) => C)
    (fun k => ((standardGaussianDensity_smooth n).continuous.comp (A k).continuous).aestronglyMeasurable)
    hi (fun k => Eventually.of_forall fun x => hbound' (A k x)) hpoint
  simpa only [integral_zero, gaussianPositionIntegral, Function.comp_def] using h

theorem gaussianPosition_positive_superlevel_bounded (n : ℕ)
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsCompact K)
    (c : ℝ) (hc : 0 < c) :
    Bornology.IsBounded {A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) |
      c ≤ gaussianPositionIntegral n K A} := by
  classical
  by_contra h
  rw [isBounded_iff_forall_norm_le] at h
  push_neg at h
  have hex (k : ℕ) : ∃ A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n),
      c ≤ gaussianPositionIntegral n K A ∧ (k : ℝ) + 1 < ‖A‖ := h ((k : ℝ) + 1)
  choose A hAc hAn using hex
  have hApos (k : ℕ) : 0 < ‖A k‖ := by
    linarith [show (0 : ℝ) ≤ (k : ℝ) from Nat.cast_nonneg k, hAn k]
  let N : ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
    fun k => ‖A k‖⁻¹ • A k
  have hNnorm (k : ℕ) : ‖N k‖ = 1 := by
    dsimp only [N]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (hApos k)),
      inv_mul_cancel₀ (hApos k).ne']
  have hNbdd : Bornology.IsBounded (range N) :=
    isBounded_iff_forall_norm_le.mpr ⟨1, by rintro _ ⟨k, rfl⟩; exact (hNnorm k).le⟩
  obtain ⟨B, _, φ, hφ, hlim⟩ := tendsto_subseq_of_bounded hNbdd (fun k => mem_range_self k)
  have hBnorm : ‖B‖ = 1 := tendsto_nhds_unique hlim.norm (by
    simpa only [Function.comp_apply, hNnorm] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)))
  have hB : B ≠ 0 := by intro hB; rw [hB, norm_zero] at hBnorm; exact zero_ne_one hBnorm
  have hAnorm : Tendsto (fun k => ‖A k‖) atTop atTop :=
    tendsto_atTop_mono (fun k => (hAn k).le) (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
  have hzero := gaussianPosition_integral_escape n K hK (A ∘ φ) B hB
    (hAnorm.comp hφ.tendsto_atTop) hlim
  have hc0 : c ≤ 0 := le_of_tendsto_of_tendsto' tendsto_const_nhds hzero (fun k => hAc (φ k))
  exact (not_le_of_gt hc) hc0

end AffineFKProof
