module

public import AffineFK.GaussianEntropyCalculusDissipation
public import Mathlib.Analysis.Calculus.FDeriv.Measurable
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Time integration of the actual compact entropy chain

Actual derivatives are measurable by Mathlib's derivative measurability
theorem. Their proved local bounds have a finite subcover on a compact
positive-time interval, giving interval integrability and the fundamental
theorem of calculus. No entropy identity or derivative integrability is
an unproved premise of the OU application.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory TopologicalSpace Filter Set
open scoped Distributions Topology Interval

theorem positive_time_integral_of_locally_bounded_derivative
    (F D : ℝ → ℝ) (hderiv : ∀ r : ℝ, 0 < r → HasDerivAt F (D r) r)
    (hloc : ∀ r : ℝ, 0 < r → ∃ S : Set ℝ, S ∈ 𝓝 r ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ u ∈ S, ‖D u‖ ≤ C)
    (s t : ℝ) (hs : 0 < s) (hst : s ≤ t) :
    IntervalIntegrable D volume s t ∧ (∫ r in s..t, D r) = F t - F s := by
  classical
  let K := Icc s t
  have hK : IsCompact K := isCompact_Icc
  have hpos (r : K) : 0 < (r : ℝ) := hs.trans_le r.2.1
  choose U hU C hC hb using fun r : K => hloc r (hpos r)
  obtain ⟨A, hcover⟩ := hK.elim_nhds_subcover' (fun r hr => U ⟨r, hr⟩) (fun r hr => hU ⟨r, hr⟩)
  let B := ∑ r ∈ A, C r
  have hB : 0 ≤ B := Finset.sum_nonneg (fun r _ => hC r)
  have hbound (r : ℝ) (hr : r ∈ K) : ‖D r‖ ≤ B := by
    obtain ⟨u, huA, hru⟩ := mem_iUnion₂.mp (hcover hr)
    exact (hb u r hru).trans (Finset.single_le_sum (fun u _ => hC u) huA)
  have hdeq : ∀ᵐ r ∂(volume.restrict (Ioc s t)), deriv F r = D r := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    exact (hderiv r (hs.trans hr.1)).deriv
  have hi : Integrable (deriv F) (volume.restrict (Ioc s t)) := by
    apply (integrable_const B).mono' (aestronglyMeasurable_deriv F _)
    filter_upwards [ae_restrict_mem measurableSet_Ioc, hdeq] with r hr heq
    rw [heq]
    exact hbound r ⟨hr.1.le, hr.2⟩
  have hDi : IntegrableOn D (Ioc s t) volume := hi.congr hdeq
  have hDI : IntervalIntegrable D volume s t :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hst).mpr hDi
  refine ⟨hDI, intervalIntegral.integral_eq_sub_of_hasDerivAt ?_ hDI⟩
  intro r hr
  rw [uIcc_of_le hst] at hr
  exact hderiv r (hs.trans_le hr.1)

theorem ou_compact_entropy_time_integral (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (hU : Integrable (fun u : EuclideanSpace ℝ (Fin n) => u) ν)
    (ψ g : ℝ → ℝ) (hψ : ∀ r : ℝ, 0 < r → HasDerivAt ψ (g r) r)
    (hgm : Measurable g) (B : ℝ) (hB : 0 ≤ B) (hgb : ∀ r : ℝ, 0 < r → ‖g r‖ ≤ B)
    (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ))
    (s t : ℝ) (hs : 0 < s) (hst : s ≤ t) :
    let D := fun r : ℝ => ∫ x : EuclideanSpace ℝ (Fin n), φ x *
      g (gaussianSmoothingDensity n ν (Real.exp (-r)) (Real.sqrt (1 - Real.exp (-2 * r))) x /
        standardGaussianDensity n x) * ouDensityTimeDerivative n ν r x
    let F := fun r : ℝ => ∫ x : EuclideanSpace ℝ (Fin n), φ x *
      (standardGaussianDensity n x * ψ (gaussianSmoothingDensity n ν (Real.exp (-r))
        (Real.sqrt (1 - Real.exp (-2 * r))) x / standardGaussianDensity n x))
    IntervalIntegrable D volume s t ∧ (∫ r in s..t, D r) = F t - F s := by
  let E := EuclideanSpace ℝ (Fin n)
  let q : ℝ → E → ℝ := fun r x => gaussianSmoothingDensity n ν (Real.exp (-r))
    (Real.sqrt (1 - Real.exp (-2 * r))) x / standardGaussianDensity n x
  let F : ℝ → ℝ := fun r => ∫ x : E, φ x * (standardGaussianDensity n x * ψ (q r x))
  let D : ℝ → ℝ := fun r => ∫ x : E, φ x * g (q r x) * ouDensityTimeDerivative n ν r x
  have hderiv (r : ℝ) (hr : 0 < r) : HasDerivAt F (D r) r :=
    (ou_compact_entropy_chain_rule n ν hU ψ g hψ hgm B hB hgb φ r hr).2
  obtain ⟨M, hM, hMbound⟩ := φ.hasCompactSupport.isBounded.exists_pos_norm_le
  have hφ : Integrable (fun x : E => ‖φ x‖) volume :=
    (φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport).norm
  have hloc (r : ℝ) (hr : 0 < r) : ∃ S : Set ℝ, S ∈ 𝓝 r ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ u ∈ S, ‖D u‖ ≤ C := by
    obtain ⟨S, hS, C, hC, hCb⟩ := ou_density_time_derivative_local_bound n ν hU r hr M hM.le
    refine ⟨S, hS, B * C * (∫ x : E, ‖φ x‖), by positivity, ?_⟩
    intro u hu
    have hbound (x : E) : ‖φ x * g (q u x) * ouDensityTimeDerivative n ν u x‖ ≤ (B * C) * ‖φ x‖ := by
      by_cases hx : φ x = 0
      · simp only [hx, zero_mul, norm_zero, mul_zero, le_refl]
      · have hD := (hCb u hu).2 x (hMbound x (subset_tsupport φ hx))
        have hq : 0 < q u x := div_pos
          (gaussianSmoothingDensity_pos n ν _ _ (ou_smoothing_scale_domain u (hCb u hu).1).2.1 x)
          (standardGaussianDensity_pos n x)
        calc
          _ = ‖φ x‖ * ‖g (q u x)‖ * ‖ouDensityTimeDerivative n ν u x‖ := by simp only [norm_mul]
          _ ≤ ‖φ x‖ * B * C := mul_le_mul
            (mul_le_mul_of_nonneg_left (hgb _ hq) (norm_nonneg _)) hD (norm_nonneg _)
            (mul_nonneg (norm_nonneg _) hB)
          _ = _ := by ring
    exact (norm_integral_le_of_norm_le (hφ.const_mul (B * C))
      (Filter.Eventually.of_forall hbound)).trans_eq (integral_const_mul _ _)
  exact positive_time_integral_of_locally_bounded_derivative F D hderiv hloc s t hs hst

end AffineFKProof
