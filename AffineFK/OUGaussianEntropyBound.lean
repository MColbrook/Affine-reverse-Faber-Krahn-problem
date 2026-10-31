module

public import AffineFK.GaussianKLCalculus
public import AffineFK.OrnsteinUhlenbeckScales
public import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
# Gaussian-mixture entropy upper bound and the large-time OU endpoint

Entropy is the actual extended-valued Kullback--Leibler divergence. Joint
Gaussian density calculation and the proved data processing inequality
derive finiteness and the bound from only a second moment. No initial
density, finite initial entropy or desired mixture bound is assumed.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory InformationTheory Filter
open scoped ENNReal Topology

theorem gaussian_mixture_entropy_bound (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (hsecond : Integrable (fun u : EuclideanSpace ℝ (Fin n) => ‖u‖ ^ 2) ν)
    (a b : ℝ) (hb : 0 < b) :
    klDiv ((ν.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))).map
      (fun p => a • p.1 + b • p.2)) (stdGaussian (EuclideanSpace ℝ (Fin n))) ≤
      ENNReal.ofReal ((1 / 2 : ℝ) * (a ^ 2 * (∫ u, ‖u‖ ^ 2 ∂ν) +
        n * (b ^ 2 - 1 - Real.log (b ^ 2)))) := by
  have hU : MemLp (fun u : EuclideanSpace ℝ (Fin n) => u) 2 ν :=
    (memLp_two_iff_integrable_sq_norm continuous_id.aestronglyMeasurable).mpr hsecond
  exact (gaussian_mixture_klDiv_le_joint n ν a b).trans_eq (gaussian_joint_klDiv_exact n ν hU a b hb)

theorem gaussian_mixture_entropy_finite (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (hsecond : Integrable (fun u : EuclideanSpace ℝ (Fin n) => ‖u‖ ^ 2) ν)
    (a b : ℝ) (hb : 0 < b) :
    klDiv ((ν.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))).map
      (fun p => a • p.1 + b • p.2)) (stdGaussian (EuclideanSpace ℝ (Fin n))) ≠ ∞ :=
  ne_of_lt (lt_of_le_of_lt (gaussian_mixture_entropy_bound n ν hsecond a b hb) ENNReal.ofReal_lt_top)

theorem gaussian_mixture_entropy_bound_unit_second_moment (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (hsecond : Integrable (fun u : EuclideanSpace ℝ (Fin n) => ‖u‖ ^ 2) ν)
    (hmoment : (∫ u : EuclideanSpace ℝ (Fin n), ‖u‖ ^ 2 ∂ν) = n)
    (a b : ℝ) (hb : 0 < b) (hab : a ^ 2 + b ^ 2 = 1) :
    klDiv ((ν.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))).map
      (fun p => a • p.1 + b • p.2)) (stdGaussian (EuclideanSpace ℝ (Fin n))) ≤
      ENNReal.ofReal (-(n : ℝ) / 2 * Real.log (b ^ 2)) := by
  have h := gaussian_mixture_entropy_bound n ν hsecond a b hb
  rw [hmoment] at h
  have heq : (1 / 2 : ℝ) * (a ^ 2 * (n : ℝ) + n * (b ^ 2 - 1 - Real.log (b ^ 2))) =
      -(n : ℝ) / 2 * Real.log (b ^ 2) := by
    calc
      _ = (n : ℝ) / 2 * ((a ^ 2 + b ^ 2) - 1 - Real.log (b ^ 2)) := by ring
      _ = _ := by rw [hab]; ring
  rwa [heq] at h

theorem ou_gaussian_entropy_bound (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (hsecond : Integrable (fun u : EuclideanSpace ℝ (Fin n) => ‖u‖ ^ 2) ν)
    (t : ℝ) (ht : 0 < t) :
    klDiv ((ν.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))).map
      (fun p => Real.exp (-t) • p.1 + Real.sqrt (1 - Real.exp (-2 * t)) • p.2))
      (stdGaussian (EuclideanSpace ℝ (Fin n))) ≤
      ENNReal.ofReal ((1 / 2 : ℝ) * (Real.exp (-2 * t) * (∫ u, ‖u‖ ^ 2 ∂ν) +
        n * ((1 - Real.exp (-2 * t)) - 1 - Real.log (1 - Real.exp (-2 * t))))) := by
  have hd := ou_smoothing_scale_domain t ht
  have hs : Real.sqrt (1 - Real.exp (-2 * t)) ^ 2 = 1 - Real.exp (-2 * t) :=
    Real.sq_sqrt (Real.sqrt_pos.mp hd.2.1).le
  have he : Real.exp (-t) ^ 2 = Real.exp (-2 * t) := by simpa using ou_exponential_power t 2
  simpa only [hs, he] using gaussian_mixture_entropy_bound n ν hsecond
    (Real.exp (-t)) (Real.sqrt (1 - Real.exp (-2 * t))) hd.2.1

theorem ou_gaussian_entropy_tendsto_zero (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (hsecond : Integrable (fun u : EuclideanSpace ℝ (Fin n) => ‖u‖ ^ 2) ν) :
    Tendsto (fun t : ℝ => klDiv ((ν.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))).map
      (fun p => Real.exp (-t) • p.1 + Real.sqrt (1 - Real.exp (-2 * t)) • p.2))
      (stdGaussian (EuclideanSpace ℝ (Fin n)))) atTop (𝓝 0) := by
  have he : Tendsto (fun t : ℝ => Real.exp (-2 * t)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg (by norm_num : (-2 : ℝ) < 0))
  have hd : Tendsto (fun t : ℝ => 1 - Real.exp (-2 * t)) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.sub he
  have hl : Tendsto (fun t : ℝ => Real.log (1 - Real.exp (-2 * t))) atTop (𝓝 0) := by
    simpa only [Real.log_one] using hd.log one_ne_zero
  have hreal : Tendsto (fun t : ℝ => (1 / 2 : ℝ) *
      (Real.exp (-2 * t) * (∫ u, ‖u‖ ^ 2 ∂ν) +
        n * ((1 - Real.exp (-2 * t)) - 1 - Real.log (1 - Real.exp (-2 * t)))))
      atTop (𝓝 0) := by
    have hone : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
    simpa using (he.mul_const (∫ u, ‖u‖ ^ 2 ∂ν)).add
      (((hd.sub hone).sub hl).const_mul (n : ℝ)) |>.const_mul (1 / 2 : ℝ)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (show Tendsto (fun _ : ℝ => (0 : ℝ≥0∞)) atTop (𝓝 0) from tendsto_const_nhds)
    (by simpa only [ENNReal.ofReal_zero] using ENNReal.tendsto_ofReal hreal)
    (Filter.Eventually.of_forall fun _ => zero_le)
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  exact ou_gaussian_entropy_bound n ν hsecond t ht

end AffineFKProof
