/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the preserved upstream LICENSE.
Adapted for the affine Faber--Krahn project by Codex (AI), 28 October 2026.
-/
module

public import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator
public import Mathlib.MeasureTheory.Measure.LevyConvergence
public import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
public import Mathlib.MeasureTheory.Function.LpSpace.Complete

/-!
# Gaussian closure under L2 convergence: attributed existing proof reuse

The generic prefix of Scott Armstrong and Amélie Loher's
`DOZZ/GFFStructure/GaussianClosure.lean` is reused from commit
`5d770d1a6d69fac6dbb63060e8a89861bf3ee330`:
https://github.com/scottnarmstrong/DOZZ/tree/5d770d1a6d69fac6dbb63060e8a89861bf3ee330
The original file, Apache-2.0 LICENSE, citation and Git-blob provenance
remain under `vendor/bridge-primary-static/DOZZ/`. These are their proofs,
not original proofs by Codex or the manuscript authors. Only the local
namespace and import/section presentation differ in the initial copy.
No upstream author endorsement is claimed. Our pinned-toolchain build
and subsequent axiom checking are required before any reuse claim.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology InnerProductSpace RealInnerProductSpace

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- Expectation is the L² pairing with the constant one. -/
theorem integral_eq_inner_one (U : Lp ℝ 2 P) :
    (∫ ω, U ω ∂P) = ⟪U, Lp.const 2 P (1 : ℝ)⟫_ℝ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_const (p := (2 : ℝ≥0∞)) P (1 : ℝ)] with ω hω
  change U ω = Lp.const 2 P (1 : ℝ) ω * U ω
  rw [hω]
  exact (one_mul _).symm

/-- Means converge under L² convergence. -/
theorem tendsto_integral_of_tendsto_L2 {U : ℕ → Lp ℝ 2 P} {V : Lp ℝ 2 P}
    (h : Tendsto U atTop (𝓝 V)) :
    Tendsto (fun n => ∫ ω, U n ω ∂P) atTop (𝓝 (∫ ω, V ω ∂P)) := by
  simp_rw [integral_eq_inner_one]
  exact h.inner tendsto_const_nhds

omit [IsProbabilityMeasure P] in
/-- Mixed second moments are L² pairings. -/
theorem integral_mul_eq_inner (U V : Lp ℝ 2 P) :
    (∫ ω, U ω * V ω ∂P) = ⟪U, V⟫_ℝ := by
  rw [L2.inner_def]
  congr 1
  funext ω
  change U ω * V ω = V ω * U ω
  exact mul_comm _ _

/-- Covariance in L² is a continuous expression in pairings and expectations. -/
theorem covariance_L2_eq (U V : Lp ℝ 2 P) :
    covariance U V P = ⟪U, V⟫_ℝ - (∫ ω, U ω ∂P) * (∫ ω, V ω ∂P) := by
  rw [covariance_eq_sub (Lp.memLp U) (Lp.memLp V)]
  change (∫ ω, U ω * V ω ∂P) - _ = _
  rw [integral_mul_eq_inner]

/-- Covariances converge when both variables converge in L². -/
theorem tendsto_covariance_of_tendsto_L2
    {U V : ℕ → Lp ℝ 2 P} {U₀ V₀ : Lp ℝ 2 P}
    (hU : Tendsto U atTop (𝓝 U₀)) (hV : Tendsto V atTop (𝓝 V₀)) :
    Tendsto (fun n => covariance (U n) (V n) P) atTop (𝓝 (covariance U₀ V₀ P)) := by
  simp_rw [covariance_L2_eq]
  exact (hU.inner hV).sub
    ((tendsto_integral_of_tendsto_L2 hU).mul (tendsto_integral_of_tendsto_L2 hV))

/-- Variances converge under L² convergence. -/
theorem tendsto_variance_of_tendsto_L2 {U : ℕ → Lp ℝ 2 P} {V : Lp ℝ 2 P}
    (h : Tendsto U atTop (𝓝 V)) :
    Tendsto (fun n => variance (U n) P) atTop (𝓝 (variance V P)) := by
  simp_rw [← covariance_self (Lp.aestronglyMeasurable _).aemeasurable]
  exact tendsto_covariance_of_tendsto_L2 h h

/-- A scalar L² limit of Gaussian variables is Gaussian, allowing degenerate limits. -/
theorem hasGaussianLaw_of_tendsto_L2 {U : ℕ → Lp ℝ 2 P} {V : Lp ℝ 2 P}
    (hG : ∀ n, HasGaussianLaw (U n) P) (h : Tendsto U atTop (𝓝 V)) :
    HasGaussianLaw V P := by
  have hdist : TendstoInDistribution (fun n => ⇑(U n)) atTop (⇑V) (fun _ => P) P :=
    (tendstoInMeasure_of_tendsto_Lp h).tendstoInDistribution
      (fun n => (Lp.aestronglyMeasurable (U n)).aemeasurable)
  apply (hasGaussianLaw_iff_charFun_map_eq (Lp.aestronglyMeasurable V).aemeasurable).2
  intro t
  have hmean := tendsto_integral_of_tendsto_L2 h
  have hvar := tendsto_variance_of_tendsto_L2 h
  have hmeanC := Complex.continuous_ofReal.tendsto _ |>.comp hmean
  have hvarC := Complex.continuous_ofReal.tendsto _ |>.comp hvar
  have hexp : Tendsto
      (fun n => Complex.exp ((t : ℂ) * (∫ ω, U n ω ∂P) * Complex.I -
        (variance (U n) P : ℂ) * (t : ℂ) ^ 2 / 2)) atTop
      (𝓝 (Complex.exp ((t : ℂ) * (∫ ω, V ω ∂P) * Complex.I -
        (variance V P : ℂ) * (t : ℂ) ^ 2 / 2))) := by
    exact Complex.continuous_exp.tendsto _ |>.comp
      ((tendsto_const_nhds.mul hmeanC).mul tendsto_const_nhds |>.sub
        ((hvarC.mul tendsto_const_nhds).div tendsto_const_nhds (by norm_num : (2 : ℂ) ≠ 0)))
  have hchar := hdist.tendsto_charFun t
  simp_rw [(hG _).map_eq_gaussianReal, charFun_gaussianReal,
    Real.coe_toNNReal _ (variance_nonneg _ _)] at hchar
  have heq := tendsto_nhds_unique hchar hexp
  rw [heq]
  change Complex.exp ((t : ℂ) * (∫ ω, V ω ∂P) * Complex.I -
    (variance V P : ℂ) * (t : ℂ) ^ 2 / 2) =
    Complex.exp (((∫ ω, V ω * t ∂P) : ℝ) * Complex.I -
      (variance (fun ω => V ω * t) P : ℂ) / 2)
  rw [integral_mul_const, variance_mul_const]
  congr 1
  push_cast
  ring

omit [IsProbabilityMeasure P] in
/-- Gaussianity of all real linear combinations identifies a finite-dimensional law. -/
theorem hasGaussianLaw_pi_of_linearCombinations {ι : Type*} [Fintype ι]
    (Z : ι → Ω → ℝ) (hmeas : ∀ i, AEMeasurable (Z i) P)
    (hlin : ∀ a : ι → ℝ, HasGaussianLaw (fun ω => ∑ i, a i * Z i ω) P) :
    HasGaussianLaw (fun ω i => Z i ω) P := by
  classical
  have hm : AEMeasurable (fun ω i => Z i ω) P := AEMeasurable.of_eval hmeas
  refine ⟨hm, isGaussian_of_isGaussian_map fun L => ?_⟩
  have hform (ω : Ω) : L (fun i => Z i ω) =
      ∑ i, L (Pi.single i 1) * Z i ω := by
    rw [pi_eq_sum_univ' (fun i => Z i ω), map_sum]
    simp only [map_smul, smul_eq_mul, mul_comm]
  have hg : HasGaussianLaw (L ∘ fun ω i => Z i ω) P := by
    simpa only [Function.comp_def, hform] using hlin (fun i => L (Pi.single i 1))
  rw [AEMeasurable.map_map_of_aemeasurable (by fun_prop) hm]
  exact hg.isGaussian_map

omit [IsProbabilityMeasure P] in
/-- Scalar linear combinations of a finite restriction of a Gaussian process are Gaussian. -/
theorem gaussianProcess_linearCombination {T : Type*}
    {Z : T → Ω → ℝ} (hZ : IsGaussianProcess Z P) (I : Finset T) (a : I → ℝ) :
    HasGaussianLaw (fun ω => ∑ i : I, a i * Z i ω) P := by
  let L : (I → ℝ) →L[ℝ] ℝ := ∑ i : I, a i • ContinuousLinearMap.proj i
  have hL (x : I → ℝ) : L x = ∑ i, a i * x i := by
    simp only [L, sum_apply, smul_apply,
      ContinuousLinearMap.proj_apply, smul_eq_mul]
  have hg := (hZ.hasGaussianLaw I).map L
  convert hg using 1
  funext ω
  exact (hL (I.restrict (Z · ω))).symm

omit [IsProbabilityMeasure P] in
/-- L² representatives of finite scalar combinations agree with the pointwise sums. -/
theorem coeFn_L2_linearCombination {ι : Type*} [Fintype ι]
    (a : ι → ℝ) (Z : ι → Lp ℝ 2 P) :
    (⇑(∑ i, a i • Z i)) =ᵐ[P] fun ω => ∑ i, a i * Z i ω := by
  classical
  have hs := Lp.coeFn_finsetSum Finset.univ (fun i => a i • Z i)
  have ht : ∀ᵐ ω ∂P, ∀ i, (a i • Z i) ω = a i * Z i ω :=
    ae_all_iff.2 fun i => Lp.coeFn_smul (a i) (Z i)
  filter_upwards [hs, ht] with ω hω hω'
  rw [hω]
  rw [Finset.sum_apply]
  change ∑ i, (a i • Z i) ω = ∑ i, a i * Z i ω
  exact Finset.sum_congr rfl (fun i _ => hω' i)

/-- Joint Gaussianity is preserved by coordinatewise L² limits, with no countability condition
on the process index. Every finite restriction is handled on its own finite null-set union. -/
theorem isGaussianProcess_of_tendsto_L2 {T : Type*}
    (Z : ℕ → T → Lp ℝ 2 P) (W : T → Lp ℝ 2 P)
    (hZ : ∀ n, IsGaussianProcess (fun t => ⇑(Z n t)) P)
    (hlim : ∀ t, Tendsto (fun n => Z n t) atTop (𝓝 (W t))) :
    IsGaussianProcess (fun t => ⇑(W t)) P := by
  classical
  constructor
  intro I
  apply hasGaussianLaw_pi_of_linearCombinations
    (fun i : I => ⇑(W i)) (fun i => (Lp.aestronglyMeasurable (W i)).aemeasurable)
  intro a
  have hg : ∀ n, HasGaussianLaw (⇑(∑ i : I, a i • Z n i)) P := by
    intro n
    exact (gaussianProcess_linearCombination (hZ n) I a).congr
      (coeFn_L2_linearCombination a (fun i : I => Z n i)).symm
  have hl : Tendsto (fun n => ∑ i : I, a i • Z n i) atTop
      (𝓝 (∑ i : I, a i • W i)) :=
    tendsto_finsetSum _ fun i _ => (hlim i).const_smul (a i)
  exact (hasGaussianLaw_of_tendsto_L2 hg hl).congr (coeFn_L2_linearCombination a _)

end AffineFKProof
