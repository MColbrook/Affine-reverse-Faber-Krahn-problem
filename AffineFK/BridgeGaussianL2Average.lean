module

public import AffineFK.DensityApproximationL1Translation
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Genuine strongly continuous Gaussian averages in Lebesgue L2

Translations are actual Mathlib Lp composition isometries. The Gaussian
average is a Bochner integral in the Hilbert space L2, whose integrability
follows from that exact isometry. Dominated convergence proves its strong
limit at zero. Its identification with the actual heat kernel is separate.
Reuse: Yury Kudryashov's continuous measure-preserving Lp composition
theorem and Mathlib's proved Bochner dominated convergence.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory Filter
open scoped Topology

def bridgeL2Translate (n : ℕ) (y : EuclideanSpace ℝ (Fin n)) :
    Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) →ₗᵢ[ℝ]
      Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
  Lp.compMeasurePreservingₗᵢ ℝ (densityApproximationTranslation n (-y))
    (densityApproximationTranslation_measurePreserving n (-y))

theorem bridgeL2Translate_coe (n : ℕ) (y : EuclideanSpace ℝ (Fin n))
    (f : Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    (bridgeL2Translate n y f : EuclideanSpace ℝ (Fin n) → ℝ) =ᵐ[volume]
      fun x => f (x+y) := by
  unfold bridgeL2Translate
  change (Lp.compMeasurePreserving (densityApproximationTranslation n (-y))
    (densityApproximationTranslation_measurePreserving n (-y)) f : EuclideanSpace ℝ (Fin n) → ℝ)
      =ᵐ[volume] fun x => f (x+y)
  have h := Lp.coeFn_compMeasurePreserving f
    (densityApproximationTranslation_measurePreserving n (-y))
  simpa only [densityApproximationTranslation, ContinuousMap.coe_mk, Function.comp_def,
    sub_neg_eq_add] using h

theorem bridgeL2Translate_norm (n : ℕ) (y : EuclideanSpace ℝ (Fin n))
    (f : Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    ‖bridgeL2Translate n y f‖ = ‖f‖ := (bridgeL2Translate n y).norm_map f

theorem bridgeL2Translate_zero (n : ℕ)
    (f : Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    bridgeL2Translate n 0 f = f := by
  apply Lp.ext
  simpa only [add_zero] using bridgeL2Translate_coe n 0 f

theorem bridgeL2Translate_continuous (n : ℕ)
    (f : Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    Continuous (fun y => bridgeL2Translate n y f) := by
  exact continuous_const.compMeasurePreservingLp
    ((densityApproximationTranslation_continuous n).comp continuous_neg)
    (fun y => densityApproximationTranslation_measurePreserving n (-y)) (by norm_num)

def bridgeGaussianL2Average (n : ℕ) (b : ℝ)
    (f : Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
  ∫ u, bridgeL2Translate n (b • u) f ∂stdGaussian (EuclideanSpace ℝ (Fin n))

theorem bridgeGaussianL2Average_integrable (n : ℕ) (b : ℝ)
    (f : Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    Integrable (fun u => bridgeL2Translate n (b • u) f)
      (stdGaussian (EuclideanSpace ℝ (Fin n))) := by
  apply (integrable_const ‖f‖).mono'
    (((bridgeL2Translate_continuous n f).comp (by fun_prop)).aestronglyMeasurable)
  exact Eventually.of_forall fun u => (bridgeL2Translate_norm n (b • u) f).le

theorem bridgeGaussianL2Average_norm_le (n : ℕ) (b : ℝ)
    (f : Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    ‖bridgeGaussianL2Average n b f‖ ≤ ‖f‖ := by
  calc
    _ ≤ ∫ u, ‖bridgeL2Translate n (b • u) f‖
        ∂stdGaussian (EuclideanSpace ℝ (Fin n)) := norm_integral_le_integral_norm _
    _ = _ := by simp only [bridgeL2Translate_norm, integral_const, probReal_univ, one_smul]

theorem bridgeGaussianL2Average_zero (n : ℕ)
    (f : Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    bridgeGaussianL2Average n 0 f = f := by
  simp only [bridgeGaussianL2Average, zero_smul, bridgeL2Translate_zero, integral_const,
    probReal_univ, one_smul]

theorem bridgeGaussianL2Average_tendsto (n : ℕ)
    (f : Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    Tendsto (fun b : ℝ => bridgeGaussianL2Average n b f) (𝓝 0) (𝓝 f) := by
  have h := tendsto_integral_filter_of_dominated_convergence (μ := stdGaussian (EuclideanSpace ℝ (Fin n)))
    (bound := fun _ => ‖f‖)
    (F := fun b u => bridgeL2Translate n (b • u) f) (f := fun _ => f)
    (Eventually.of_forall fun b => (bridgeGaussianL2Average_integrable n b f).aestronglyMeasurable)
    (Eventually.of_forall fun b => Eventually.of_forall fun u =>
      (bridgeL2Translate_norm n (b • u) f).le)
    (integrable_const _)
    (Eventually.of_forall fun u => by
      have hu : Tendsto (fun b : ℝ => b • u) (𝓝 0) (𝓝 (0 : EuclideanSpace ℝ (Fin n))) := by
        simpa only [zero_smul] using
          ((show Continuous (fun b : ℝ => b • u) by fun_prop).tendsto (0 : ℝ))
      simpa only [bridgeL2Translate_zero, Function.comp_def] using
        ((bridgeL2Translate_continuous n f).continuousAt.tendsto (x := (0 : EuclideanSpace ℝ (Fin n)))).comp hu)
  simpa only [bridgeGaussianL2Average, integral_const, probReal_univ, one_smul] using h

end AffineFKProof
