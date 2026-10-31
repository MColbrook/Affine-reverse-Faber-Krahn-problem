module

public import AffineFK.BridgePathLawExt
public import AffineFK.BridgeGaussianFiniteLaw
public import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace

/-!
# Equality of continuous Gaussian path laws

Actual scalar coordinate means and covariance kernels determine the law
on the Borel continuous-path space. The argument compares finite Gaussian
coordinate laws, reconstructs finite vector laws, and then uses the genuine
continuous-path Borel sigma algebra. No path-law equality is assumed.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory

theorem bridge_gaussian_continuous_path_law_ext {X : Type*}
    [TopologicalSpace X] [SecondCountableTopology X] [LocallyCompactSpace X]
    (n : ℕ) (μ ν : Measure C(X, EuclideanSpace ℝ (Fin n)))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : IsGaussianProcess (fun q : X × Fin n =>
      fun f : C(X, EuclideanSpace ℝ (Fin n)) => f q.1 q.2) μ)
    (hν : IsGaussianProcess (fun q : X × Fin n =>
      fun f : C(X, EuclideanSpace ℝ (Fin n)) => f q.1 q.2) ν)
    (hm : ∀ t i, (∫ f, f t i ∂μ) = ∫ f, f t i ∂ν)
    (hc : ∀ s t i j, cov[fun f => f s i, fun f => f t j; μ] =
      cov[fun f => f s i, fun f => f t j; ν]) : μ = ν := by
  classical
  apply bridge_continuous_path_law_ext μ ν
  intro I
  let J : Finset (X × Fin n) := I.product Finset.univ
  let F : C(X, EuclideanSpace ℝ (Fin n)) → J → ℝ := fun f q => f q.1.1 q.1.2
  have heq : μ.map F = ν.map F :=
    bridge_gaussian_finite_law_ext μ ν F F (hμ.hasGaussianLaw J) (hν.hasGaussianLaw J)
      (fun q => hm q.1.1 q.1.2)
      (fun q r => hc q.1.1 r.1.1 q.1.2 r.1.2)
  let G : (J → ℝ) → I → EuclideanSpace ℝ (Fin n) := fun v i =>
    WithLp.toLp 2 (fun k => v ⟨(i.1, k), by simp [J, i.2]⟩)
  have hG : Measurable G := Measurable.of_eval (fun i =>
    (WithLp.measurable_toLp 2 (Fin n → ℝ)).comp
      (Measurable.of_eval (fun k => measurable_pi_apply (⟨(i.1, k), by simp [J, i.2]⟩ : J))))
  have hF : Measurable F := by fun_prop
  have hmap := congrArg (fun m : Measure (J → ℝ) => m.map G) heq
  rw [Measure.map_map hG hF, Measure.map_map hG hF] at hmap
  exact hmap

end AffineFKProof
