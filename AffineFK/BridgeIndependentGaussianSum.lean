module

public import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Independence
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
public import Mathlib.Probability.Moments.Covariance

/-!
# Genuine independent product sums of Gaussian processes

These lemmas use actual product probabilities, Gaussian finite laws and
Mathlib's measure-preserving projections and independence theorems. They
do not assume the output Gaussian law, its mean or its covariance.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory

theorem bridge_gaussian_process_prod_sum {Ω Λ I : Type*} [MeasurableSpace Ω]
    [MeasurableSpace Λ] (μ : Measure Ω) (ν : Measure Λ) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (X : I → Ω → ℝ) (Y : I → Λ → ℝ)
    (hX : IsGaussianProcess X μ) (hY : IsGaussianProcess Y ν) :
    IsGaussianProcess (fun i (p : Ω × Λ) => X i p.1+Y i p.2) (μ.prod ν) := by
  classical
  constructor
  intro J
  let F : Ω → J → ℝ := fun ω i => X i.1 ω
  let G : Λ → J → ℝ := fun ω i => Y i.1 ω
  have hF : HasGaussianLaw F μ := hX.hasGaussianLaw J
  have hG : HasGaussianLaw G ν := hY.hasGaussianLaw J
  have hFp : HasGaussianLaw (fun p : Ω × Λ => F p.1) (μ.prod ν) := by
    letI := hF.isGaussian_map
    exact ((show HasLaw F (μ.map F) μ from ⟨hF.aemeasurable,rfl⟩).comp
      (measurePreserving_fst (μ := μ) (ν := ν)).hasLaw).hasGaussianLaw
  have hGp : HasGaussianLaw (fun p : Ω × Λ => G p.2) (μ.prod ν) := by
    letI := hG.isGaussian_map
    exact ((show HasLaw G (ν.map G) ν from ⟨hG.aemeasurable,rfl⟩).comp
      (measurePreserving_snd (μ := μ) (ν := ν)).hasLaw).hasGaussianLaw
  exact ((indepFun_prod₀ hF.aemeasurable hG.aemeasurable).hasGaussianLaw hFp hGp).add

theorem bridge_integral_prod_sum {Ω Λ : Type*} [MeasurableSpace Ω] [MeasurableSpace Λ]
    (μ : Measure Ω) (ν : Measure Λ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (X : Ω → ℝ) (Y : Λ → ℝ) (hX : Integrable X μ) (hY : Integrable Y ν) :
    (∫ p : Ω × Λ, X p.1+Y p.2 ∂μ.prod ν) = (∫ ω, X ω ∂μ)+(∫ ω, Y ω ∂ν) := by
  have hx : Integrable (fun p : Ω × Λ => X p.1) (μ.prod ν) :=
    (measurePreserving_fst (μ := μ) (ν := ν)).integrable_comp_of_integrable hX
  have hy : Integrable (fun p : Ω × Λ => Y p.2) (μ.prod ν) :=
    (measurePreserving_snd (μ := μ) (ν := ν)).integrable_comp_of_integrable hY
  rw [integral_add hx hy]
  exact congrArg₂ (fun a b : ℝ => a+b)
    ((measurePreserving_fst (μ := μ) (ν := ν)).hasLaw.integral_comp hX.aestronglyMeasurable)
    ((measurePreserving_snd (μ := μ) (ν := ν)).hasLaw.integral_comp hY.aestronglyMeasurable)

theorem bridge_covariance_prod_sum {Ω Λ : Type*} [MeasurableSpace Ω] [MeasurableSpace Λ]
    (μ : Measure Ω) (ν : Measure Λ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (X X' : Ω → ℝ) (Y Y' : Λ → ℝ)
    (hX : MemLp X 2 μ) (hX' : MemLp X' 2 μ) (hY : MemLp Y 2 ν) (hY' : MemLp Y' 2 ν) :
    cov[fun p : Ω × Λ => X p.1+Y p.2, fun p => X' p.1+Y' p.2; μ.prod ν] =
      cov[X,X'; μ]+cov[Y,Y'; ν] := by
  have hx : MemLp (fun p : Ω × Λ => X p.1) 2 (μ.prod ν) :=
    hX.comp_measurePreserving (measurePreserving_fst (μ := μ) (ν := ν))
  have hx' : MemLp (fun p : Ω × Λ => X' p.1) 2 (μ.prod ν) :=
    hX'.comp_measurePreserving (measurePreserving_fst (μ := μ) (ν := ν))
  have hy : MemLp (fun p : Ω × Λ => Y p.2) 2 (μ.prod ν) :=
    hY.comp_measurePreserving (measurePreserving_snd (μ := μ) (ν := ν))
  have hy' : MemLp (fun p : Ω × Λ => Y' p.2) 2 (μ.prod ν) :=
    hY'.comp_measurePreserving (measurePreserving_snd (μ := μ) (ν := ν))
  have hxy : cov[fun p : Ω × Λ => X p.1, fun p => Y' p.2; μ.prod ν] = 0 :=
    (indepFun_prod₀ hX.aemeasurable hY'.aemeasurable).covariance_eq_zero hx hy'
  have hyx : cov[fun p : Ω × Λ => Y p.2, fun p => X' p.1; μ.prod ν] = 0 := by
    rw [covariance_comm]
    exact (indepFun_prod₀ hX'.aemeasurable hY.aemeasurable).covariance_eq_zero hx' hy
  change cov[(fun p : Ω × Λ => X p.1)+(fun p => Y p.2),
    (fun p => X' p.1)+(fun p => Y' p.2); μ.prod ν] = _
  rw [covariance_add_left hx hy (hx'.add hy'), covariance_add_right hx hx' hy',
    covariance_add_right hy hx' hy', hxy, hyx]
  rw [(measurePreserving_fst (μ := μ) (ν := ν)).hasLaw.covariance_fun_comp hX.aemeasurable hX'.aemeasurable,
    (measurePreserving_snd (μ := μ) (ν := ν)).hasLaw.covariance_fun_comp hY.aemeasurable hY'.aemeasurable]
  simp

end AffineFKProof
