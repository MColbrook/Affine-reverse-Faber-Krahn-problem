module

public import AffineFK.OUPoincareRegression
public import AffineFK.OUFisherRelativeDissipation

/-!
# Numerical relative information and the actual OU Hessian energies

The literal isotropic input moments supply the true L2 coordinate domain.
The canonical numerical information is identified with the actual smooth
relative-score energy, and the ordinary Hessian energy is K+2I+n.
These identities concern the existing canonical information definition;
no new numerical functional or assumed energy formula is introduced.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal Matrix.Norms.L2Operator

theorem ou_isotropic_relativeFisher_score_energy (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (hmean : ∀ i : Fin n, (∫ x : EuclideanSpace ℝ (Fin n), x i ∂ν) = 0)
    (hcov : ∀ i j : Fin n, (∫ x : EuclideanSpace ℝ (Fin n), x i * x j ∂ν) =
      if i = j then (1 : ℝ) else 0)
    (t : ℝ) (ht : 0 < t) :
    let ρ := gaussianSmoothingDensity n ν (Real.exp (-t)) (Real.sqrt (1 - Real.exp (-2 * t)))
    relativeFisherMeasure n (ouInitialLaw n ν t) ≠ (∞ : ℝ≥0∞) ∧
      (relativeFisherMeasure n (ouInitialLaw n ν t)).toReal =
        ∫ x, ‖gaussianRelativeScore n ρ x‖ ^ 2 ∂ouInitialLaw n ν t := by
  let E := EuclideanSpace ℝ (Fin n)
  let c := Real.exp (-t)
  let d := Real.sqrt (1 - Real.exp (-2 * t))
  let ρ := gaussianSmoothingDensity n ν c d
  have hd : 0 < d := (ou_smoothing_scale_domain t ht).2.1
  have hlaw : ouInitialLaw n ν t = densityMeasure n ρ := gaussianSmoothingDensity_law n ν c d hd
  let : IsProbabilityMeasure (densityMeasure n ρ) := by rw [← hlaw]; infer_instance
  have hX : MemLp (id : E → E) 2 ν := memLp_piLp_iff.mpr (isotropic_coordinate_memLp n ν hcov)
  have hout := gaussianSmoothing_density_isotropy n ν hmean hcov c d hd (ou_smoothing_scale_domain t ht).2.2
  have hXout : MemLp (id : E → E) 2 (densityMeasure n ρ) := memLp_piLp_iff.mpr fun i => (hout.1 i).1
  have hord : MemLp (gradient (fun x => Real.log (ρ x))) 2 (densityMeasure n ρ) :=
    (gaussianSmoothing_ordinaryScore_density_memLp_four n ν c d hd).1.mono_exponent (by norm_num)
  have hrel : MemLp (gaussianRelativeScore n ρ) 2 (densityMeasure n ρ) := hord.add hXout
  have hscore : MemLp (gaussianSmoothingScore n ν c d) 2 (ouInitialLaw n ν t) := by
    rw [gaussianSmoothingScore_eq_density_score n ν c d hd, hlaw]
    exact hrel
  have hactual := fisherMeasure_gaussian_smoothing_score_energy n ν hX c d hd hscore
  have heq : relativeFisherMeasure n (ouInitialLaw n ν t) =
      ENNReal.ofReal (∫ x, ‖gaussianRelativeScore n ρ x‖ ^ 2 ∂ouInitialLaw n ν t) := by
    simpa only [gaussianSmoothingScore_eq_density_score n ν c d hd, ouInitialLaw, c, d, ρ] using hactual.2
  refine ⟨hactual.1, ?_⟩
  rw [heq, ENNReal.toReal_ofReal (integral_nonneg (fun x => sq_nonneg _))]

theorem ou_ordinary_hessian_eq_relative_energy (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (hmean : ∀ i : Fin n, (∫ x : EuclideanSpace ℝ (Fin n), x i ∂ν) = 0)
    (hcov : ∀ i j : Fin n, (∫ x : EuclideanSpace ℝ (Fin n), x i * x j ∂ν) =
      if i = j then (1 : ℝ) else 0)
    (t : ℝ) (ht : 0 < t) :
    let ρ := gaussianSmoothingDensity n ν (Real.exp (-t)) (Real.sqrt (1 - Real.exp (-2 * t)))
    (∫ x, matrixHilbertSchmidtSq (densityLogHessian n ρ x) ∂ouInitialLaw n ν t) =
      (∫ x, ∑ i : Fin n, ‖gradient (fun y => gaussianRelativeScore n ρ y i) x‖ ^ 2 ∂ouInitialLaw n ν t) +
        2 * (relativeFisherMeasure n (ouInitialLaw n ν t)).toReal + n := by
  let ρ := gaussianSmoothingDensity n ν (Real.exp (-t)) (Real.sqrt (1 - Real.exp (-2 * t)))
  have hd := (ou_smoothing_scale_domain t ht).2.1
  have hlaw : ouInitialLaw n ν t = densityMeasure n ρ := gaussianSmoothingDensity_law n ν _ _ hd
  have hord : (∫ x, matrixHilbertSchmidtSq (densityLogHessian n ρ x) ∂ouInitialLaw n ν t) =
      ∫ x, ρ x * matrixHilbertSchmidtSq (densityLogHessian n ρ x) := by
    rw [hlaw]
    exact density_integral_eq n ρ (gaussianSmoothingDensity_continuous n ν _ _)
      (fun x => (gaussianSmoothingDensity_pos n ν _ _ hd x).le) _
  have hI := (ou_isotropic_relativeFisher_toReal n ν hmean hcov t ht).2
  have hK := ou_relative_hessian_energy_identity n ν t ht
  dsimp only at hK
  dsimp only
  rw [hord]
  linarith

end AffineFKProof
