module

public import AffineFK.ConditionalVectorFieldL4
public import AffineFK.GaussianFourthMoment

/-!
# Fourth moments of a fixed Gaussian conditional field

The first marginal is any probability law; no moment or density is
required. The second marginal is the actual standard Gaussian. A fixed
field with the chosen pointwise conditional representation belongs to
L4 on the actual affine image law and has the exact Gaussian fourth-
moment upper bound. No logarithmic-score identification is claimed here.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory

theorem gaussian_conditional_vector_field_memLp_four (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (a b c : ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (hg : StronglyMeasurable g)
    (hrep : ∀ p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n),
      g (a • p.1 + b • p.2) = c • condExp
        ((inferInstance : MeasurableSpace (EuclideanSpace ℝ (Fin n))).comap
          (fun q : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) => a • q.1 + b • q.2))
        (ν.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))) Prod.snd p) :
    MemLp g 4 ((ν.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))).map
      (fun p => a • p.1 + b • p.2)) ∧
    Integrable (fun x => ‖g x‖ ^ 4) ((ν.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))).map
      (fun p => a • p.1 + b • p.2)) ∧
    (∫ x, ‖g x‖ ^ 4 ∂(ν.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))).map
      (fun p => a • p.1 + b • p.2)) ≤ c ^ 4 * ((n : ℝ) * (n + 2)) := by
  let γ := stdGaussian (EuclideanSpace ℝ (Fin n))
  have hq : MemLp (Prod.snd : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n)) 4 (ν.prod γ) :=
    (stdGaussian_norm_fourth_moment n).1.comp_snd ν
  have hqI : Integrable (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) => ‖p.2‖ ^ 4)
      (ν.prod γ) := hq.integrable_norm_pow (by norm_num)
  have hsource : (∫ p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n), ‖p.2‖ ^ 4
      ∂ν.prod γ) = (n : ℝ) * (n + 2) := by
    rw [integral_prod _ hqI]
    simp only [γ, (stdGaussian_norm_fourth_moment n).2.2, integral_const, probReal_univ, one_smul]
  have hfour := conditional_vector_field_memLp_four (ν.prod γ) Prod.snd hq
    (fun p => a • p.1 + b • p.2) (by fun_prop) c g hg hrep
  exact ⟨hfour.1, hfour.2.1, by simpa only [hsource] using hfour.2.2.2⟩

end AffineFKProof
