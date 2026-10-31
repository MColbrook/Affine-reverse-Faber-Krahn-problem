module

public import AffineFK.OrdinaryFisherConvolution
public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Ordinary weak scores under invertible linear maps

The score is transported by the adjoint of the inverse, on the actual
image law. The proof uses actual compact smooth pullbacks and the ordinary
chain rule. The exact energy factor is the squared operator norm of that
inverse, without density or moment assumptions on the input law.

This is the distributional score transport. The separate assertion that
the transformed square root belongs to the completed Sobolev graph is
not inferred from the weak equation in this module.

Adjoints and their isometry are Mathlib's Hilbert-space adjoint results;
Bochner change of variables and Lp map equivalences are also primary
Mathlib results. Their contributor attribution is retained in those modules.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory TopologicalSpace InnerProductSpace
open scoped Distributions RealInnerProductSpace

set_option maxHeartbeats 500000

def ordinaryFisherLinearTest (n : ℕ)
    (A : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ)) :
    𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ) :=
  ⟨φ ∘ A, φ.contDiff.comp A.contDiff,
    φ.hasCompactSupport.comp_homeomorph A.toHomeomorph, Set.subset_univ _⟩

theorem ordinaryFisherLinearTest_gradient_pairing (n : ℕ)
    (A : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ))
    (x h : EuclideanSpace ℝ (Fin n)) :
    ⟪gradient (ordinaryFisherLinearTest n A φ) x, h⟫ = ⟪gradient φ (A x), A h⟫ := by
  rw [inner_gradient_left, inner_gradient_left]
  have hd := ((φ.contDiff.differentiable (by simp)).differentiableAt (x := A x)).hasFDerivAt.comp
    x A.toContinuousLinearMap.hasFDerivAt
  change fderiv ℝ (φ ∘ A) x h = _
  rw [hd.fderiv]
  rfl

theorem ordinaryFisher_component_directional_identity
    (n : ℕ) (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (s : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (hs : MemLp s 2 ν)
    (hweak : ∀ (i : Fin n) (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ)),
      (∫ x, s x i * φ x ∂ν) = -(∫ x, partialTest n i φ x ∂ν))
    (h : EuclideanSpace ℝ (Fin n))
    (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ)) :
    (∫ x, ⟪s x, h⟫ * φ x ∂ν) = -(∫ x, ⟪gradient φ x, h⟫ ∂ν) := by
  have hl (i : Fin n) : Integrable (fun x => s x i * φ x) ν :=
    (hs.eval_piLp i).integrable_mul (testFunction_memLp_two n ν φ)
  have hd (i : Fin n) : Integrable (partialTest n i φ) ν :=
    (testFunction_memLp_two n ν (partialTest n i φ)).integrable (by norm_num)
  have heq : (fun x => ⟪s x, h⟫ * φ x) =
      (fun x => ∑ i : Fin n, h i * (s x i * φ x)) := by
    funext x
    simp only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, star_trivial, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hdeq : (fun x => ⟪gradient φ x, h⟫) =
      (fun x => ∑ i : Fin n, h i * partialTest n i φ x) := by
    funext x
    simp only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, star_trivial, partialTest_apply]
  rw [heq, hdeq, integral_finsetSum _ fun i _ => (hl i).const_mul (h i),
    integral_finsetSum _ fun i _ => (hd i).const_mul (h i), ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_const_mul, integral_const_mul, hweak i φ, mul_neg]

def ordinaryFisherLinearScore (n : ℕ)
    (A : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (s : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (z : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  A.symm.toContinuousLinearMap.adjoint (s (A.symm z))

theorem ordinaryFisherLinearScore_memLp_energy
    (n : ℕ) (ν : Measure (EuclideanSpace ℝ (Fin n)))
    (A : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (s : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (hs : MemLp s 2 ν) :
    MemLp (ordinaryFisherLinearScore n A s) 2 (ν.map A) ∧
      (∫ z, ‖ordinaryFisherLinearScore n A s z‖ ^ 2 ∂ν.map A) ≤
        ‖A.symm.toContinuousLinearMap‖ ^ 2 * ∫ x, ‖s x‖ ^ 2 ∂ν := by
  have hmap : MemLp (ordinaryFisherLinearScore n A s) 2 (ν.map A) := by
    apply A.toHomeomorph.toMeasurableEquiv.memLp_map_measure_iff.mpr
    change MemLp (fun x => A.symm.toContinuousLinearMap.adjoint (s (A.symm (A x)))) 2 ν
    simp only [A.symm_apply_apply]
    apply (hs.norm.const_mul ‖A.symm.toContinuousLinearMap.adjoint‖).mono'
      (A.symm.toContinuousLinearMap.adjoint.continuous.comp_aestronglyMeasurable
        hs.aestronglyMeasurable)
    exact Filter.Eventually.of_forall fun x => A.symm.toContinuousLinearMap.adjoint.le_opNorm (s x)
  refine ⟨hmap, ?_⟩
  have hsq := (memLp_two_iff_integrable_sq_norm hs.aestronglyMeasurable).mp hs
  have hmapsq := (memLp_two_iff_integrable_sq_norm hmap.aestronglyMeasurable).mp hmap
  rw [integral_map A.continuous.measurable.aemeasurable hmapsq.aestronglyMeasurable,
    ← integral_const_mul]
  have hcomp : Integrable (fun x => ‖ordinaryFisherLinearScore n A s (A x)‖ ^ 2) ν :=
    (integrable_map_measure hmapsq.aestronglyMeasurable A.continuous.measurable.aemeasurable).mp hmapsq
  apply integral_mono_ae hcomp (hsq.const_mul _)
  exact Filter.Eventually.of_forall fun x => by
    simp only [ordinaryFisherLinearScore, A.symm_apply_apply]
    have hb := A.symm.toContinuousLinearMap.adjoint.le_opNorm (s x)
    have hn : ‖A.symm.toContinuousLinearMap.adjoint‖ = ‖A.symm.toContinuousLinearMap‖ :=
      ContinuousLinearMap.adjoint.norm_map _
    rw [hn] at hb
    simpa only [mul_pow] using (sq_le_sq₀ (norm_nonneg _)
      (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr hb

theorem ordinaryFisherLinearScore_directional_identity
    (n : ℕ) (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (A : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (s : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hsmeas : StronglyMeasurable s) (hs : MemLp s 2 ν)
    (hweak : ∀ (i : Fin n) (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ)),
      (∫ x, s x i * φ x ∂ν) = -(∫ x, partialTest n i φ x ∂ν))
    (h : EuclideanSpace ℝ (Fin n))
    (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ)) :
    Integrable (fun z => ⟪ordinaryFisherLinearScore n A s z, h⟫ * φ z) (ν.map A) ∧
    Integrable (fun z => ⟪gradient φ z, h⟫) (ν.map A) ∧
    (∫ z, ⟪ordinaryFisherLinearScore n A s z, h⟫ * φ z ∂ν.map A) =
      -(∫ z, ⟪gradient φ z, h⟫ ∂ν.map A) := by
  have hrmeas : StronglyMeasurable (ordinaryFisherLinearScore n A s) :=
    A.symm.toContinuousLinearMap.adjoint.continuous.comp_stronglyMeasurable
      (hsmeas.comp_measurable A.symm.continuous.measurable)
  have hr := (ordinaryFisherLinearScore_memLp_energy n ν A s hs).1
  have hinner : MemLp (fun z => ⟪ordinaryFisherLinearScore n A s z, h⟫) 2 (ν.map A) :=
    ((innerSL ℝ).flip h).comp_memLp' hr
  have hl : Integrable (fun z => ⟪ordinaryFisherLinearScore n A s z, h⟫ * φ z) (ν.map A) :=
    hinner.integrable_mul (testFunction_memLp_two n (ν.map A) φ)
  have hg : MemLp (gradient φ) 2 (ν.map A) := by
    let B := TestFunction.toBoundedContinuousFunctionCLM ℝ (testFunctionGradient φ)
    apply MemLp.of_bound
      ((toDual ℝ (EuclideanSpace ℝ (Fin n))).symm.continuous.comp
        (φ.contDiff.continuous_fderiv (by simp))).aestronglyMeasurable ‖B‖
    exact Filter.Eventually.of_forall fun z => by
      change ‖gradient φ z‖ ≤ ‖B‖
      rw [← testFunctionGradient_apply]
      exact B.norm_coe_le_norm z
  have hd : Integrable (fun z => ⟪gradient φ z, h⟫) (ν.map A) := by
    exact (((innerSL ℝ).flip h).comp_memLp' hg).integrable (by norm_num)
  refine ⟨hl, hd, ?_⟩
  rw [integral_map A.continuous.measurable.aemeasurable hl.aestronglyMeasurable,
    integral_map A.continuous.measurable.aemeasurable hd.aestronglyMeasurable]
  calc
    _ = ∫ x, ⟪s x, A.symm h⟫ * ordinaryFisherLinearTest n A φ x ∂ν := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by
        change ⟪A.symm.toContinuousLinearMap.adjoint (s (A.symm (A x))), h⟫ * φ (A x) =
          ⟪s x, A.symm h⟫ * φ (A x)
        rw [A.symm_apply_apply, ContinuousLinearMap.adjoint_inner_left]
        rfl
    _ = -(∫ x, ⟪gradient (ordinaryFisherLinearTest n A φ) x, A.symm h⟫ ∂ν) :=
      ordinaryFisher_component_directional_identity n ν s hs hweak (A.symm h)
        (ordinaryFisherLinearTest n A φ)
    _ = _ := by
      congr 1
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by
        change ⟪gradient (ordinaryFisherLinearTest n A φ) x, A.symm h⟫ =
          ⟪gradient φ (A x), h⟫
        rw [ordinaryFisherLinearTest_gradient_pairing, A.apply_symm_apply]

end AffineFKProof
