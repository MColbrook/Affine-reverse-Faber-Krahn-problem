module

public import AffineFK.SteinTestIdentities

/-!
# Affine changes of compact smooth tests

These are actual translated and rescaled test functions, used when a test
of a normalised sum is viewed as a function of one summand with the others
fixed. All nonzero real scales, including negative ones, are allowed. The
first and ordered second partial derivatives retain their exact scale factors.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory TopologicalSpace
open scoped Distributions RealInnerProductSpace

def translatedTestFunction
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (b : E) (f : 𝓓((⊤ : Opens E), ℝ)) : 𝓓((⊤ : Opens E), ℝ) :=
  ⟨fun x => f (x + b), f.contDiff.comp (contDiff_id.add contDiff_const),
    f.hasCompactSupport.comp_homeomorph (Homeomorph.addRight b), Set.subset_univ _⟩

theorem translatedTestFunction_apply
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (b : E) (f : 𝓓((⊤ : Opens E), ℝ)) (x : E) :
    translatedTestFunction b f x = f (x + b) := by rfl

theorem gradient_translatedTestFunction
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (b : E) (f : 𝓓((⊤ : Opens E), ℝ)) (x : E) :
    gradient (translatedTestFunction b f) x = gradient f (x + b) := by
  have heq : (translatedTestFunction b f : E → ℝ) = f ∘ (fun y => y + b) := rfl
  have ht : HasFDerivAt (fun y : E => y + b) (ContinuousLinearMap.id ℝ E) x :=
    (hasFDerivAt_id x).add_const b
  have hdiff : Differentiable ℝ f := f.contDiff.differentiable (by simp)
  have hd := hdiff.differentiableAt.hasFDerivAt.comp x ht
  rw [heq, gradient, hd.fderiv, ContinuousLinearMap.comp_id]
  rfl

theorem partialTest_smul
    (n : ℕ) (j : Fin n) (c : ℝ)
    (f : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ)) :
    partialTest n j (c • f) = c • partialTest n j f := by
  unfold partialTest
  rw [map_smul, map_smul]

theorem partialTest_translated
    (n : ℕ) (j : Fin n) (b : EuclideanSpace ℝ (Fin n))
    (f : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ)) :
    partialTest n j (translatedTestFunction b f) = translatedTestFunction b (partialTest n j f) := by
  ext x
  rw [partialTest_apply, gradient_translatedTestFunction, translatedTestFunction_apply,
    partialTest_apply]

theorem partialTest_scaled
    (n : ℕ) (j : Fin n) (r : ℝ) (hr : r ≠ 0)
    (f : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ)) :
    partialTest n j (scaledTestFunction r hr f) = r⁻¹ • scaledTestFunction r hr (partialTest n j f) := by
  ext x
  rw [partialTest_apply, gradient_scaledTestFunction]
  change (r⁻¹ • gradient f (r⁻¹ • x)) j = r⁻¹ * (scaledTestFunction r hr (partialTest n j f)) x
  rw [scaledTestFunction_apply, partialTest_apply]
  rfl

def affineTestFunction
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (r : ℝ) (hr : r ≠ 0) (b : E) (f : 𝓓((⊤ : Opens E), ℝ)) :
    𝓓((⊤ : Opens E), ℝ) :=
  translatedTestFunction b (scaledTestFunction r hr f)

theorem affineTestFunction_apply
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (r : ℝ) (hr : r ≠ 0) (b : E) (f : 𝓓((⊤ : Opens E), ℝ)) (x : E) :
    affineTestFunction r hr b f x = f (r⁻¹ • (x + b)) := by rfl

theorem partialTest_affine
    (n : ℕ) (j : Fin n) (r : ℝ) (hr : r ≠ 0) (b : EuclideanSpace ℝ (Fin n))
    (f : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ)) :
    partialTest n j (affineTestFunction r hr b f) =
      r⁻¹ • affineTestFunction r hr b (partialTest n j f) := by
  unfold affineTestFunction
  rw [partialTest_translated, partialTest_scaled]
  rfl

theorem second_partialTest_affine
    (n : ℕ) (j k : Fin n) (r : ℝ) (hr : r ≠ 0) (b : EuclideanSpace ℝ (Fin n))
    (f : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ)) :
    partialTest n k (partialTest n j (affineTestFunction r hr b f)) =
      (r⁻¹ * r⁻¹) • affineTestFunction r hr b (partialTest n k (partialTest n j f)) := by
  rw [partialTest_affine, partialTest_smul, partialTest_affine, smul_smul]

end AffineFKProof
