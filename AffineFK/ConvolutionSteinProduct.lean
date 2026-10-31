module

public import AffineFK.AffineGaussianIntegrationByParts
public import AffineFK.AffineProductIntegrability
public import AffineFK.SmoothPartials

/-!
# First, second and mixed compact identities for independent affine sums

The fixed-input identities use actual compact affine tests with their
proved derivative factors. Genuine joint L1 bounds precede every use of
Fubini. The abstract weak identities below will be discharged by the
actual smooth density score and second-ratio identities; they are not
assumptions about the Hessian or score of the output law.

Affine compact tests and product integrability reuse the earlier
Mathlib-backed Stein and Gaussian smoothing development with attribution.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory TopologicalSpace
open scoped Distributions

theorem convolution_affine_first_identity (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) (s : EuclideanSpace ℝ (Fin n) → ℝ)
    (i : Fin n)
    (hweak : ∀ ψ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ),
      (∫ x, s x * ψ x ∂ν) = -(∫ x, partialTest n i ψ x ∂ν))
    (a : ℝ) (ha : a ≠ 0) (z : EuclideanSpace ℝ (Fin n))
    (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ)) :
    (∫ x, s x * φ (a • x + z) ∂ν) = -a * (∫ x, partialTest n i φ (a • x + z) ∂ν) := by
  have h := hweak (gaussianAffineTest n a ha z φ)
  have hd : (∫ x, partialTest n i (gaussianAffineTest n a ha z φ) x ∂ν) =
      a * (∫ x, partialTest n i φ (a • x + z) ∂ν) := by
    rw [partialTest_gaussianAffineTest]
    change (∫ x, a * gaussianAffineTest n a ha z (partialTest n i φ) x ∂ν) = _
    simp_rw [gaussianAffineTest_apply]
    rw [integral_const_mul]
  rw [hd] at h
  simpa only [gaussianAffineTest_apply, neg_mul] using h

theorem convolution_affine_second_identity (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) (q : EuclideanSpace ℝ (Fin n) → ℝ)
    (i j : Fin n)
    (hweak : ∀ ψ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ),
      (∫ x, q x * ψ x ∂ν) = ∫ x, partialTest n i (partialTest n j ψ) x ∂ν)
    (a : ℝ) (ha : a ≠ 0) (z : EuclideanSpace ℝ (Fin n))
    (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ)) :
    (∫ x, q x * φ (a • x + z) ∂ν) = a ^ 2 *
      (∫ x, partialTest n i (partialTest n j φ) (a • x + z) ∂ν) := by
  have h := hweak (gaussianAffineTest n a ha z φ)
  rw [second_partialTest_gaussianAffineTest] at h
  change (∫ x, q x * gaussianAffineTest n a ha z φ x ∂ν) =
    ∫ x, (a * a) * gaussianAffineTest n a ha z (partialTest n i (partialTest n j φ)) x ∂ν at h
  simp_rw [gaussianAffineTest_apply] at h
  rw [integral_const_mul] at h
  simpa only [pow_two] using h

theorem convolution_product_first_fst (n : ℕ)
    (ν η : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν] [IsProbabilityMeasure η]
    (s : EuclideanSpace ℝ (Fin n) → ℝ) (hs : Integrable s ν) (i : Fin n)
    (hweak : ∀ ψ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ),
      (∫ x, s x * ψ x ∂ν) = -(∫ x, partialTest n i ψ x ∂ν))
    (a : ℝ) (ha : a ≠ 0) (b : ℝ)
    (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ)) :
    Integrable (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      s p.1 * φ (a • p.1 + b • p.2)) (ν.prod η) ∧
    Integrable (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      partialTest n i φ (a • p.1 + b • p.2)) (ν.prod η) ∧
    (∫ p, s p.1 * φ (a • p.1 + b • p.2) ∂ν.prod η) =
      -a * (∫ p, partialTest n i φ (a • p.1 + b • p.2) ∂ν.prod η) := by
  let W : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) :=
    fun p => a • p.1 + b • p.2
  have hW : Continuous W := by dsimp [W]; fun_prop
  have hL := integrable_fst_mul_test_comp n ν η s hs W hW φ
  have hR : Integrable (fun p => partialTest n i φ (W p)) (ν.prod η) := by
    simpa only [one_mul] using integrable_fst_mul_test_comp n ν η (fun _ => (1 : ℝ))
      (integrable_const 1) W hW (partialTest n i φ)
  refine ⟨hL, hR, ?_⟩
  calc
    _ = ∫ y, (∫ x, s x * φ (a • x + b • y) ∂ν) ∂η := integral_prod_symm _ hL
    _ = ∫ y, -a * (∫ x, partialTest n i φ (a • x + b • y) ∂ν) ∂η :=
      integral_congr_ae (Filter.Eventually.of_forall fun y => convolution_affine_first_identity n ν s i hweak a ha (b • y) φ)
    _ = _ := by rw [integral_const_mul, ← integral_prod_symm _ hR]

theorem convolution_product_first_snd (n : ℕ)
    (ν η : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν] [IsProbabilityMeasure η]
    (s : EuclideanSpace ℝ (Fin n) → ℝ) (hs : Integrable s η) (i : Fin n)
    (hweak : ∀ ψ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ),
      (∫ y, s y * ψ y ∂η) = -(∫ y, partialTest n i ψ y ∂η))
    (a b : ℝ) (hb : b ≠ 0)
    (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ)) :
    Integrable (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      s p.2 * φ (a • p.1 + b • p.2)) (ν.prod η) ∧
    Integrable (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      partialTest n i φ (a • p.1 + b • p.2)) (ν.prod η) ∧
    (∫ p, s p.2 * φ (a • p.1 + b • p.2) ∂ν.prod η) =
      -b * (∫ p, partialTest n i φ (a • p.1 + b • p.2) ∂ν.prod η) := by
  let W : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) :=
    fun p => a • p.1 + b • p.2
  have hW : Continuous W := by dsimp [W]; fun_prop
  have hL := integrable_snd_mul_test_comp n ν η s hs W hW φ
  have hR : Integrable (fun p => partialTest n i φ (W p)) (ν.prod η) := by
    simpa only [one_mul] using integrable_fst_mul_test_comp n ν η (fun _ => (1 : ℝ))
      (integrable_const 1) W hW (partialTest n i φ)
  have hfixed (x : EuclideanSpace ℝ (Fin n)) :
      (∫ y, s y * φ (a • x + b • y) ∂η) = -b * (∫ y, partialTest n i φ (a • x + b • y) ∂η) := by
    simpa only [add_comm] using convolution_affine_first_identity n η s i hweak b hb (a • x) φ
  refine ⟨hL, hR, ?_⟩
  calc
    _ = ∫ x, (∫ y, s y * φ (a • x + b • y) ∂η) ∂ν := integral_prod _ hL
    _ = ∫ x, -b * (∫ y, partialTest n i φ (a • x + b • y) ∂η) ∂ν :=
      integral_congr_ae (Filter.Eventually.of_forall hfixed)
    _ = _ := by rw [integral_const_mul, ← integral_prod _ hR]

theorem convolution_product_second_fst (n : ℕ)
    (ν η : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν] [IsProbabilityMeasure η]
    (q : EuclideanSpace ℝ (Fin n) → ℝ) (hq : Integrable q ν) (i j : Fin n)
    (hweak : ∀ ψ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ),
      (∫ x, q x * ψ x ∂ν) = ∫ x, partialTest n i (partialTest n j ψ) x ∂ν)
    (a : ℝ) (ha : a ≠ 0) (b : ℝ)
    (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ)) :
    Integrable (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      q p.1 * φ (a • p.1 + b • p.2)) (ν.prod η) ∧
    Integrable (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      partialTest n i (partialTest n j φ) (a • p.1 + b • p.2)) (ν.prod η) ∧
    (∫ p, q p.1 * φ (a • p.1 + b • p.2) ∂ν.prod η) = a ^ 2 *
      (∫ p, partialTest n i (partialTest n j φ) (a • p.1 + b • p.2) ∂ν.prod η) := by
  let W : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) :=
    fun p => a • p.1 + b • p.2
  have hW : Continuous W := by dsimp [W]; fun_prop
  have hL := integrable_fst_mul_test_comp n ν η q hq W hW φ
  have hR : Integrable (fun p => partialTest n i (partialTest n j φ) (W p)) (ν.prod η) := by
    simpa only [one_mul] using integrable_fst_mul_test_comp n ν η (fun _ => (1 : ℝ))
      (integrable_const 1) W hW (partialTest n i (partialTest n j φ))
  refine ⟨hL, hR, ?_⟩
  calc
    _ = ∫ y, (∫ x, q x * φ (a • x + b • y) ∂ν) ∂η := integral_prod_symm _ hL
    _ = ∫ y, a ^ 2 * (∫ x, partialTest n i (partialTest n j φ) (a • x + b • y) ∂ν) ∂η :=
      integral_congr_ae (Filter.Eventually.of_forall fun y => convolution_affine_second_identity n ν q i j hweak a ha (b • y) φ)
    _ = _ := by rw [integral_const_mul, ← integral_prod_symm _ hR]

theorem convolution_product_second_snd (n : ℕ)
    (ν η : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν] [IsProbabilityMeasure η]
    (q : EuclideanSpace ℝ (Fin n) → ℝ) (hq : Integrable q η) (i j : Fin n)
    (hweak : ∀ ψ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ),
      (∫ y, q y * ψ y ∂η) = ∫ y, partialTest n i (partialTest n j ψ) y ∂η)
    (a b : ℝ) (hb : b ≠ 0)
    (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ)) :
    Integrable (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      q p.2 * φ (a • p.1 + b • p.2)) (ν.prod η) ∧
    Integrable (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      partialTest n i (partialTest n j φ) (a • p.1 + b • p.2)) (ν.prod η) ∧
    (∫ p, q p.2 * φ (a • p.1 + b • p.2) ∂ν.prod η) = b ^ 2 *
      (∫ p, partialTest n i (partialTest n j φ) (a • p.1 + b • p.2) ∂ν.prod η) := by
  let W : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) :=
    fun p => a • p.1 + b • p.2
  have hW : Continuous W := by dsimp [W]; fun_prop
  have hL := integrable_snd_mul_test_comp n ν η q hq W hW φ
  have hR : Integrable (fun p => partialTest n i (partialTest n j φ) (W p)) (ν.prod η) := by
    simpa only [one_mul] using integrable_fst_mul_test_comp n ν η (fun _ => (1 : ℝ))
      (integrable_const 1) W hW (partialTest n i (partialTest n j φ))
  have hfixed (x : EuclideanSpace ℝ (Fin n)) :
      (∫ y, q y * φ (a • x + b • y) ∂η) = b ^ 2 *
        (∫ y, partialTest n i (partialTest n j φ) (a • x + b • y) ∂η) := by
    simpa only [add_comm] using convolution_affine_second_identity n η q i j hweak b hb (a • x) φ
  refine ⟨hL, hR, ?_⟩
  calc
    _ = ∫ x, (∫ y, q y * φ (a • x + b • y) ∂η) ∂ν := integral_prod _ hL
    _ = ∫ x, b ^ 2 * (∫ y, partialTest n i (partialTest n j φ) (a • x + b • y) ∂η) ∂ν :=
      integral_congr_ae (Filter.Eventually.of_forall hfixed)
    _ = _ := by rw [integral_const_mul, ← integral_prod _ hR]

theorem convolution_product_cross_identity (n : ℕ)
    (ν η : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν] [IsProbabilityMeasure η]
    (v w : EuclideanSpace ℝ (Fin n) → ℝ) (hv : Integrable v ν) (hw : Integrable w η)
    (i j : Fin n)
    (hfirst : ∀ ψ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ),
      (∫ x, v x * ψ x ∂ν) = -(∫ x, partialTest n i ψ x ∂ν))
    (hsecond : ∀ ψ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ),
      (∫ y, w y * ψ y ∂η) = -(∫ y, partialTest n j ψ y ∂η))
    (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0)
    (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ)) :
    Integrable (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      (v p.1 * w p.2) * φ (a • p.1 + b • p.2)) (ν.prod η) ∧
    Integrable (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      partialTest n i (partialTest n j φ) (a • p.1 + b • p.2)) (ν.prod η) ∧
    (∫ p, (v p.1 * w p.2) * φ (a • p.1 + b • p.2) ∂ν.prod η) =
      (a * b) * (∫ p, partialTest n i (partialTest n j φ) (a • p.1 + b • p.2) ∂ν.prod η) := by
  let E := EuclideanSpace ℝ (Fin n)
  let W : E × E → E := fun p => a • p.1 + b • p.2
  have hW : Continuous W := by dsimp [W]; fun_prop
  have hL := integrable_product_mul_test_comp n ν η v w hv hw W hW φ
  have hS := convolution_product_first_snd n ν η w hw j hsecond a b hb (partialTest n i φ)
  have hR : Integrable (fun p => partialTest n i (partialTest n j φ) (W p)) (ν.prod η) :=
    hS.2.1.congr (Filter.Eventually.of_forall fun p => partialTest_commute n j i φ (W p))
  refine ⟨hL, hR, ?_⟩
  calc
    _ = ∫ y, w y * (∫ x, v x * φ (a • x + b • y) ∂ν) ∂η := by
      rw [integral_prod_symm _ hL]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun y => by
        dsimp only [W]
        rw [← integral_const_mul]
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun x => by ring
    _ = ∫ y, -a * (∫ x, w y * partialTest n i φ (a • x + b • y) ∂ν) ∂η := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun y => by
        dsimp only
        rw [convolution_affine_first_identity n ν v i hfirst a ha (b • y) φ, integral_const_mul]
        ring
    _ = -a * (∫ p, w p.2 * partialTest n i φ (a • p.1 + b • p.2) ∂ν.prod η) := by
      rw [integral_const_mul, ← integral_prod_symm _ hS.1]
    _ = -a * (-b * (∫ p, partialTest n j (partialTest n i φ) (a • p.1 + b • p.2) ∂ν.prod η)) := by
      rw [hS.2.2]
    _ = _ := by
      have heq : (fun p : E × E => partialTest n j (partialTest n i φ) (W p)) =
          fun p => partialTest n i (partialTest n j φ) (W p) :=
        funext fun p => partialTest_commute n j i φ (W p)
      change -a * (-b * (∫ p, partialTest n j (partialTest n i φ) (W p) ∂ν.prod η)) = _
      rw [heq]
      ring

end AffineFKProof
