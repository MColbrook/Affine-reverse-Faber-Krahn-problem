module

public import AffineFK.GaussianTensorMomentTheorem
public import AffineFK.AffineProductIntegrability
public import Mathlib.MeasureTheory.SpecificCodomains.WithLp

/-!
# The Gaussian quadratic contraction of a random tensor

The tensor depends only on the first variable of the product law. Its
L2 assumption and the Gaussian fourth moments give actual joint L2
membership. Fubini then integrates the fixed-tensor formula without any
symmetry or fourth-moment assumption on the tensor.

The product integrability and Fubini results are from Mathlib's
MeasureTheory.Integral.Prod; coordinatewise Lp membership is from
Etienne Marion's SpecificCodomains.WithLp (Apache-2.0).
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory

theorem real_product_memLp_two
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (η : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure η]
    (f : X → ℝ) (g : Y → ℝ) (hf : MemLp f 2 μ) (hg : MemLp g 2 η) :
    MemLp (fun p : X × Y => f p.1 * g p.2) 2 (μ.prod η) := by
  apply (memLp_two_iff_integrable_sq
    ((hf.comp_fst η).aestronglyMeasurable.mul (hg.comp_snd μ).aestronglyMeasurable)).mpr
  convert hf.integrable_sq.mul_prod hg.integrable_sq using 1
  funext p
  exact mul_pow (f p.1) (g p.2) 2

theorem random_gaussianHermiteContraction_memLp
    (n : ℕ) (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (T : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n × Fin n × Fin n))
    (hT : MemLp T 2 ν) :
    MemLp (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      gaussianHermiteContraction n (T p.1) p.2) 2
      (ν.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))) := by
  apply memLp_piLp_iff.mpr
  intro i
  change MemLp (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
    ∑ j : Fin n, ∑ k : Fin n,
      T p.1 (i, j, k) * (p.2 j * p.2 k - if j = k then 1 else 0)) 2 _
  apply memLp_finsetSum Finset.univ
  intro j _
  apply memLp_finsetSum Finset.univ
  intro k _
  exact real_product_memLp_two ν (stdGaussian (EuclideanSpace ℝ (Fin n)))
    (fun u => T u (i, j, k)) (fun g => g j * g k - if j = k then 1 else 0)
    (hT.eval_piLp (i, j, k)) (stdGaussian_quadratic_memLp n j k)

theorem random_gaussian_tensor_hermite_contraction
    (n : ℕ) (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (T : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n × Fin n × Fin n))
    (hT : MemLp T 2 ν) :
    MemLp (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      gaussianHermiteContraction n (T p.1) p.2) 2
      (ν.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))) ∧
    (∫ p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n),
      ‖gaussianHermiteContraction n (T p.1) p.2‖ ^ 2
      ∂ν.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))) =
      ∫ u, ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
        (T u (i, j, k) ^ 2 + T u (i, j, k) * T u (i, k, j)) ∂ν ∧
    (∫ p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n),
      ‖gaussianHermiteContraction n (T p.1) p.2‖ ^ 2
      ∂ν.prod (stdGaussian (EuclideanSpace ℝ (Fin n)))) ≤
      2 * (∫ u, ‖T u‖ ^ 2 ∂ν) := by
  let γ := stdGaussian (EuclideanSpace ℝ (Fin n))
  have hQ := random_gaussianHermiteContraction_memLp n ν T hT
  have hsq := (memLp_two_iff_integrable_sq_norm hQ.aestronglyMeasurable).mp hQ
  have hTsq := (memLp_two_iff_integrable_sq_norm hT.aestronglyMeasurable).mp hT
  have hfubini := integral_prod (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
    ‖gaussianHermiteContraction n (T p.1) p.2‖ ^ 2) hsq
  refine ⟨hQ, ?_, ?_⟩
  · calc
      _ = ∫ u, ∫ g, ‖gaussianHermiteContraction n (T u) g‖ ^ 2 ∂γ ∂ν := hfubini
      _ = _ := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun u => (stdGaussian_tensor_hermite_contraction n (T u)).2.1
  · calc
      _ = ∫ u, ∫ g, ‖gaussianHermiteContraction n (T u) g‖ ^ 2 ∂γ ∂ν := hfubini
      _ ≤ ∫ u, 2 * ‖T u‖ ^ 2 ∂ν := by
        apply integral_mono hsq.integral_prod_left (hTsq.const_mul 2)
        intro u
        exact (stdGaussian_tensor_hermite_contraction n (T u)).2.2
      _ = _ := integral_const_mul _ _

end AffineFKProof
