module

public import AffineFK.PoincareConvolutionScaled
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.HasLaw

/-!
# Poincare inheritance for genuinely independent random vectors

The actual joint law is a product by independence. Finite-sum inheritance
then follows by induction, using independence of a partial sum from an
unused input. The original probability space is arbitrary.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory TopologicalSpace InnerProductSpace ProbabilityTheory
open scoped Distributions RealInnerProductSpace

theorem poincareConvolution_independent_add
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (n : ℕ) (X Y : Ω → EuclideanSpace ℝ (Fin n))
    (hX : AEMeasurable X μ) (hY : AEMeasurable Y μ) (hind : IndepFun X Y μ)
    (P Q : ℝ) (hP0 : 0 ≤ P) (hQ0 : 0 ≤ Q)
    (hP : ∀ f : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ),
      (∫ x, (f x - ∫ y, f y ∂μ.map X) ^ 2 ∂μ.map X) ≤
        P * (∫ x, ‖gradient f x‖ ^ 2 ∂μ.map X))
    (hQ : ∀ f : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ),
      (∫ x, (f x - ∫ y, f y ∂μ.map Y) ^ 2 ∂μ.map Y) ≤
        Q * (∫ x, ‖gradient f x‖ ^ 2 ∂μ.map Y))
    (f : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ)) :
    (∫ x, (f x - ∫ y, f y ∂μ.map (fun ω => X ω + Y ω)) ^ 2
      ∂μ.map (fun ω => X ω + Y ω)) ≤
      (P + Q) * (∫ x, ‖gradient f x‖ ^ 2 ∂μ.map (fun ω => X ω + Y ω)) := by
  have h := poincareConvolution n (μ.map X) (μ.map Y) P Q hP0 hQ0 hP hQ f
  have hlaw : ((μ.map X).prod (μ.map Y)).map (fun p => p.1 + p.2) =
      μ.map (fun ω => X ω + Y ω) := by
    rw [← hind.map_prod_eq_prod_map_map hX hY,
      AEMeasurable.map_map_of_aemeasurable (by fun_prop) (hX.prodMk hY)]
    rfl
  rwa [hlaw] at h

theorem poincareConvolution_independent_finset
    {Ω ι : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (n : ℕ) (X : ι → Ω → EuclideanSpace ℝ (Fin n))
    (hX : ∀ i, AEMeasurable (X i) μ) (hind : iIndepFun X μ)
    (P : ι → ℝ) (hP0 : ∀ i, 0 ≤ P i)
    (hP : ∀ i, ∀ f : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ),
      (∫ x, (f x - ∫ y, f y ∂μ.map (X i)) ^ 2 ∂μ.map (X i)) ≤
        P i * (∫ x, ‖gradient f x‖ ^ 2 ∂μ.map (X i)))
    (s : Finset ι) (f : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ)) :
    (∫ x, (f x - ∫ y, f y ∂μ.map (fun ω => ∑ i ∈ s, X i ω)) ^ 2
      ∂μ.map (fun ω => ∑ i ∈ s, X i ω)) ≤
      (∑ i ∈ s, P i) * (∫ x, ‖gradient f x‖ ^ 2 ∂μ.map (fun ω => ∑ i ∈ s, X i ω)) := by
  classical
  induction s using Finset.induction_on generalizing f with
  | empty => simp [Measure.map_const]
  | @insert i s hi ih =>
      have hsum : AEMeasurable (fun ω => ∑ j ∈ s, X j ω) μ :=
        s.aemeasurable_fun_sum (fun j _ => hX j)
      have hindsum : IndepFun (X i) (fun ω => ∑ j ∈ s, X j ω) μ := by
        have heq : (∑ j ∈ s, X j) = (fun ω => ∑ j ∈ s, X j ω) := by
          funext ω
          simp only [Finset.sum_apply]
        rw [← heq]
        exact (hind.indepFun_finsetSum_of_notMem₀ hX hi).symm
      have h := poincareConvolution_independent_add μ n (X i) (fun ω => ∑ j ∈ s, X j ω)
        (hX i) hsum hindsum (P i) (∑ j ∈ s, P j) (hP0 i)
        (Finset.sum_nonneg fun j _ => hP0 j) (hP i) ih f
      simpa only [Finset.sum_insert hi] using h

end AffineFKProof
