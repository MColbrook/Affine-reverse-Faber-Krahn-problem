module

public import AffineFK.PoincareConvolutionIndependent
public import AffineFK.NormalizedSumSteinIdentity

/-! Normalized independent copies preserve an admissible Poincare constant. -/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory TopologicalSpace InnerProductSpace ProbabilityTheory
open scoped Distributions RealInnerProductSpace

theorem poincareConvolution_normalized_copies
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (n m : ℕ) (hm : 0 < m)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (U : Fin m → Ω → EuclideanSpace ℝ (Fin n))
    (hU : ∀ i, HasLaw (U i) ν μ) (hind : iIndepFun U μ)
    (P : ℝ) (hP0 : 0 ≤ P)
    (hP : ∀ f : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ),
      (∫ x, (f x - ∫ y, f y ∂ν) ^ 2 ∂ν) ≤ P * (∫ x, ‖gradient f x‖ ^ 2 ∂ν))
    (f : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ)) :
    (∫ x, (f x - ∫ y, f y ∂μ.map (normalizedSum n m U)) ^ 2 ∂μ.map (normalizedSum n m U)) ≤
      P * (∫ x, ‖gradient f x‖ ^ 2 ∂μ.map (normalizedSum n m U)) := by
  have hRaw : ∀ φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ),
      (∫ x, (φ x - ∫ y, φ y ∂μ.map (fun ω => ∑ i, U i ω)) ^ 2
        ∂μ.map (fun ω => ∑ i, U i ω)) ≤
        ((m : ℝ) * P) * (∫ x, ‖gradient φ x‖ ^ 2 ∂μ.map (fun ω => ∑ i, U i ω)) := by
    intro φ
    have h := poincareConvolution_independent_finset μ n U (fun i => (hU i).aemeasurable)
      hind (fun _ => P) (fun _ => hP0) (fun i ψ => by rw [(hU i).map_eq]; exact hP ψ) Finset.univ φ
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using h
  let a := (Real.sqrt (m : ℝ))⁻¹
  have h := poincareLinearMap_scalar n (μ.map (fun ω => ∑ i, U i ω))
    ((m : ℝ) * P) (mul_nonneg (Nat.cast_nonneg _) hP0) hRaw a f
  have hsum : AEMeasurable (fun ω => ∑ i, U i ω) μ :=
    Finset.univ.aemeasurable_fun_sum (fun i _ => (hU i).aemeasurable)
  have hlaw : (μ.map (fun ω => ∑ i, U i ω)).map (fun x => a • x) =
      μ.map (normalizedSum n m U) := by
    rw [AEMeasurable.map_map_of_aemeasurable (by fun_prop) hsum]
    rfl
  have hcoeff : a ^ 2 * ((m : ℝ) * P) = P := by
    have ha2 : a ^ 2 = (m : ℝ)⁻¹ := by
      dsimp only [a]
      rw [pow_two, inverse_sqrt_square]
    rw [ha2, ← mul_assoc, inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hm)), one_mul]
  rwa [hlaw, hcoeff] at h

end AffineFKProof
