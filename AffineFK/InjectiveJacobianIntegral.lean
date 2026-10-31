module

public import Mathlib.MeasureTheory.Function.Jacobian
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Tactic.NormNum

/-!
# Genuine Jacobian mass and integral bounds for injective Euclidean maps

Mathlib's change-of-variables theorem by Sebastien Gouezel (following
Fremlin's Measure Theory) supplies the actual image measure. The image
inclusion then bounds that measure, and finite target volume derives
integrability of the absolute Jacobian, rather than assuming it.
The core needs only actual within-derivatives on a measurable set;
neither continuous nor everywhere invertible derivatives are required.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory Set
open scoped ENNReal

theorem injective_jacobian_lintegral_image (n : ℕ)
    (F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (DF : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (U : Set (EuclideanSpace ℝ (Fin n))) (hU : MeasurableSet U)
    (hDF : ∀ x ∈ U, HasFDerivWithinAt F (DF x) U x) (hF : InjOn F U) :
    MeasurableSet (F '' U) ∧
      (∫⁻ x in U, ENNReal.ofReal |(DF x).det| ∂volume) = volume (F '' U) :=
  ⟨measurable_image_of_fderivWithin hU hDF hF,
    lintegral_abs_det_fderiv_eq_addHaar_image volume hU hDF hF⟩

theorem injective_jacobian_lintegral_le_volume (n : ℕ)
    (F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (DF : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (U K : Set (EuclideanSpace ℝ (Fin n))) (hU : MeasurableSet U)
    (hDF : ∀ x ∈ U, HasFDerivWithinAt F (DF x) U x) (hF : InjOn F U)
    (himage : F '' U ⊆ K) :
    (∫⁻ x in U, ENNReal.ofReal |(DF x).det| ∂volume) ≤ volume K :=
  (injective_jacobian_lintegral_image n F DF U hU hDF hF).2.trans_le (measure_mono himage)

theorem injective_jacobian_integral_bound (n : ℕ)
    (F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (DF : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (U K : Set (EuclideanSpace ℝ (Fin n))) (hU : MeasurableSet U)
    (hDF : ∀ x ∈ U, HasFDerivWithinAt F (DF x) U x) (hF : InjOn F U)
    (himage : F '' U ⊆ K) (hKfinite : volume K ≠ ∞) :
    IntegrableOn (fun x => |(DF x).det|) U volume ∧
      (∫ x in U, |(DF x).det| ∂volume) = volume.real (F '' U) ∧
      (∫ x in U, |(DF x).det| ∂volume) ≤ volume.real K := by
  have hImageFinite : volume (F '' U) ≠ ∞ :=
    ne_top_of_le_ne_top hKfinite (measure_mono himage)
  have hOne : IntegrableOn (fun _ : EuclideanSpace ℝ (Fin n) => (1 : ℝ)) (F '' U) volume :=
    integrableOn_const hImageFinite
  have hJacobian : IntegrableOn (fun x => |(DF x).det|) U volume := by
    simpa only [smul_eq_mul, mul_one] using
      (integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume hU hDF hF
        (fun _ : EuclideanSpace ℝ (Fin n) => (1 : ℝ))).mp hOne
  have hExact : (∫ x in U, |(DF x).det| ∂volume) = volume.real (F '' U) := by
    have h := integral_image_eq_integral_abs_det_fderiv_smul volume hU hDF hF
      (fun _ : EuclideanSpace ℝ (Fin n) => (1 : ℝ))
    simpa only [setIntegral_const, smul_eq_mul, mul_one] using h.symm
  exact ⟨hJacobian, hExact, hExact.trans_le (measureReal_mono himage hKfinite)⟩

theorem injective_jacobian_integral_bound_of_hasFDerivAt (n : ℕ)
    (F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (DF : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (U K : Set (EuclideanSpace ℝ (Fin n))) (hU : MeasurableSet U)
    (hDF : ∀ x ∈ U, HasFDerivAt F (DF x) x) (hF : InjOn F U)
    (himage : F '' U ⊆ K) (hKfinite : volume K ≠ ∞) :
    IntegrableOn (fun x => |(DF x).det|) U volume ∧
      (∫ x in U, |(DF x).det| ∂volume) = volume.real (F '' U) ∧
      (∫ x in U, |(DF x).det| ∂volume) ≤ volume.real K :=
  injective_jacobian_integral_bound n F DF U K hU
    (fun x hx => (hDF x hx).hasFDerivWithinAt) hF himage hKfinite

theorem injective_C1_jacobian_integral_bound (n : ℕ)
    (F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hC1 : ContDiff ℝ 1 F) (hF : Function.Injective F)
    (K : Set (EuclideanSpace ℝ (Fin n))) (himage : range F ⊆ K)
    (hKfinite : volume K ≠ ∞) :
    Integrable (fun x => |(fderiv ℝ F x).det|) volume ∧
      (∫ x, |(fderiv ℝ F x).det| ∂volume) = volume.real (range F) ∧
      (∫ x, |(fderiv ℝ F x).det| ∂volume) ≤ volume.real K := by
  have hDF (x : EuclideanSpace ℝ (Fin n)) : HasFDerivAt F (fderiv ℝ F x) x :=
    (hC1.differentiable (by norm_num) x).hasFDerivAt
  have h := injective_jacobian_integral_bound_of_hasFDerivAt n F (fderiv ℝ F) univ K
    MeasurableSet.univ (fun x _ => hDF x) hF.injOn
    (by simpa only [image_univ] using himage) hKfinite
  simpa only [IntegrableOn, Measure.restrict_univ, image_univ] using h

end AffineFKProof
