module

public import AffineFK.OUInformationIntegral
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# The complete time integral of the two OU information bounds

The exponential first bound proves genuine integrability on the positive
half-line. The finite-interval change of variables then passes to infinity
through Mathlib's improper-integral theorem. No numerical quadrature or
assumption about the value of this integral enters the argument.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory Set Filter

theorem ouInformationEnvelope_nonneg (A B t : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    0 ≤ ouInformationEnvelope A B t :=
  le_min (mul_nonneg (Real.exp_pos _).le hA)
    (mul_nonneg (div_nonneg (mul_nonneg (by norm_num) (Real.exp_pos _).le)
      (sq_nonneg _)) hB)

theorem ouInformationEnvelope_integrable_Ioi (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    IntegrableOn (ouInformationEnvelope A B) (Ioi 0) volume := by
  have hdom : IntegrableOn (fun t : ℝ => A * Real.exp (-2 * t)) (Ioi 0) volume :=
    (integrableOn_exp_mul_Ioi (a := (-2 : ℝ)) (by norm_num) 0).const_mul A
  apply hdom.mono'
  · unfold ouInformationEnvelope
    fun_prop
  · filter_upwards [] with t
    rw [Real.norm_eq_abs, abs_of_nonneg (ouInformationEnvelope_nonneg A B t hA hB)]
    exact (min_le_left (Real.exp (-2 * t) * A)
      ((2 * Real.exp (-6 * t) / (1 - Real.exp (-2 * t)) ^ 2) * B)).trans_eq (mul_comm _ _)

theorem ouInformationEnvelope_integral_Ioi_bound (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    (∫ t in Ioi (0 : ℝ), ouInformationEnvelope A B t) ≤
      Real.sqrt 2 * Real.sqrt B * Real.sqrt A := by
  have hlim := intervalIntegral_tendsto_integral_Ioi 0
    (ouInformationEnvelope_integrable_Ioi A B hA hB) tendsto_id
  apply le_of_tendsto hlim
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  exact ouInformationEnvelope_time_integral_bound A B 0 t hA hB le_rfl ht

end AffineFKProof
