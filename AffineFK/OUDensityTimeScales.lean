module

public import AffineFK.OrnsteinUhlenbeckScales
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Actual positive-time derivatives of the OU smoothing curve

These are derivatives of the exponential and square-root functions, not
assumed semigroup or entropy identities. The square-root chain rule is used
only at strictly positive time, where its argument is strictly positive.
-/

@[expose] public noncomputable section
namespace AffineFKProof

theorem ou_scale_a_hasDerivAt (t : ℝ) :
    HasDerivAt (fun s : ℝ => Real.exp (-s)) (-Real.exp (-t)) t := by
  simpa only [Pi.neg_apply, id_eq, mul_neg_one] using (hasDerivAt_id t).neg.exp

theorem ou_scale_b_hasDerivAt (t : ℝ) (ht : 0 < t) :
    HasDerivAt (fun s : ℝ => Real.sqrt (1 - Real.exp (-2 * s)))
      (Real.exp (-2 * t) / Real.sqrt (1 - Real.exp (-2 * t))) t := by
  have hd := ou_smoothing_scale_domain t ht
  have hpos : 0 < 1 - Real.exp (-2 * t) := Real.sqrt_pos.mp hd.2.1
  have he : HasDerivAt (fun s : ℝ => Real.exp (-2 * s))
      (-2 * Real.exp (-2 * t)) t := by
    convert ((hasDerivAt_id t).const_mul (-2 : ℝ)).exp using 1 <;>
      simp only [id_eq] <;> ring
  convert ((he.const_sub 1).sqrt hpos.ne') using 1 <;>
    field_simp [hd.2.1.ne'] <;> ring

theorem ou_scale_derivatives_continuousAt (t : ℝ) (ht : 0 < t) :
    ContinuousAt (fun s : ℝ => -Real.exp (-s)) t ∧
    ContinuousAt (fun s : ℝ => Real.exp (-2 * s) /
      Real.sqrt (1 - Real.exp (-2 * s))) t := by
  have ha : Continuous (fun s : ℝ => -Real.exp (-s)) := by fun_prop
  have hn : Continuous (fun s : ℝ => Real.exp (-2 * s)) := by fun_prop
  have hb : Continuous (fun s : ℝ => Real.sqrt (1 - Real.exp (-2 * s))) := by fun_prop
  exact ⟨ha.continuousAt, hn.continuousAt.div hb.continuousAt
    (ou_smoothing_scale_domain t ht).2.1.ne'⟩

theorem ou_affine_curve_hasDerivAt (n : ℕ)
    (u g : EuclideanSpace ℝ (Fin n)) (t : ℝ) (ht : 0 < t) :
    HasDerivAt (fun s : ℝ => Real.exp (-s) • u + Real.sqrt (1 - Real.exp (-2 * s)) • g)
      ((-Real.exp (-t)) • u +
        (Real.exp (-2 * t) / Real.sqrt (1 - Real.exp (-2 * t))) • g) t :=
  ((ou_scale_a_hasDerivAt t).smul_const u).add ((ou_scale_b_hasDerivAt t ht).smul_const g)

end AffineFKProof
