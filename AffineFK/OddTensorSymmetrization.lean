module

public import AffineFK.SteinTestIdentities
public import AffineFK.SteinSumLaw

/-!
# Odd part of a square-integrable tensor field

Antisymmetrisation under an even probability measure preserves L2, does not
increase squared energy, and gives exact oddness and zero mean. The mean
lemma reuses the already checked odd_tensor_integral_zero proof from the
normalised-sum development; the change of variables is Mathlib's invariant
Bochner integral under negation.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory

def oddPart
    {X H : Type*} [Neg X] [AddCommGroup H] [Module ℝ H] (T : X → H) (x : X) : H :=
  (1 / 2 : ℝ) • (T x - T (-x))

theorem oddPart_odd
    {X H : Type*} [InvolutiveNeg X] [AddCommGroup H] [Module ℝ H]
    (T : X → H) (x : X) : oddPart T (-x) = -oddPart T x := by
  simp only [oddPart, neg_neg, ← smul_neg, neg_sub]

theorem oddPart_memLp
    {X H : Type*} [AddGroup X] [MeasurableSpace X] [MeasurableNeg X]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (ν : Measure X) [Measure.IsNegInvariant ν] (T : X → H) (hT : MemLp T 2 ν) :
    MemLp (oddPart T) 2 ν := by
  exact (hT.sub (hT.comp_measurePreserving (Measure.measurePreserving_neg ν))).const_smul (1 / 2 : ℝ)

theorem oddPart_norm_sq_bound
    {X H : Type*} [Neg X] [NormedAddCommGroup H] [NormedSpace ℝ H]
    (T : X → H) (x : X) :
    ‖oddPart T x‖ ^ 2 ≤ (1 / 2 : ℝ) * (‖T x‖ ^ 2 + ‖T (-x)‖ ^ 2) := by
  have hb := norm_add_sq_bound (T x) (-T (-x))
  rw [norm_neg, ← sub_eq_add_neg] at hb
  rw [oddPart, norm_smul, Real.norm_eq_abs]
  norm_num
  nlinarith

theorem oddPart_energy_le
    {X H : Type*} [AddGroup X] [MeasurableSpace X] [MeasurableNeg X]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (ν : Measure X) [Measure.IsNegInvariant ν] (T : X → H) (hT : MemLp T 2 ν) :
    (∫ x, ‖oddPart T x‖ ^ 2 ∂ν) ≤ ∫ x, ‖T x‖ ^ 2 ∂ν := by
  have hneg : MemLp (fun x => T (-x)) 2 ν :=
    hT.comp_measurePreserving (Measure.measurePreserving_neg ν)
  have hint := (memLp_two_iff_integrable_sq_norm hT.aestronglyMeasurable).mp hT
  have hintneg := (memLp_two_iff_integrable_sq_norm hneg.aestronglyMeasurable).mp hneg
  have hodd := oddPart_memLp ν T hT
  have hintodd := (memLp_two_iff_integrable_sq_norm hodd.aestronglyMeasurable).mp hodd
  calc
    _ ≤ ∫ x, (1 / 2 : ℝ) * (‖T x‖ ^ 2 + ‖T (-x)‖ ^ 2) ∂ν :=
      integral_mono hintodd ((hint.add hintneg).const_mul _) (oddPart_norm_sq_bound T)
    _ = (1 / 2 : ℝ) * ((∫ x, ‖T x‖ ^ 2 ∂ν) + (∫ x, ‖T (-x)‖ ^ 2 ∂ν)) := by
      rw [integral_const_mul, integral_add hint hintneg]
    _ = _ := by
      rw [integral_neg_eq_self (fun x => ‖T x‖ ^ 2) ν]
      ring

theorem oddPart_integral_zero
    {X H : Type*} [AddGroup X] [MeasurableSpace X] [MeasurableNeg X]
    [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
    (ν : Measure X) [IsProbabilityMeasure ν] [Measure.IsNegInvariant ν]
    (T : X → H) (hT : MemLp T 2 ν) :
    Integrable (oddPart T) ν ∧ (∫ x, oddPart T x ∂ν) = 0 := by
  exact odd_tensor_integral_zero ν (oddPart T) (oddPart_memLp ν T hT)
    (Filter.Eventually.of_forall (oddPart_odd T))

end AffineFKProof
