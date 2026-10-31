module

public import AffineFK.GaussianPositionPoincare
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# An elementary radius bound for a volume-one Euclidean ball

The unit-volume coordinate cube lies in the ball of radius sqrt(n)/2.
The actual Haar scaling formula then bounds the radius of any volume-one
Euclidean ball. No Gamma-function estimate or numerical approximation is
needed. Lebesgue/PiLp transport and Haar scaling retain Mathlib's original
Apache-2.0 contributor attribution.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory Set Metric
open scoped ENNReal

def gaussianPositionCube (n : ℕ) : Set (EuclideanSpace ℝ (Fin n)) :=
  {x | ∀ i, (-1 / 2 : ℝ) ≤ x i ∧ x i ≤ (1 / 2 : ℝ)}

theorem gaussianPositionCube_measurable (n : ℕ) : MeasurableSet (gaussianPositionCube n) := by
  have heq : gaussianPositionCube n =
      ⋂ i : Fin n, {x : EuclideanSpace ℝ (Fin n) | x i ∈ Icc (-1 / 2 : ℝ) (1 / 2 : ℝ)} := by
    ext x
    simp [gaussianPositionCube]
  rw [heq]
  exact MeasurableSet.iInter fun i =>
    (show Measurable (fun x : EuclideanSpace ℝ (Fin n) => x i) by fun_prop) measurableSet_Icc

theorem gaussianPositionCube_volume (n : ℕ) : volume (gaussianPositionCube n) = 1 := by
  have hpre : (WithLp.toLp 2) ⁻¹' gaussianPositionCube n =
      Set.pi Set.univ (fun _ : Fin n => Icc (-1 / 2 : ℝ) (1 / 2 : ℝ)) := by
    ext x
    simp [gaussianPositionCube, Pi.le_def, forall_and]
  rw [← (PiLp.volume_preserving_toLp (Fin n)).map_eq,
    Measure.map_apply (by fun_prop) (gaussianPositionCube_measurable n), hpre]
  change (Measure.pi (fun _ : Fin n => (volume : Measure ℝ)))
    (Set.pi Set.univ (fun _ : Fin n => Icc (-1 / 2 : ℝ) (1 / 2 : ℝ))) = 1
  rw [Measure.pi_pi]
  norm_num [Real.volume_Icc]

theorem gaussianPositionCube_subset_ball (n : ℕ) :
    gaussianPositionCube n ⊆ closedBall (0 : EuclideanSpace ℝ (Fin n)) (Real.sqrt n / 2) := by
  intro x hx
  have hs : ‖x‖ ^ 2 ≤ (n : ℝ) / 4 := by
    calc
      _ = ∑ i : Fin n, (x i) ^ 2 := EuclideanSpace.real_norm_sq_eq x
      _ ≤ ∑ _i : Fin n, (1 / 4 : ℝ) := by
        apply Finset.sum_le_sum
        intro i _
        have hi := hx i
        have hp := mul_nonneg (sub_nonneg.mpr hi.2) (show 0 ≤ x i + (1 / 2 : ℝ) by linarith)
        nlinarith
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
  rw [mem_closedBall, dist_zero_right]
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hroot := Real.sq_sqrt hn
  have hroot0 := Real.sqrt_nonneg (n : ℝ)
  nlinarith [norm_nonneg x]

theorem gaussianPosition_volume_one_ball_radius (n : ℕ) (hn : 0 < n)
    (R : ℝ) (hR : 0 < R)
    (hvolume : volume (closedBall (0 : EuclideanSpace ℝ (Fin n)) R) = 1) :
    R ^ 2 ≤ (n : ℝ) / 4 := by
  let E := EuclideanSpace ℝ (Fin n)
  let s : ℝ := Real.sqrt n / 2
  have hs : 0 ≤ s := div_nonneg (Real.sqrt_nonneg _) (by norm_num)
  have hcube : (1 : ℝ≥0∞) ≤ volume (closedBall (0 : E) s) := by
    rw [← gaussianPositionCube_volume n]
    exact measure_mono (gaussianPositionCube_subset_ball n)
  have hsreal : 1 ≤ (volume : Measure E).real (closedBall (0 : E) s) := by
    have h := (ENNReal.toReal_le_toReal ENNReal.one_ne_top measure_closedBall_lt_top.ne).mpr hcube
    simpa only [ENNReal.toReal_one, measureReal_def] using h
  let c : ℝ := (volume : Measure E).real (ball (0 : E) 1)
  have hcpos : 0 < c := ENNReal.toReal_pos
    (isOpen_ball.measure_pos volume ⟨0, by simp⟩).ne' measure_ball_lt_top.ne
  have hRreal : R ^ n * c = 1 := by
    have h := Measure.addHaar_real_closedBall (volume : Measure E) (0 : E) hR.le
    rw [show (volume : Measure E).real (closedBall (0 : E) R) = 1 by
      simp only [measureReal_def, hvolume, ENNReal.toReal_one]] at h
    simpa only [E, finrank_euclideanSpace, Fintype.card_fin, c] using h.symm
  have hsformula : (volume : Measure E).real (closedBall (0 : E) s) = s ^ n * c := by
    simpa only [E, finrank_euclideanSpace, Fintype.card_fin, c] using
      (Measure.addHaar_real_closedBall (volume : Measure E) (0 : E) hs)
  rw [hsformula] at hsreal
  have hpow : R ^ n ≤ s ^ n := (mul_le_mul_iff_left₀ hcpos).mp (by linarith [hRreal, hsreal])
  have hle : R ≤ s := (pow_le_pow_iff_left₀ hR.le hs hn.ne').mp hpow
  have hp := mul_nonneg (sub_nonneg.mpr hle) (add_nonneg hs hR.le)
  have hroot := Real.sq_sqrt (show (0 : ℝ) ≤ (n : ℝ) from Nat.cast_nonneg n)
  dsimp only [s] at hp
  nlinarith

end AffineFKProof
