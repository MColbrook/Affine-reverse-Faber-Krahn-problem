module

public import AffineFK.GaussianReferenceScore
public import Mathlib.Analysis.Distribution.TemperateGrowth
public import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-!
# All-order uniform bounds for the actual standard Gaussian density

The scalar Gaussian dominates every polynomial by the exponential series.
The differential equation Dk(x)=k(x)(-x)^dual propagates this rapid decay
to every Frechet derivative, using Mathlib's higher-product derivative
bound and temperate growth of a continuous linear map. No Gaussian
derivative bound is assumed in the final theorem.

The higher derivative bounds and temperate-growth interfaces are due to
Sebastien Gouezel, Floris van Doorn, Moritz Doll and Anatole Dedecker in
Mathlib (Apache-2.0).
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory
open scoped ContDiff RealInnerProductSpace

theorem gaussian_weighted_scalar_bound (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 0 ≤ r →
      (1 + r) ^ k * Real.exp (-(r ^ 2 / 2)) ≤ C := by
  refine ⟨(2 : ℝ) ^ k + 4 ^ k * (k.factorial : ℝ), by positivity, ?_⟩
  intro r hr
  by_cases hsmall : r ≤ 1
  · have hp : (1 + r) ^ k ≤ (2 : ℝ) ^ k := by gcongr; linarith
    have he : Real.exp (-(r ^ 2 / 2)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg r])
    calc
      _ ≤ (2 : ℝ) ^ k * 1 := mul_le_mul hp he (Real.exp_pos _).le (by positivity)
      _ ≤ _ := by simpa only [mul_one] using le_add_of_nonneg_right (by positivity : 0 ≤ (4 : ℝ) ^ k * (k.factorial : ℝ))
  · have hlarge : 1 ≤ r := le_of_not_ge hsmall
    have hpow : (1 + r) ^ k ≤ 4 ^ k * (r ^ 2 / 2) ^ k := by
      calc
        _ ≤ (2 * r) ^ k := by gcongr; linarith
        _ = 2 ^ k * r ^ k := mul_pow _ _ _
        _ ≤ 2 ^ k * r ^ (2 * k) := mul_le_mul_of_nonneg_left
          (pow_le_pow_right₀ hlarge (show k ≤ 2 * k by omega)) (by positivity)
        _ = (2 * r ^ 2) ^ k := by rw [mul_pow, pow_mul]
        _ = _ := by rw [← mul_pow]; congr 1; ring
    have hfact : (r ^ 2 / 2) ^ k ≤ (k.factorial : ℝ) * Real.exp (r ^ 2 / 2) := by
      have h := Real.pow_div_factorial_le_exp (r ^ 2 / 2) (by positivity : 0 ≤ r ^ 2 / 2) k
      exact (div_le_iff₀ (by positivity : (0 : ℝ) < k.factorial)).mp h |>.trans_eq (mul_comm _ _)
    calc
      _ ≤ (4 ^ k * ((k.factorial : ℝ) * Real.exp (r ^ 2 / 2))) *
          Real.exp (-(r ^ 2 / 2)) := mul_le_mul_of_nonneg_right
            (hpow.trans (mul_le_mul_of_nonneg_left hfact (by positivity))) (Real.exp_pos _).le
      _ = 4 ^ k * (k.factorial : ℝ) := by
        rw [mul_assoc (4 ^ k), mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]
      _ ≤ _ := le_add_of_nonneg_left (by positivity)

theorem rapid_derivative_bounds_of_factor
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → ℝ) (L : E → E →L[ℝ] ℝ)
    (hf : ContDiff ℝ ∞ f) (hL : L.HasTemperateGrowth)
    (hd : fderiv ℝ f = fun x => f x • L x)
    (hbase : ∀ k : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x : E, (1 + ‖x‖) ^ k * ‖f x‖ ≤ C) :
    ∀ m k : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x : E,
      (1 + ‖x‖) ^ k * ‖iteratedFDeriv ℝ m f x‖ ≤ C := by
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro k
    cases m with
    | zero =>
      simpa only [norm_iteratedFDeriv_zero] using hbase k
    | succ m =>
      obtain ⟨p, D, hD, hDbound⟩ := hL.norm_iteratedFDeriv_le_uniform m
      have hprev (i : Fin (m + 1)) : ∃ C : ℝ, 0 ≤ C ∧ ∀ x : E,
          (1 + ‖x‖) ^ (k + p) * ‖iteratedFDeriv ℝ (i : ℕ) f x‖ ≤ C :=
        ih i i.isLt (k + p)
      choose C hC hCbound using hprev
      let B : ℝ := ∑ i : Fin (m + 1), C i
      have hB : 0 ≤ B := Finset.sum_nonneg fun i _ => hC i
      have hCtotal (i : Fin (m + 1)) : C i ≤ B :=
        Finset.single_le_sum (fun j _ => hC j) (Finset.mem_univ i)
      refine ⟨D * B * (∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ)), by positivity, ?_⟩
      intro x
      have hq : 0 ≤ 1 + ‖x‖ := by positivity
      calc
        _ = (1 + ‖x‖) ^ k *
            ‖iteratedFDeriv ℝ m (fun y => f y • L y) x‖ := by
          rw [← norm_iteratedFDeriv_fderiv, hd]
        _ ≤ (1 + ‖x‖) ^ k * ∑ i ∈ Finset.range (m + 1),
            (m.choose i : ℝ) * ‖iteratedFDeriv ℝ i f x‖ * ‖iteratedFDeriv ℝ (m - i) L x‖ :=
          mul_le_mul_of_nonneg_left (norm_iteratedFDeriv_smul_le hf hL.1 x (by simp)) (pow_nonneg hq k)
        _ = ∑ i ∈ Finset.range (m + 1), (1 + ‖x‖) ^ k *
            ((m.choose i : ℝ) * ‖iteratedFDeriv ℝ i f x‖ * ‖iteratedFDeriv ℝ (m - i) L x‖) :=
          Finset.mul_sum _ _ _
        _ ≤ ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * D * B := by
          apply Finset.sum_le_sum
          intro i hi
          have hib : i < m + 1 := Finset.mem_range.mp hi
          calc
            _ ≤ (1 + ‖x‖) ^ k * ((m.choose i : ℝ) * ‖iteratedFDeriv ℝ i f x‖ *
                (D * (1 + ‖x‖) ^ p)) := by
              gcongr
              exact hDbound (m - i) (Nat.sub_le m i) x
            _ = (m.choose i : ℝ) * D *
                ((1 + ‖x‖) ^ (k + p) * ‖iteratedFDeriv ℝ i f x‖) := by rw [pow_add]; ring
            _ ≤ _ := mul_le_mul_of_nonneg_left
              ((hCbound ⟨i, hib⟩ x).trans (hCtotal ⟨i, hib⟩)) (by positivity)
        _ = _ := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          ring

theorem standardGaussianDensity_weighted_bound (n k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : EuclideanSpace ℝ (Fin n),
      (1 + ‖x‖) ^ k * ‖standardGaussianDensity n x‖ ≤ C := by
  obtain ⟨B, hB, hbound⟩ := gaussian_weighted_scalar_bound k
  let A : ℝ := Real.exp ((n : ℝ) * Real.log ((Real.sqrt (2 * Real.pi))⁻¹))
  refine ⟨A * B, mul_nonneg (Real.exp_pos _).le hB, ?_⟩
  intro x
  have heq : standardGaussianDensity n x = A * Real.exp (-(‖x‖ ^ 2 / 2)) := by
    rw [← Real.exp_log (standardGaussianDensity_pos n x), log_standardGaussianDensity]
    simp only [A, Real.exp_sub, Real.exp_neg, div_eq_mul_inv]
  rw [Real.norm_of_nonneg (standardGaussianDensity_pos n x).le, heq]
  calc
    _ = A * ((1 + ‖x‖) ^ k * Real.exp (-(‖x‖ ^ 2 / 2))) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (hbound ‖x‖ (norm_nonneg x)) (Real.exp_pos _).le

theorem fderiv_standardGaussianDensity (n : ℕ) :
    fderiv ℝ (standardGaussianDensity n) = fun x => standardGaussianDensity n x •
      (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))) (-x) := by
  funext x
  have hdiff := ((standardGaussianDensity_smooth n).differentiable (by simp)).differentiableAt (x := x)
  have hlog : (standardGaussianDensity n x)⁻¹ • fderiv ℝ (standardGaussianDensity n) x =
      (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))) (-x) := by
    rw [← fderiv.log hdiff (standardGaussianDensity_pos n x).ne',
      ← toDual_gradient, gradient_log_standardGaussianDensity]
  have h := congrArg (fun z => standardGaussianDensity n x • z) hlog
  simpa only [smul_smul, mul_inv_cancel₀ (standardGaussianDensity_pos n x).ne', one_smul] using h

theorem standardGaussianDensity_iteratedFDeriv_weighted_bound (n m k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : EuclideanSpace ℝ (Fin n),
      (1 + ‖x‖) ^ k * ‖iteratedFDeriv ℝ m (standardGaussianDensity n) x‖ ≤ C := by
  apply rapid_derivative_bounds_of_factor (standardGaussianDensity n)
    (fun x => (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))) (-x))
    (standardGaussianDensity_smooth n) ?_ (fderiv_standardGaussianDensity n)
    (standardGaussianDensity_weighted_bound n) m k
  exact (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).toContinuousLinearEquiv.hasTemperateGrowth.comp
    Function.HasTemperateGrowth.id'.neg

theorem standardGaussianDensity_iteratedFDeriv_bound (n m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : EuclideanSpace ℝ (Fin n),
      ‖iteratedFDeriv ℝ m (standardGaussianDensity n) x‖ ≤ C := by
  simpa only [pow_zero, one_mul] using standardGaussianDensity_iteratedFDeriv_weighted_bound n m 0

end AffineFKProof
