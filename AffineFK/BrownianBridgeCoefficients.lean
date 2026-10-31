module

public import AffineFK.Exponents
public import Mathlib.Probability.Independence.InfinitePi
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Basic.ENNReal.BigOperators
public import Mathlib.MeasureTheory.Group.Pointwise

/-!
# Independent Gaussian coefficients in the bridge argument

The probability space below is an actual countable product of finite
families of standard Gaussian vectors. Independence is proved from the
product law. No Brownian or killed-kernel representation is assumed or
claimed in this file. The infinite-product estimate reuses Mathlib's
`Measure.infinitePi_pi_univ` and `ENNReal.tprod_eq_iInf_prod`, including
their continuity-of-probability proofs (Mathlib contributors, Apache-2.0).
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal BigOperators Pointwise

theorem probability_infinite_product_exp_lower
    {X : ℕ → Type*} [∀ j, MeasurableSpace (X j)]
    (μ : ∀ j, Measure (X j)) [∀ j, IsProbabilityMeasure (μ j)]
    (S : ∀ j, Set (X j)) (hS : ∀ j, MeasurableSet (S j))
    (c : ℕ → ℝ) (hc : ∀ j, 0 ≤ c j) (hs : Summable c)
    (hcost : ∀ j, ENNReal.ofReal (Real.exp (-c j)) ≤ μ j (S j)) :
    ENNReal.ofReal (Real.exp (-(∑' j, c j))) ≤
      Measure.infinitePi μ (Set.univ.pi S) := by
  rw [Measure.infinitePi_pi_univ μ hS,
    ENNReal.tprod_eq_iInf_prod (fun j => prob_le_one)]
  apply le_iInf
  intro s
  calc
    ENNReal.ofReal (Real.exp (-(∑' j, c j))) ≤
        ENNReal.ofReal (Real.exp (-(∑ j ∈ s, c j))) := by
      apply ENNReal.ofReal_le_ofReal
      apply Real.exp_le_exp.mpr
      exact neg_le_neg (hs.sum_le_tsum s (fun j _ => hc j))
    _ = ∏ j ∈ s, ENNReal.ofReal (Real.exp (-c j)) := by
      rw [← Finset.sum_neg_distrib, Real.exp_sum,
        ENNReal.ofReal_prod_of_nonneg (fun _ _ => (Real.exp_pos _).le)]
    _ ≤ ∏ j ∈ s, μ j (S j) := Finset.prod_le_prod' (fun j _ => hcost j)

/-- The genuine coefficient probability space, with `2^j` vectors at level `j`. -/
def bridgeCoefficientMeasure (n : ℕ) :
    Measure (∀ j : ℕ, Fin (2 ^ j) → EuclideanSpace ℝ (Fin n)) :=
  Measure.infinitePi (fun j : ℕ => Measure.infinitePi (fun _ : Fin (2 ^ j) =>
    stdGaussian (EuclideanSpace ℝ (Fin n))))

instance bridgeCoefficientMeasure_probability (n : ℕ) :
    IsProbabilityMeasure (bridgeCoefficientMeasure n) := by
  unfold bridgeCoefficientMeasure
  infer_instance

/-- All levels and positions are independent under the actual product law. -/
theorem bridgeCoefficientMeasure_independent (n : ℕ) :
    iIndepFun (fun (i : Σ j : ℕ, Fin (2 ^ j))
      (ω : ∀ j : ℕ, Fin (2 ^ j) → EuclideanSpace ℝ (Fin n)) => ω i.1 i.2)
      (bridgeCoefficientMeasure n) := by
  exact iIndepFun_uncurry_infinitePi
    (fun j (_ : Fin (2 ^ j)) => stdGaussian (EuclideanSpace ℝ (Fin n)))
    (X := fun _ _ x => x) (by fun_prop)

/-- Every coefficient has exactly the standard Gaussian vector law. -/
theorem bridgeCoefficientMeasure_hasLaw (n j : ℕ) (k : Fin (2 ^ j)) :
    HasLaw (fun ω : ∀ j : ℕ, Fin (2 ^ j) → EuclideanSpace ℝ (Fin n) => ω j k)
      (stdGaussian (EuclideanSpace ℝ (Fin n))) (bridgeCoefficientMeasure n) := by
  exact ((measurePreserving_eval_infinitePi
    (fun _ : Fin (2 ^ j) => stdGaussian (EuclideanSpace ℝ (Fin n))) k).comp
    (measurePreserving_eval_infinitePi
      (fun j : ℕ => Measure.infinitePi (fun _ : Fin (2 ^ j) =>
        stdGaussian (EuclideanSpace ℝ (Fin n)))) j)).hasLaw

theorem probability_finite_product_exp_lower
    {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
    (S : Set X) (hS : MeasurableSet S) (c : ℝ)
    (hcost : ENNReal.ofReal (Real.exp (-c)) ≤ μ S) (m : ℕ) :
    ENNReal.ofReal (Real.exp (-(m : ℝ) * c)) ≤
      Measure.infinitePi (fun _ : Fin m => μ) (Set.univ.pi (fun _ => S)) := by
  rw [Measure.infinitePi_eq_pi, Measure.pi_pi]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  calc
    ENNReal.ofReal (Real.exp (-(m : ℝ) * c)) =
        (ENNReal.ofReal (Real.exp (-c))) ^ m := by
      rw [← ENNReal.ofReal_pow (Real.exp_pos _).le, ← Real.exp_nat_mul]
      congr 2
      ring
    _ ≤ (μ S) ^ m := pow_le_pow_left' hcost m

/-- The event uses the literal dilates `2^(a*j) D` for every coefficient. -/
def bridgeCoefficientEvent (n : ℕ) (D : Set (EuclideanSpace ℝ (Fin n))) (a : ℝ) :
    Set (∀ j : ℕ, Fin (2 ^ j) → EuclideanSpace ℝ (Fin n)) :=
  Set.univ.pi (fun j : ℕ => Set.univ.pi
    (fun _ : Fin (2 ^ j) => ((2 : ℝ) ^ (a * (j : ℝ))) • D))

/-- The actual infinite coefficient event has the manuscript's exponential lower bound.
The profile is expressed without taking the real logarithm at zero.
The Brownian-law identification is a separate obligation. -/
theorem bridgeCoefficientEvent_probability_lower
    (n : ℕ) (D : Set (EuclideanSpace ℝ (Fin n))) (hD : MeasurableSet D)
    (p a A : ℝ) (hp : 2 < p) (ha : 1 / p < a) (hupper : a < 1 / 2) (hA : 0 ≤ A)
    (hprofile : ∀ t : ℝ, 1 ≤ t →
      ENNReal.ofReal (Real.exp (-A * t ^ (-p))) ≤
        stdGaussian (EuclideanSpace ℝ (Fin n)) (t • D)) :
    ENNReal.ofReal (Real.exp (-A / (1 - (2 : ℝ) ^ (1 - a * p)))) ≤
      bridgeCoefficientMeasure n (bridgeCoefficientEvent n D a) := by
  let c : ℕ → ℝ := fun j => A * (2 : ℝ) ^ ((1 - a * p) * (j : ℝ))
  have hc (j : ℕ) : 0 ≤ c j := mul_nonneg hA (Real.rpow_pos_of_pos (by norm_num) _).le
  have hs : Summable c := (bridge_series_summable p a hp ha hupper).1.mul_left A
  have hexact : (∑' j, c j) = A / (1 - (2 : ℝ) ^ (1 - a * p)) := by
    rw [show c = (fun j : ℕ => A * (2 : ℝ) ^ ((1 - a * p) * (j : ℝ))) from rfl,
      tsum_mul_left, (bridge_series_values p a hp ha hupper).1, div_eq_mul_inv]
  have ha0 : 0 < a := lt_trans (one_div_pos.mpr (by linarith)) ha
  have hdilate (j : ℕ) : MeasurableSet (((2 : ℝ) ^ (a * (j : ℝ))) • D) := by
    exact hD.const_smul₀ _
  have hlevel (j : ℕ) : ENNReal.ofReal (Real.exp (-c j)) ≤
      Measure.infinitePi (fun _ : Fin (2 ^ j) => stdGaussian (EuclideanSpace ℝ (Fin n)))
        (Set.univ.pi (fun _ : Fin (2 ^ j) => ((2 : ℝ) ^ (a * (j : ℝ))) • D)) := by
    have hb : 1 ≤ (2 : ℝ) ^ (a * (j : ℝ)) :=
      Real.one_le_rpow (by norm_num) (mul_nonneg ha0.le (Nat.cast_nonneg _))
    have h := probability_finite_product_exp_lower
      (stdGaussian (EuclideanSpace ℝ (Fin n))) _ (hdilate j)
      (A * ((2 : ℝ) ^ (a * (j : ℝ))) ^ (-p)) (by simpa [neg_mul] using hprofile _ hb) (2 ^ j)
    have heq : ((2 ^ j : ℕ) : ℝ) *
        (A * ((2 : ℝ) ^ (a * (j : ℝ))) ^ (-p)) = c j := by
      rw [Nat.cast_pow, Nat.cast_ofNat, ← Real.rpow_natCast,
        ← Real.rpow_mul (by norm_num : 0 ≤ (2 : ℝ))]
      dsimp [c]
      rw [mul_left_comm, mul_assoc, ← Real.rpow_add (by norm_num : 0 < (2 : ℝ))]
      congr 2
      ring
    simpa only [heq, neg_mul] using h
  have h := probability_infinite_product_exp_lower
    (fun j : ℕ => Measure.infinitePi (fun _ : Fin (2 ^ j) => stdGaussian (EuclideanSpace ℝ (Fin n))))
    (fun j => Set.univ.pi (fun _ : Fin (2 ^ j) => ((2 : ℝ) ^ (a * (j : ℝ))) • D))
    (fun j => MeasurableSet.univ_pi (fun _ => hdilate j)) c hc hs hlevel
  simpa only [hexact, neg_div, bridgeCoefficientMeasure, bridgeCoefficientEvent] using h

end AffineFKProof
