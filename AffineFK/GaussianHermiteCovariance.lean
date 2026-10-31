module

public import AffineFK.GaussianHermitePairs
public import Mathlib.Data.Multiset.Count

/-!
# Covariance of centred Gaussian coordinate products

The Gram coefficient is evaluated through equality of unordered index
pairs. Mathlib's multiset count extensionality and cons cancellation supply
the combinatorial step. No Gaussian fourth-moment identity is a hypothesis.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory

theorem hermitePairDegree_val (n : ℕ) (j k i : Fin n) :
    (hermitePairDegree n j k i).val = ({j, k} : Multiset (Fin n)).count i := by
  by_cases hjk : j = k <;> by_cases hij : i = j <;> by_cases hik : i = k <;>
    simp_all [hermitePairDegree]

theorem multiset_pair_eq_iff (n : ℕ) (j k l p : Fin n) :
    ({j, k} : Multiset (Fin n)) = {l, p} ↔ (j = l ∧ k = p) ∨ (j = p ∧ k = l) := by
  constructor
  · intro hm
    have hj : j = l ∨ j = p := by
      have hmem : j ∈ ({l, p} : Multiset (Fin n)) := by rw [← hm]; simp
      simpa using hmem
    rcases hj with h | h
    · left
      refine ⟨h, ?_⟩
      subst l
      exact Multiset.singleton_inj.mp ((Multiset.cons_inj_right j).mp hm)
    · right
      refine ⟨h, ?_⟩
      subst p
      rw [Multiset.pair_comm l j] at hm
      exact Multiset.singleton_inj.mp ((Multiset.cons_inj_right j).mp hm)
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · rfl
    · exact Multiset.pair_comm _ _

theorem hermitePairDegree_eq_iff (n : ℕ) (j k l p : Fin n) :
    hermitePairDegree n j k = hermitePairDegree n l p ↔
      (j = l ∧ k = p) ∨ (j = p ∧ k = l) := by
  constructor
  · intro h
    apply (multiset_pair_eq_iff n j k l p).mp
    apply Multiset.ext.mpr
    intro i
    rw [← hermitePairDegree_val n j k i, ← hermitePairDegree_val n l p i]
    exact congrArg Fin.val (congrFun h i)
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · rfl
    · exact hermitePairDegree_swap n _ _

theorem hermiteGram_product (n : ℕ) (α β : Fin n → Fin 3) :
    (∏ i, if α i = β i then (if α i = 2 then 2 else 1) else (0 : ℝ)) =
      if α = β then (∏ i, if α i = 2 then (2 : ℝ) else 1) else 0 := by
  classical
  by_cases h : α = β
  · subst β
    simp
  · rw [ite_eq_right h]
    obtain ⟨i, hi⟩ : ∃ i, α i ≠ β i := by
      by_contra hn
      push Not at hn
      exact h (funext hn)
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])

theorem hermitePair_weight_product (n : ℕ) (j k : Fin n) :
    (∏ i, if hermitePairDegree n j k i = 2 then (2 : ℝ) else 1) =
      if j = k then 2 else 1 := by
  classical
  by_cases h : j = k
  · subst k
    have hp (i : Fin n) : (if hermitePairDegree n j j i = 2 then (2 : ℝ) else 1) =
        if i = j then 2 else 1 := by
      by_cases hi : i = j <;> simp [hermitePairDegree, hi]
    simp_rw [hp]
    simp
  · have hp (i : Fin n) : (if hermitePairDegree n j k i = 2 then (2 : ℝ) else 1) = 1 := by
      by_cases hi : i = j ∨ i = k <;> simp [hermitePairDegree, h, hi]
    simp_rw [hp]
    simp [h]

theorem hermitePair_gram_coefficient (n : ℕ) (j k l p : Fin n) :
    (∏ i, if hermitePairDegree n j k i = hermitePairDegree n l p i then
      (if hermitePairDegree n j k i = 2 then (2 : ℝ) else 1) else 0) =
      (if j = l then 1 else 0) * (if k = p then 1 else 0) +
        (if j = p then 1 else 0) * (if k = l then 1 else 0) := by
  rw [hermiteGram_product, hermitePair_weight_product]
  simp_rw [hermitePairDegree_eq_iff]
  by_cases hjk : j = k <;> by_cases hjl : j = l <;> by_cases hkp : k = p <;>
    by_cases hjp : j = p <;> by_cases hkl : k = l <;> simp_all <;> norm_num

theorem productGaussian_quadratic_pair_covariance (n : ℕ) (j k l p : Fin n) :
    Integrable (fun x : Fin n → ℝ =>
      (x j * x k - if j = k then 1 else 0) * (x l * x p - if l = p then 1 else 0))
      (Measure.pi fun _ => gaussianReal 0 1) ∧
    (∫ x : Fin n → ℝ,
      (x j * x k - if j = k then 1 else 0) * (x l * x p - if l = p then 1 else 0)
      ∂Measure.pi (fun _ => gaussianReal 0 1)) =
      (if j = l then 1 else 0) * (if k = p then 1 else 0) +
        (if j = p then 1 else 0) * (if k = l then 1 else 0) := by
  have h := productGaussian_quadratic_pair_covariance_product n j k l p
  exact ⟨h.1, h.2.trans (hermitePair_gram_coefficient n j k l p)⟩

end AffineFKProof
