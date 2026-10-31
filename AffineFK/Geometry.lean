module

public import Mathlib.Analysis.Convex.Combination
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# Deterministic convex-set steps in the affine reverse Faber–Krahn note

These results formalise only the finite-sum support geometry and the set
geometry of the centred symmetric intersection. They do not assert a
probability support theorem, a volume estimate, or a spectral inequality.

The convex-average proof reuses `Convex.sum_mem`, formalised in Mathlib by
Yury Kudryashov. The preimage/intersection convexity lemmas are from Mathlib's
convexity library (Alexander Bentkamp, Yury Kudryashov, and Yaël Dillies).
The square-root identities are reused from Mathlib. Existing library sources
retain their Apache-2.0 licence and source attribution.
-/

open scoped BigOperators Pointwise

public section

namespace AffineFKProof

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- The mean of a nonempty finite family of points of a convex set lies in the set.
This is the exact average needed before the square-root support dilation. -/
theorem average_mem_convex {D : Set E} (hD : Convex ℝ D)
    {m : ℕ} (hm : 0 < m) (u : Fin m → E) (hu : ∀ i, u i ∈ D) :
    (m : ℝ)⁻¹ • (∑ i, u i) ∈ D := by
  have hmR : 0 < (m : ℝ) := Nat.cast_pos.mpr hm
  have hweights : (∑ _i : Fin m, (m : ℝ)⁻¹) = 1 := by
    simp [hmR.ne']
  have havg := hD.sum_mem
    (t := Finset.univ) (w := fun _i : Fin m => (m : ℝ)⁻¹) (z := u)
    (by intro i hi; exact inv_nonneg.mpr hmR.le)
    hweights (by intro i hi; exact hu i)
  simpa only [← Finset.smul_sum] using havg

/-- For `m > 0`, a normalised sum of `m` points in a convex set lies in its
`sqrt m` dilate. This is the pointwise geometric assertion used in Section 4. -/
theorem normalized_sum_mem_sqrt_dilate {D : Set E} (hD : Convex ℝ D)
    {m : ℕ} (hm : 0 < m) (u : Fin m → E) (hu : ∀ i, u i ∈ D) :
    (Real.sqrt (m : ℝ))⁻¹ • (∑ i, u i) ∈ (Real.sqrt (m : ℝ)) • D := by
  have hmR : 0 < (m : ℝ) := Nat.cast_pos.mpr hm
  have hs : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.mpr hmR
  have hscalar : Real.sqrt (m : ℝ) * (m : ℝ)⁻¹ = (Real.sqrt (m : ℝ))⁻¹ := by
    apply mul_right_cancel₀ hs.ne'
    calc
      (Real.sqrt (m : ℝ) * (m : ℝ)⁻¹) * Real.sqrt (m : ℝ)
          = (Real.sqrt (m : ℝ)) ^ 2 * (m : ℝ)⁻¹ := by ring
      _ = 1 := by rw [Real.sq_sqrt hmR.le, mul_inv_cancel₀ hmR.ne']
      _ = (Real.sqrt (m : ℝ))⁻¹ * Real.sqrt (m : ℝ) :=
        (inv_mul_cancel₀ hs.ne').symm
  refine ⟨(m : ℝ)⁻¹ • (∑ i, u i), average_mem_convex hD hm u hu, ?_⟩
  simp only [smul_smul, hscalar]

omit [Module ℝ E] in
/-- The translate by `-c` of `K ∩ (2c-K)` is invariant under negation.
This assertion is valid for arbitrary sets; convexity is not required. -/
theorem centered_intersection_even (K : Set E) (c z : E) :
    (-z ∈ {w : E | w + c ∈ K ∧ c - w ∈ K}) ↔
      (z ∈ {w : E | w + c ∈ K ∧ c - w ∈ K}) := by
  constructor
  · rintro ⟨h₁, h₂⟩
    constructor
    · simpa only [sub_neg_eq_add, add_comm] using h₂
    · simpa only [sub_eq_add_neg, add_comm] using h₁
  · rintro ⟨h₁, h₂⟩
    constructor
    · simpa only [sub_eq_add_neg, add_comm] using h₂
    · simpa only [sub_neg_eq_add, add_comm] using h₁

/-- The translate by `-c` of the symmetric intersection `K ∩ (2c-K)` is convex
when `K` is convex. This gives only the set-convexity part of the reduction. -/
theorem convex_centered_intersection {K : Set E} (hK : Convex ℝ K) (c : E) :
    Convex ℝ {z : E | z + c ∈ K ∧ c - z ∈ K} := by
  have h₁ : Convex ℝ {z : E | z + c ∈ K} :=
    hK.translate_preimage_left c
  have h₂ : Convex ℝ {z : E | c - z ∈ K} := by
    intro x hx y hy a b ha hb hab
    change c - (a • x + b • y) ∈ K
    have h := hK hx hy ha hb hab
    have heq : a • (c - x) + b • (c - y) = c - (a • x + b • y) := by
      rw [smul_sub, smul_sub, sub_add_sub_comm, ← add_smul, hab, one_smul]
    rwa [heq] at h
  exact h₁.inter h₂

end AffineFKProof
