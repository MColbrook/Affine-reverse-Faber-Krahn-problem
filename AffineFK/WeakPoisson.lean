module

public import Mathlib.Analysis.InnerProductSpace.LaxMilgram
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# The Hilbert-space step in the weak Poisson construction

J and D are the value and gradient maps of a Hilbert graph norm. The two
explicit norm hypotheses express that graph norm and its Poincare inequality.
The construction of the manuscript's weighted Sobolev space and verification
of these hypotheses for it are separate obligations.

This proof reuses Mathlib's Lax--Milgram theorem (Daniel Roca González) and
Riesz representation theorem (Mathlib's inner-product dual-space contributors),
under Apache-2.0.
-/

public section
namespace AffineFKProof
open InnerProductSpace ContinuousLinearMap
open scoped RealInnerProductSpace

/-- The Poincare inequality makes the gradient form coercive for the
Hilbert graph norm, with the explicit constant 1/(P+1). -/
theorem gradient_form_coercive
    {V F G : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [InnerProductSpace ℝ G]
    (J : V →L[ℝ] F) (D : V →L[ℝ] G) (P : ℝ) (hP : 0 ≤ P)
    (hgraph : ∀ v, ‖v‖ ^ 2 = ‖J v‖ ^ 2 + ‖D v‖ ^ 2)
    (hpoincare : ∀ v, ‖J v‖ ^ 2 ≤ P * ‖D v‖ ^ 2) :
    IsCoercive ((innerSL ℝ).bilinearComp D D) := by
  have hP1 : 0 < P + 1 := by linarith
  refine ⟨(P + 1)⁻¹, inv_pos.mpr hP1, ?_⟩
  intro v
  change (P + 1)⁻¹ * ‖v‖ * ‖v‖ ≤ ⟪D v, D v⟫
  rw [real_inner_self_eq_norm_sq]
  have hbase : ‖v‖ ^ 2 ≤ ‖D v‖ ^ 2 * (P + 1) := by
    rw [hgraph]
    nlinarith [hpoincare v]
  calc
    _ = ‖v‖ ^ 2 / (P + 1) := by ring
    _ ≤ _ := (div_le_iff₀ hP1).mpr hbase

/-- Lax--Milgram gives a unique weak solution with a genuine Hilbert source
g. This assertion does not assume existence of the desired solution. -/
theorem weak_gradient_solution
    {V F G : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [NormedAddCommGroup G] [InnerProductSpace ℝ G]
    (J : V →L[ℝ] F) (D : V →L[ℝ] G) (P : ℝ) (hP : 0 ≤ P)
    (hgraph : ∀ v, ‖v‖ ^ 2 = ‖J v‖ ^ 2 + ‖D v‖ ^ 2)
    (hpoincare : ∀ v, ‖J v‖ ^ 2 ≤ P * ‖D v‖ ^ 2) (g : F) :
    ∃! u : V, ∀ v : V, ⟪D u, D v⟫ = ⟪g, J v⟫ := by
  let B : V →L[ℝ] V →L[ℝ] ℝ := (innerSL ℝ).bilinearComp D D
  have hc : IsCoercive B := gradient_form_coercive J D P hP hgraph hpoincare
  let L : V →L[ℝ] ℝ := (innerSL ℝ g).comp J
  let f : V := (toDual ℝ V).symm L
  let u : V := hc.continuousLinearEquivOfBilin.symm f
  have hu : hc.continuousLinearEquivOfBilin u = f :=
    hc.continuousLinearEquivOfBilin.apply_symm_apply f
  have hsol : ∀ v : V, ⟪D u, D v⟫ = ⟪g, J v⟫ := by
    intro v
    calc
      _ = ⟪hc.continuousLinearEquivOfBilin u, v⟫ :=
        (hc.continuousLinearEquivOfBilin_apply u v).symm
      _ = ⟪f, v⟫ := by rw [hu]
      _ = L v := toDual_symm_apply
      _ = _ := rfl
  refine ⟨u, hsol, ?_⟩
  intro w hw
  apply hc.continuousLinearEquivOfBilin.injective
  apply ext_inner_right ℝ
  intro v
  rw [hc.continuousLinearEquivOfBilin_apply, hc.continuousLinearEquivOfBilin_apply]
  exact (hw v).trans (hsol v).symm

/-- Testing the weak equation with its solution and using Poincare gives
the exact energy estimate needed at both Poisson steps. -/
theorem weak_gradient_energy_bound
    {V F G : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [NormedAddCommGroup G] [InnerProductSpace ℝ G]
    (J : V →L[ℝ] F) (D : V →L[ℝ] G) (P : ℝ) (hP : 0 ≤ P)
    (hpoincare : ∀ v, ‖J v‖ ^ 2 ≤ P * ‖D v‖ ^ 2) (g : F) (u : V)
    (hsol : ∀ v : V, ⟪D u, D v⟫ = ⟪g, J v⟫) :
    ‖D u‖ ^ 2 ≤ P * ‖g‖ ^ 2 := by
  have htest : ‖D u‖ ^ 2 ≤ ‖g‖ * ‖J u‖ := by
    rw [← real_inner_self_eq_norm_sq, hsol u]
    exact real_inner_le_norm _ _
  by_cases hzero : ‖D u‖ = 0
  · simpa only [hzero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using
      mul_nonneg hP (sq_nonneg ‖g‖)
  · have hpos : 0 < ‖D u‖ ^ 2 := sq_pos_of_ne_zero hzero
    have hsq := (sq_le_sq₀ (sq_nonneg ‖D u‖)
      (mul_nonneg (norm_nonneg g) (norm_nonneg (J u)))).mpr htest
    have hscale := mul_le_mul_of_nonneg_left (hpoincare u) (sq_nonneg ‖g‖)
    have hproduct : (‖D u‖ ^ 2) * (‖D u‖ ^ 2) ≤ (P * ‖g‖ ^ 2) * (‖D u‖ ^ 2) := by
      nlinarith [hsq, hscale]
    exact (mul_le_mul_iff_left₀ hpos).mp hproduct

/-- The same weak-solution theorem with the canonical inherited structures
on two nested submodules. This avoids recomputing the concrete graph's
inherited instances when the result is specialised to its mean-zero kernel. -/
theorem weak_gradient_solution_nested_submodule
    {H F G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [NormedAddCommGroup G] [InnerProductSpace ℝ G]
    (A : Submodule ℝ H) (S : Submodule ℝ A) [CompleteSpace S]
    (J : S →L[ℝ] F) (D : S →L[ℝ] G) (P : ℝ) (hP : 0 ≤ P)
    (hgraph : ∀ v, ‖v‖ ^ 2 = ‖J v‖ ^ 2 + ‖D v‖ ^ 2)
    (hpoincare : ∀ v, ‖J v‖ ^ 2 ≤ P * ‖D v‖ ^ 2) (g : F) :
    ∃! u : S, (∀ v : S, ⟪D u, D v⟫ = ⟪g, J v⟫) ∧ ‖D u‖ ^ 2 ≤ P * ‖g‖ ^ 2 := by
  obtain ⟨u, hu, hunique⟩ :=
    weak_gradient_solution (V := ↥S) (F := F) (G := G) J D P hP hgraph hpoincare g
  refine ⟨u, ⟨hu, ?_⟩, ?_⟩
  · exact weak_gradient_energy_bound (V := ↥S) (F := F) (G := G) J D P hP hpoincare g u hu
  · intro w hw
    exact hunique w hw.1

end AffineFKProof
