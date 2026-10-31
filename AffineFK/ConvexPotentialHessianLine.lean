module

public import AffineFK.GaussianSmoothedScoreHessianSymmetry
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Nonnegative second derivatives along lines of an actual convex potential

Convexity is restricted to a genuine affine line. Its actual first
derivative is monotone, and the actual derivative of that first derivative
is therefore nonnegative. The two chain-rule computations identify this
with the true second Frechet derivative on the repeated direction.

Convex differentiation reuses Mathlib's proofs by Sebastien Gouezel,
Yury Kudryashov, David Loeffler and contributors (Apache-2.0).
-/

@[expose] public noncomputable section
namespace AffineFKProof
open TopologicalSpace InnerProductSpace
open scoped ContDiff RealInnerProductSpace

theorem convex_potential_line_convex (n : ℕ)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hconv : ConvexOn ℝ Set.univ f)
    (x v : EuclideanSpace ℝ (Fin n)) :
    ConvexOn ℝ Set.univ (fun t : ℝ => f (x + t • v)) := by
  refine ⟨convex_univ, ?_⟩
  intro s _hs t _ht α β hα hβ hsum
  have hpath : α • (x + s • v) + β • (x + t • v) = x + (α * s + β * t) • v := by
    calc
      _ = (α • x + β • x) + ((α * s) • v + (β * t) • v) := by
        simp only [smul_add, smul_smul]
        abel
      _ = (α + β) • x + (α * s + β * t) • v := by simp only [add_smul]
      _ = _ := by rw [hsum, one_smul]
  have h := hconv.2 (Set.mem_univ (x + s • v)) (Set.mem_univ (x + t • v)) hα hβ hsum
  rw [hpath] at h
  simpa only [smul_eq_mul] using h

theorem convex_potential_second_fderiv_nonneg (n : ℕ)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ContDiff ℝ ∞ f)
    (hconv : ConvexOn ℝ Set.univ f) (x v : EuclideanSpace ℝ (Fin n)) :
    0 ≤ fderiv ℝ (fderiv ℝ f) x v v := by
  let g : ℝ → ℝ := fun t => f (x + t • v)
  have hline (t : ℝ) : HasDerivAt (fun s : ℝ => x + s • v) v t := by
    simpa only [Pi.add_apply, id_eq, zero_add, one_smul] using!
      (hasDerivAt_const t x).add ((hasDerivAt_id t).smul_const v)
  have hg (t : ℝ) : HasDerivAt g (fderiv ℝ f (x + t • v) v) t := by
    simpa only [Function.comp_def, g] using
      (((hf.differentiable (by simp)).differentiableAt (x := x + t • v)).hasFDerivAt.comp_hasDerivAt t (hline t))
  have hmon : Monotone (deriv g) := by
    intro s t hst
    exact (convex_potential_line_convex n f hconv x v).monotoneOn_deriv
      (fun u _ => (hg u).differentiableAt) (Set.mem_univ s) (Set.mem_univ t) hst
  have hfirst : deriv g = fun t => fderiv ℝ f (x + t • v) v := funext fun t => (hg t).deriv
  have hfd : ContDiff ℝ ∞ (fderiv ℝ f) := hf.fderiv_right (by simp)
  have hsecondLine : HasDerivAt (fun t : ℝ => fderiv ℝ f (x + t • v))
      (fderiv ℝ (fderiv ℝ f) x v) 0 := by
    have h := (((hfd.differentiable (by simp)).differentiableAt
      (x := x + (0 : ℝ) • v)).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hline 0))
    simpa only [Function.comp_def, zero_smul, add_zero] using h
  have hsecond : HasDerivAt (deriv g) (fderiv ℝ (fderiv ℝ f) x v v) 0 := by
    rw [hfirst]
    simpa only [map_zero, add_zero] using hsecondLine.clm_apply (hasDerivAt_const (0 : ℝ) v)
  have hnonneg : 0 ≤ deriv (deriv g) 0 := hmon.deriv_nonneg
  rwa [hsecond.deriv] at hnonneg

end AffineFKProof
