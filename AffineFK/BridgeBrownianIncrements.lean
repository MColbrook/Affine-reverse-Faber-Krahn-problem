module

public import AffineFK.BridgeBrownianLaw
public import Mathlib.Probability.Independence.Process.HasIndepIncrements.Basic

/-!
# Independent vector increments on the actual finite-horizon law

The Gaussian/zero cross-covariance argument follows the proof of Etienne
Marion's `IsPreBrownianReal.hasIndepIncrements` in pinned Mathlib,
`Probability/BrownianMotion/Basic.lean`. Here the index set is `[0,1]`
and the increments are full Euclidean vectors, including dimension zero.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Pointwise BigOperators Topology RealInnerProductSpace

theorem bridgeBrownianLaw_vector_gaussian_process (n : ℕ) :
    IsGaussianProcess (fun t : Icc (0 : ℝ) 1 =>
      fun f : C(Icc (0 : ℝ) 1, EuclideanSpace ℝ (Fin n)) => f t) (bridgeBrownianLaw n) := by
  classical
  apply (bridgeBrownianLaw_gaussian_process n).of_isGaussianProcess
  intro t
  let S : Finset (Icc (0 : ℝ) 1 × Fin n) := Finset.univ.image (fun i : Fin n => (t, i))
  let Q : (S → ℝ) →L[ℝ] (Fin n → ℝ) :=
    ContinuousLinearMap.pi (fun i => ContinuousLinearMap.proj ⟨(t, i), by simp [S]⟩)
  let L : (S → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)).symm.toContinuousLinearMap.comp Q
  refine ⟨S, L, ?_⟩
  intro f
  apply PiLp.ext
  intro i
  rfl

theorem bridgeBrownian_min_increment_zero {m : ℕ} (t : Fin (m + 1) → ℝ)
    (ht : Monotone t) (i j : Fin m) (hij : i ≠ j) :
    min (t i.succ) (t j.succ) - min (t i.succ) (t j.castSucc) -
      min (t i.castSucc) (t j.succ) + min (t i.castSucc) (t j.castSucc) = 0 := by
  have hordered (i j : Fin m) (h : i < j) :
      min (t i.succ) (t j.succ) - min (t i.succ) (t j.castSucc) -
        min (t i.castSucc) (t j.succ) + min (t i.castSucc) (t j.castSucc) = 0 := by
    have h1 : i.succ ≤ j.succ := (Fin.strictMono_succ h).le
    have h2 : i.castSucc ≤ j.succ := Fin.le_of_lt h1
    have h3 : i.castSucc ≤ j.castSucc := Fin.le_castSucc_iff.mpr h1
    rw [min_eq_left (ht h1), min_eq_left (ht h), min_eq_left (ht h2), min_eq_left (ht h3)]
    ring
  rcases lt_or_gt_of_ne hij with h | h
  · exact hordered i j h
  · have hrev := hordered j i h
    rw [min_comm (t j.succ) (t i.succ), min_comm (t j.succ) (t i.castSucc),
      min_comm (t j.castSucc) (t i.succ), min_comm (t j.castSucc) (t i.castSucc)] at hrev
    linarith

theorem bridgeBrownianLaw_hasIndepIncrements (n : ℕ) :
    HasIndepIncrements (fun t : Icc (0 : ℝ) 1 =>
      fun f : C(Icc (0 : ℝ) 1, EuclideanSpace ℝ (Fin n)) => f t) (bridgeBrownianLaw n) := by
  classical
  intro m t ht
  have hG := (bridgeBrownianLaw_vector_gaussian_process n).hasGaussianLaw_increments (t := t)
  have hraw := hG.map_equiv
    (ContinuousLinearEquiv.piCongrRight (fun _ : Fin m =>
      PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)))
  have hind := hraw.iIndepFun_of_covariance_eval (fun i j hij k l => ?_)
  · have hcomp := hind.comp (fun _ => WithLp.toLp 2)
      (fun _ => WithLp.measurable_toLp 2 (Fin n → ℝ))
    exact hcomp
  change cov[fun f : C(Icc (0 : ℝ) 1, EuclideanSpace ℝ (Fin n)) =>
      f (t i.succ) k - f (t i.castSucc) k,
    fun f : C(Icc (0 : ℝ) 1, EuclideanSpace ℝ (Fin n)) =>
      f (t j.succ) l - f (t j.castSucc) l; bridgeBrownianLaw n] = 0
  rw [covariance_fun_sub_fun_sub
    ((bridgeBrownianLaw_gaussian_process n).hasGaussianLaw_eval (t i.succ, k)).memLp_two
    ((bridgeBrownianLaw_gaussian_process n).hasGaussianLaw_eval (t i.castSucc, k)).memLp_two
    ((bridgeBrownianLaw_gaussian_process n).hasGaussianLaw_eval (t j.succ, l)).memLp_two
    ((bridgeBrownianLaw_gaussian_process n).hasGaussianLaw_eval (t j.castSucc, l)).memLp_two]
  simp_rw [bridgeBrownianLaw_coordinate_covariance]
  linear_combination (if k = l then (1 : ℝ) else 0) *
    bridgeBrownian_min_increment_zero (fun i => (t i : ℝ)) (fun _ _ h => ht h) i j hij

end AffineFKProof
