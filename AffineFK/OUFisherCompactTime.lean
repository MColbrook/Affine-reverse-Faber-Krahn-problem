module

public import AffineFK.OUDensityPDEScoreJoint
public import AffineFK.GaussianEntropyCalculusTimeIntegration

/-!
# Actual compact spatial Fisher time differentiation

Joint continuity supplies a genuine compact space/time majorant. The
parametric Bochner theorem, followed by the fundamental theorem of
calculus, then differentiates and integrates the compact spatial Fisher
functional. No derivative-integrability or dissipation identity is an
input. Spatial removal of the compact test is separate.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory Filter TopologicalSpace Set
open scoped Topology Distributions Interval

theorem positive_time_compact_weight_local_bound (n : ℕ)
    (D : ℝ → EuclideanSpace ℝ (Fin n) → ℝ)
    (hD : Continuous (fun p : {t : ℝ // 0 < t} × EuclideanSpace ℝ (Fin n) => D p.1.val p.2))
    (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ)) (t : ℝ) (ht : 0 < t) :
    ∃ S : Set ℝ, S ∈ 𝓝 t ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ r ∈ S, 0 < r ∧ ∀ x ∈ tsupport φ, ‖D r x‖ ≤ C := by
  let T := Icc (t / 2) (t + 1)
  let X := tsupport φ
  have hT : IsCompact T := isCompact_Icc
  have hX : IsCompact X := φ.hasCompactSupport
  have : CompactSpace T := isCompact_iff_compactSpace.mp hT
  have : CompactSpace X := isCompact_iff_compactSpace.mp hX
  let Q := T × X
  let W : Q → {r : ℝ // 0 < r} × EuclideanSpace ℝ (Fin n) :=
    fun q => (⟨q.1.val, (half_pos ht).trans_le q.1.property.1⟩, q.2.val)
  have hW : Continuous W := by dsimp [W, Q, T, X]; fun_prop
  obtain ⟨C, hC, hCb⟩ := (isCompact_univ.image (hD.comp hW)).isBounded.exists_pos_norm_le
  refine ⟨Ioo (t / 2) (t + 1), Ioo_mem_nhds (half_lt_self ht) (lt_add_one t), C, hC.le, ?_⟩
  intro r hr
  refine ⟨(half_pos ht).trans hr.1, ?_⟩
  intro x hx
  exact hCb (D r x) ⟨(⟨r, hr.1.le, hr.2.le⟩, ⟨x, hx⟩), Set.mem_univ _, rfl⟩

theorem positive_time_compact_integral_hasDerivAt (n : ℕ)
    (F D : ℝ → EuclideanSpace ℝ (Fin n) → ℝ)
    (hF : Continuous (fun p : {t : ℝ // 0 < t} × EuclideanSpace ℝ (Fin n) => F p.1.val p.2))
    (hD : Continuous (fun p : {t : ℝ // 0 < t} × EuclideanSpace ℝ (Fin n) => D p.1.val p.2))
    (hdiff : ∀ r : ℝ, 0 < r → ∀ x, HasDerivAt (fun s => F s x) (D r x) r)
    (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ)) (t : ℝ) (ht : 0 < t) :
    Integrable (fun x => φ x * D t x) ∧
    HasDerivAt (fun r => ∫ x, φ x * F r x) (∫ x, φ x * D t x) t := by
  let E := EuclideanSpace ℝ (Fin n)
  have hFc (r : ℝ) (hr : 0 < r) : Continuous (F r) := by
    simpa only [Function.comp_def] using hF.comp
      (continuous_const.prodMk continuous_id :
        Continuous (fun x : E => ((⟨r, hr⟩ : {u : ℝ // 0 < u}), x)))
  have hDc (r : ℝ) (hr : 0 < r) : Continuous (D r) := by
    simpa only [Function.comp_def] using hD.comp
      (continuous_const.prodMk continuous_id :
        Continuous (fun x : E => ((⟨r, hr⟩ : {u : ℝ // 0 < u}), x)))
  obtain ⟨S, hS, C, hC, hCb⟩ := positive_time_compact_weight_local_bound n D hD φ t ht
  have hFi : Integrable (fun x => φ x * F t x) :=
    (φ.continuous.mul (hFc t ht)).integrable_of_hasCompactSupport φ.hasCompactSupport.mul_right
  have hboundi : Integrable (fun x : E => C * ‖φ x‖) :=
    (φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport).norm.const_mul C
  have hbound : ∀ᵐ x ∂(volume : Measure E), ∀ r ∈ S, ‖φ x * D r x‖ ≤ C * ‖φ x‖ :=
    Filter.Eventually.of_forall fun x r hr => by
      by_cases hx : φ x = 0
      · simp only [hx, zero_mul, norm_zero, mul_zero, le_refl]
      · rw [norm_mul]
        exact (mul_le_mul_of_nonneg_left ((hCb r hr).2 x (subset_tsupport φ hx)) (norm_nonneg _)).trans_eq (mul_comm _ _)
  exact hasDerivAt_integral_of_dominated_loc_of_deriv_le hS
    ((show ∀ᶠ r in 𝓝 t, r ∈ S from hS).mono fun r hr =>
      (φ.continuous.mul (hFc r (hCb r hr).1)).aestronglyMeasurable)
    hFi (φ.continuous.mul (hDc t ht)).aestronglyMeasurable hbound hboundi
    (Filter.Eventually.of_forall fun x r hr => (hdiff r (hCb r hr).1 x).const_mul (φ x))

theorem positive_time_compact_integral_time_integral (n : ℕ)
    (F D : ℝ → EuclideanSpace ℝ (Fin n) → ℝ)
    (hF : Continuous (fun p : {t : ℝ // 0 < t} × EuclideanSpace ℝ (Fin n) => F p.1.val p.2))
    (hD : Continuous (fun p : {t : ℝ // 0 < t} × EuclideanSpace ℝ (Fin n) => D p.1.val p.2))
    (hdiff : ∀ r : ℝ, 0 < r → ∀ x, HasDerivAt (fun s => F s x) (D r x) r)
    (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ))
    (s t : ℝ) (hs : 0 < s) (hst : s ≤ t) :
    IntervalIntegrable (fun r => ∫ x, φ x * D r x) volume s t ∧
      (∫ r in s..t, ∫ x, φ x * D r x) = (∫ x, φ x * F t x) - ∫ x, φ x * F s x := by
  have hφ : Integrable (fun x : EuclideanSpace ℝ (Fin n) => ‖φ x‖) :=
    (φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport).norm
  apply positive_time_integral_of_locally_bounded_derivative
    (fun r => ∫ x, φ x * F r x) (fun r => ∫ x, φ x * D r x)
    (fun r hr => (positive_time_compact_integral_hasDerivAt n F D hF hD hdiff φ r hr).2) ?_ s t hs hst
  intro r hr
  obtain ⟨S, hS, C, hC, hCb⟩ := positive_time_compact_weight_local_bound n D hD φ r hr
  refine ⟨S, hS, C * (∫ x, ‖φ x‖), by positivity, ?_⟩
  intro u hu
  have hb (x : EuclideanSpace ℝ (Fin n)) : ‖φ x * D u x‖ ≤ C * ‖φ x‖ := by
    by_cases hx : φ x = 0
    · simp only [hx, zero_mul, norm_zero, mul_zero, le_refl]
    · rw [norm_mul]
      exact (mul_le_mul_of_nonneg_left ((hCb u hu).2 x (subset_tsupport φ hx)) (norm_nonneg _)).trans_eq (mul_comm _ _)
  exact (norm_integral_le_of_norm_le (hφ.const_mul C) (Filter.Eventually.of_forall hb)).trans_eq
    (integral_const_mul _ _)

theorem ou_ordinary_fisher_compact_time_integral (n : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
    (hU : Integrable (fun u : EuclideanSpace ℝ (Fin n) => u) ν)
    (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin n))), ℝ))
    (s t : ℝ) (hs : 0 < s) (hst : s ≤ t) :
    let ρ : ℝ → EuclideanSpace ℝ (Fin n) → ℝ := fun r =>
      gaussianSmoothingDensity n ν (Real.exp (-r)) (Real.sqrt (1 - Real.exp (-2 * r)))
    let score : ℝ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) :=
      fun r => gradient (fun x => Real.log (ρ r x))
    let D : ℝ → EuclideanSpace ℝ (Fin n) → ℝ := fun r x =>
      2 * (∑ i : Fin n, score r x i * ouOrdinaryScoreTimeDerivative n ν r x i) * ρ r x +
        ‖score r x‖ ^ 2 * ouDensityTimeDerivative n ν r x
    IntervalIntegrable (fun r => ∫ x, φ x * D r x) volume s t ∧
      (∫ r in s..t, ∫ x, φ x * D r x) =
        (∫ x, φ x * (‖score t x‖ ^ 2 * ρ t x)) - ∫ x, φ x * (‖score s x‖ ^ 2 * ρ s x) := by
  exact positive_time_compact_integral_time_integral n _ _
    (ou_ordinary_fisher_density_joint_continuous n ν)
    (ou_ordinary_fisher_density_time_derivative_joint_continuous n ν hU)
    (fun r hr x => ou_ordinary_fisher_density_hasDerivAt n ν hU r hr x) φ s t hs hst

end AffineFKProof
