module

public import AffineFK.BridgeKilledL2Representatives
public import AffineFK.BridgeGaussianBessel

/-!
# The genuine killed Brownian contraction on Lebesgue L2

Row integrability and absolute continuity make the construction independent
of L2 representatives. Linearity is proved for the actual row integrals;
the continuous linear map then uses the already proved quadratic bound.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

theorem bridgeKilledIntegral_add (n : ℕ) (t : ℝ) (ht : 0 < t)
    (Ω : Set (EuclideanSpace ℝ (Fin n))) (hΩ : IsOpen Ω)
    (f g : EuclideanSpace ℝ (Fin n) → ℝ) (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) :
    bridgeKilledIntegral n t ht Ω hΩ (fun y => f y + g y) =
      fun x => bridgeKilledIntegral n t ht Ω hΩ f x + bridgeKilledIntegral n t ht Ω hΩ g x := by
  funext x
  exact integral_add ((bridge_memLp_killed_row n t ht Ω hΩ f hf x).integrable (by norm_num))
    ((bridge_memLp_killed_row n t ht Ω hΩ g hg x).integrable (by norm_num))

theorem bridgeKilledIntegral_const_mul (n : ℕ) (t : ℝ) (ht : 0 < t)
    (Ω : Set (EuclideanSpace ℝ (Fin n))) (hΩ : IsOpen Ω)
    (c : ℝ) (f : EuclideanSpace ℝ (Fin n) → ℝ) :
    bridgeKilledIntegral n t ht Ω hΩ (fun y => c * f y) =
      fun x => c * bridgeKilledIntegral n t ht Ω hΩ f x := by
  funext x
  exact integral_const_mul c f

def bridgeKilledL2Linear (n : ℕ) (t : ℝ) (ht : 0 < t)
    (Ω : Set (EuclideanSpace ℝ (Fin n))) (hΩ : IsOpen Ω) :
    Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) →ₗ[ℝ]
      Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) where
  toFun f := (bridgeKilledIntegral_memLp_and_sq_bound_of_memLp n t ht Ω hΩ f (Lp.memLp f)).1.toLp
    (bridgeKilledIntegral n t ht Ω hΩ f)
  map_add' f g := by
    apply Lp.ext
    have he := bridgeKilledIntegral_congr_ae_input n t ht Ω hΩ _ _ (Lp.coeFn_add f g)
    change bridgeKilledIntegral n t ht Ω hΩ (↑(f+g)) =
      bridgeKilledIntegral n t ht Ω hΩ (fun x => f x + g x) at he
    rw [bridgeKilledIntegral_add n t ht Ω hΩ _ _ (Lp.memLp f) (Lp.memLp g)] at he
    filter_upwards [MemLp.coeFn_toLp (bridgeKilledIntegral_memLp_and_sq_bound_of_memLp n t ht Ω hΩ
        (↑(f+g : Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin n))))) (Lp.memLp (f+g))).1,
      Lp.coeFn_add
        ((bridgeKilledIntegral_memLp_and_sq_bound_of_memLp n t ht Ω hΩ f (Lp.memLp f)).1.toLp _)
        ((bridgeKilledIntegral_memLp_and_sq_bound_of_memLp n t ht Ω hΩ g (Lp.memLp g)).1.toLp _),
      MemLp.coeFn_toLp (bridgeKilledIntegral_memLp_and_sq_bound_of_memLp n t ht Ω hΩ f (Lp.memLp f)).1,
      MemLp.coeFn_toLp (bridgeKilledIntegral_memLp_and_sq_bound_of_memLp n t ht Ω hΩ g (Lp.memLp g)).1]
      with x hsum hadd hf hg
    rw [hsum, hadd]
    simp only [Pi.add_apply]
    rw [hf, hg]
    exact congrFun he x
  map_smul' c f := by
    apply Lp.ext
    simp only [RingHom.id_apply]
    have he := bridgeKilledIntegral_congr_ae_input n t ht Ω hΩ _ _ (Lp.coeFn_smul c f)
    change bridgeKilledIntegral n t ht Ω hΩ (↑(c • f)) =
      bridgeKilledIntegral n t ht Ω hΩ (fun x => c * f x) at he
    rw [bridgeKilledIntegral_const_mul] at he
    filter_upwards [MemLp.coeFn_toLp (bridgeKilledIntegral_memLp_and_sq_bound_of_memLp n t ht Ω hΩ
        (↑(c • f : Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin n))))) (Lp.memLp (c • f))).1,
      Lp.coeFn_smul c ((bridgeKilledIntegral_memLp_and_sq_bound_of_memLp n t ht Ω hΩ f (Lp.memLp f)).1.toLp _),
      MemLp.coeFn_toLp (bridgeKilledIntegral_memLp_and_sq_bound_of_memLp n t ht Ω hΩ f (Lp.memLp f)).1]
      with x hsmul hcoe hf
    rw [hsmul, hcoe]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [hf]
    exact congrFun he x

theorem bridgeKilledL2Linear_norm_le (n : ℕ) (t : ℝ) (ht : 0 < t)
    (Ω : Set (EuclideanSpace ℝ (Fin n))) (hΩ : IsOpen Ω)
    (f : Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    ‖bridgeKilledL2Linear n t ht Ω hΩ f‖ ≤ ‖f‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  have h := bridgeKilledIntegral_memLp_and_sq_bound_of_memLp n t ht Ω hΩ f (Lp.memLp f)
  have hf := bridgeRealL2_norm_toLp_sq volume f (Lp.memLp f)
  rw [Lp.toLp_coeFn] at hf
  change ‖h.1.toLp (bridgeKilledIntegral n t ht Ω hΩ f)‖^2 ≤ _
  rw [bridgeRealL2_norm_toLp_sq, hf]
  exact h.2

def bridgeKilledL2Operator (n : ℕ) (t : ℝ) (ht : 0 < t)
    (Ω : Set (EuclideanSpace ℝ (Fin n))) (hΩ : IsOpen Ω) :
    Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) →L[ℝ]
      Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
  (bridgeKilledL2Linear n t ht Ω hΩ).mkContinuous 1
    (fun f => by simpa only [one_mul] using bridgeKilledL2Linear_norm_le n t ht Ω hΩ f)

theorem bridgeKilledL2Operator_coe (n : ℕ) (t : ℝ) (ht : 0 < t)
    (Ω : Set (EuclideanSpace ℝ (Fin n))) (hΩ : IsOpen Ω)
    (f : Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    (bridgeKilledL2Operator n t ht Ω hΩ f : EuclideanSpace ℝ (Fin n) → ℝ) =ᵐ[volume]
      bridgeKilledIntegral n t ht Ω hΩ f :=
  MemLp.coeFn_toLp (bridgeKilledIntegral_memLp_and_sq_bound_of_memLp n t ht Ω hΩ f (Lp.memLp f)).1

end AffineFKProof
