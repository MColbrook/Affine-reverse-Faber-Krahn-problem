module

public import AffineFK.GaussianKilledNormalization
public import AffineFK.GaussianKilledDomination
public import AffineFK.PositiveLpPowerDomination
public import AffineFK.PositivePowerRayleigh
public import AffineFK.H1GaussianDirichletEnergy

/-!
# Finite Gaussian killing iterates genuinely approach the least Gaussian form

Every hypothesis of the abstract power argument is discharged for the
actual Gaussian operator and literal finite iterates. No eigenfunction,
spectral convergence, or desired energy comparison is assumed.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace

theorem gaussianKillingNormalized_rayleigh_tendsto (n : ℕ)
    (U : Set (EuclideanSpace ℝ (Fin n))) (hU : IsOpen U) (hne : U.Nonempty)
    (hfin : (volume : Measure (EuclideanSpace ℝ (Fin n))) U ≠ ∞)
    (h : ℝ) (hh : 0 < h) :
    Tendsto (fun k => ⟪gaussianKillingNormalizedL2 n U hU.measurableSet hfin h hh k,
      gaussianKilledL2 n U hU.measurableSet h hh
        (gaussianKillingNormalizedL2 n U hU.measurableSet hfin h hh k)⟫)
      atTop (𝓝 ‖gaussianKilledL2 n U hU.measurableSet h hh‖) := by
  let T := gaussianKilledL2 n U hU.measurableSet h hh
  let g := indicatorConstLp 2 hU.measurableSet hfin (1 : ℝ)
  have hpower (k : ℕ) : gaussianKillingIterateL2 n U hU.measurableSet hfin h hh k = (T^k) g := by
    rw [gaussianKillingIterateL2_eq_power,gaussianKillingIterateL2_zero_eq_indicator]
  have hb (k : ℕ) : 0 < ‖(T^k) g‖ := by
    rw [← hpower]
    exact gaussianKillingIterateL2_norm_pos n U hU hne hfin h hh k
  obtain ⟨C,hC,hbase⟩ := gaussianKilledL2_indicator_domination n U hU.measurableSet hfin h hh
  have hp : ∀ m : ℕ, ‖T^(m+1)‖ ≤ C*‖(T^m) g‖ :=
    positive_l2_operator_power_domination volume T
      (gaussianKilledL2_nonneg n U hU.measurableSet h hh) g C hC hbase
  have hd (j : ℕ) : ‖T^(2^j)‖ ≤ C*‖(T^(2^j-1)) g‖ := by
    have he : 2^j-1+1=2^j := Nat.sub_add_cancel (one_le_pow₀ (by norm_num : (1 : ℕ) ≤ 2))
    simpa only [he] using hp (2^j-1)
  have hu (k : ℕ) : positivePowerNormalize T g k =
      gaussianKillingNormalizedL2 n U hU.measurableSet hfin h hh k := by
    unfold positivePowerNormalize gaussianKillingNormalizedL2
    rw [hpower]
  have ht := positivePowerNormalize_rayleigh_tendsto T
    (gaussianKilledL2_selfAdjoint n U hU.measurableSet h hh)
    (gaussianKilledL2_quadratic_nonneg n U hU.measurableSet h hh) g hb C hC hd
  simpa only [hu] using ht

theorem gaussianKillingNormalized_exists_form_le (n : ℕ)
    (U : Set (EuclideanSpace ℝ (Fin n))) (hU : IsOpen U) (hne : U.Nonempty)
    (hfin : (volume : Measure (EuclideanSpace ℝ (Fin n))) U ≠ ∞)
    (h : ℝ) (hh : 0 < h) (ε : ℝ) (hε : 0 < ε)
    (v : Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) (hv : ‖v‖=1)
    (hsupp : ∀ᵐ x ∂volume, x ∉ U → v x=0) :
    ∃ k : ℕ, h1GaussianDirichletForm n h
      (gaussianKillingNormalizedL2 n U hU.measurableSet hfin h hh k) ≤
        h1GaussianDirichletForm n h v+ε := by
  let T := gaussianKilledL2 n U hU.measurableSet h hh
  let u := gaussianKillingNormalizedL2 n U hU.measurableSet hfin h hh
  let δ := ε*h/2
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hq := gaussianKillingNormalized_rayleigh_tendsto n U hU hne hfin h hh
  have hevent : ∀ᶠ k in atTop, ‖T‖-δ < ⟪u k,T (u k)⟫ :=
    (tendsto_order.mp hq).1 _ (sub_lt_self _ hδ)
  obtain ⟨k,hk⟩ := hevent.exists
  have hsup (j : ℕ) : ∀ᵐ x ∂volume, x ∉ U → u j x=0 := by
    filter_upwards [gaussianKillingNormalizedL2_coe n U hU.measurableSet hfin h hh j] with x hx hnot
    rw [hx,gaussianKillingNormalizedFunction_zero_exterior n U hU.measurableSet hfin h hh j x hnot]
  have hform (f : Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin n))))
      (hnorm : ‖f‖=1) (hzero : ∀ᵐ x ∂volume, x ∉ U → f x=0) :
      h1GaussianDirichletForm n h f = (2/h)*(1-⟪f,T f⟫) := by
    rw [h1GaussianDirichletForm,gaussianL2Average_eq_heat n h hh f,hnorm,one_pow]
    rw [gaussianKilledL2_supported_pairing n U hU.measurableSet h hh f hzero]
  have hqv : ⟪v,T v⟫ ≤ ‖T‖ := by
    have hi := real_inner_le_norm v (T v)
    have ht := T.le_opNorm v
    simp only [hv,one_mul,mul_one] at hi ht
    exact hi.trans ht
  refine ⟨k,?_⟩
  rw [hform _ (gaussianKillingNormalizedL2_norm n U hU hne hfin h hh k) (hsup k),
    hform v hv hsupp]
  have hdiff : ⟪v,T v⟫-⟪u k,T (u k)⟫ ≤ δ := by linarith
  have hm := mul_le_mul_of_nonneg_left hdiff (div_pos (by norm_num : (0 : ℝ) < 2) hh).le
  have hc : (2/h)*δ=ε := by dsimp [δ]; field_simp
  rw [hc] at hm
  nlinarith

theorem gaussianKillingNormalized_exists_H1_energy_le (n : ℕ)
    (U : Set (EuclideanSpace ℝ (Fin n))) (hU : IsOpen U) (hne : U.Nonempty)
    (hfin : (volume : Measure (EuclideanSpace ℝ (Fin n))) U ≠ ∞)
    (h : ℝ) (hh : 0 < h) (ε : ℝ) (hε : 0 < ε)
    (v : unweightedSobolevGraph n) (hv : ‖unweightedValue n v‖=1)
    (hsupp : ∀ᵐ x ∂volume, x ∉ U → unweightedValue n v x=0) :
    ∃ k : ℕ, h1GaussianDirichletForm n h
      (gaussianKillingNormalizedL2 n U hU.measurableSet hfin h hh k) ≤
        ‖unweightedGradient n v‖^2+ε := by
  obtain ⟨k,hk⟩ := gaussianKillingNormalized_exists_form_le n U hU hne hfin h hh ε hε _ hv hsupp
  refine ⟨k,hk.trans ?_⟩
  linarith [h1GaussianDirichletForm_le_gradient_energy n h hh v]

end AffineFKProof
