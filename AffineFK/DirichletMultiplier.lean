module

public import AffineFK.H1MultiplierAmbient

/-!
# Genuine smooth bounded multiplication on H1 and H0^1

The proved ambient product operator preserves the actual compact smooth
core. Continuity then preserves its closure, first globally and then with
support inside the given open set. The resulting H0^1 element has the
actual product value and actual weak product-rule gradient almost
everywhere. No admissibility or product-rule conclusion is a premise.
-/

@[expose] public noncomputable section
namespace AffineFKProof
open MeasureTheory TopologicalSpace
open scoped ContDiff

theorem h1MultiplierAmbient_preserves_graph (n : ℕ)
    (m : EuclideanSpace ℝ (Fin n) → ℝ) (hm : ContDiff ℝ ∞ m) (C0 C1 : ℝ)
    (hb0 : ∀ x, ‖m x‖ ≤ C0) (hb1 : ∀ x, ‖gradient m x‖ ≤ C1)
    (v : SobolevAmbient (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hv : v ∈ unweightedSobolevGraph n) :
    h1MultiplierAmbient n m hm C0 C1 hb0 hb1 v ∈ unweightedSobolevGraph n := by
  let L := h1MultiplierAmbient n m hm C0 C1 hb0 hb1
  have hcore : ((unweightedSmoothPair n).range).map L.toLinearMap ≤
      (unweightedSmoothPair n).range := by
    rintro z ⟨y, ⟨φ, rfl⟩, rfl⟩
    exact ⟨h1MultiplyTest n ⊤ m hm φ, (h1MultiplierAmbient_smooth_pair n m hm C0 C1 hb0 hb1 φ).symm⟩
  have h := (((unweightedSmoothPair n).range).topologicalClosure_map L).trans
    (Submodule.topologicalClosure_mono hcore)
  exact h ⟨v, hv, rfl⟩

def h1Multiplier (n : ℕ) (m : EuclideanSpace ℝ (Fin n) → ℝ)
    (hm : ContDiff ℝ ∞ m) (C0 C1 : ℝ)
    (hb0 : ∀ x, ‖m x‖ ≤ C0) (hb1 : ∀ x, ‖gradient m x‖ ≤ C1) :
    unweightedSobolevGraph n →L[ℝ] unweightedSobolevGraph n :=
  ((h1MultiplierAmbient n m hm C0 C1 hb0 hb1).comp (unweightedSobolevGraph n).subtypeL).codRestrict
    (unweightedSobolevGraph n) (fun v => h1MultiplierAmbient_preserves_graph n m hm C0 C1 hb0 hb1 v v.property)

theorem h1Multiplier_value (n : ℕ) (m : EuclideanSpace ℝ (Fin n) → ℝ)
    (hm : ContDiff ℝ ∞ m) (C0 C1 : ℝ)
    (hb0 : ∀ x, ‖m x‖ ≤ C0) (hb1 : ∀ x, ‖gradient m x‖ ≤ C1)
    (v : unweightedSobolevGraph n) :
    (unweightedValue n (h1Multiplier n m hm C0 C1 hb0 hb1 v) :
      EuclideanSpace ℝ (Fin n) → ℝ) =ᵐ[volume] fun x => m x * unweightedValue n v x :=
  h1MultiplierAmbient_value n m hm C0 C1 hb0 hb1 v

theorem h1Multiplier_gradient (n : ℕ) (m : EuclideanSpace ℝ (Fin n) → ℝ)
    (hm : ContDiff ℝ ∞ m) (C0 C1 : ℝ)
    (hb0 : ∀ x, ‖m x‖ ≤ C0) (hb1 : ∀ x, ‖gradient m x‖ ≤ C1)
    (v : unweightedSobolevGraph n) :
    (unweightedGradient n (h1Multiplier n m hm C0 C1 hb0 hb1 v) :
      EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) =ᵐ[volume]
      fun x => m x • unweightedGradient n v x + unweightedValue n v x • gradient m x :=
  h1MultiplierAmbient_gradient n m hm C0 C1 hb0 hb1 v

theorem h1Multiplier_dirichlet_test (n : ℕ) (U : Opens (EuclideanSpace ℝ (Fin n)))
    (m : EuclideanSpace ℝ (Fin n) → ℝ) (hm : ContDiff ℝ ∞ m) (C0 C1 : ℝ)
    (hb0 : ∀ x, ‖m x‖ ≤ C0) (hb1 : ∀ x, ‖gradient m x‖ ≤ C1)
    (φ : TestFunction U ℝ ⊤) :
    h1Multiplier n m hm C0 C1 hb0 hb1 (dirichletTestToH1 n U φ) =
      dirichletTestToH1 n U (h1MultiplyTest n U m hm φ) := by
  apply Subtype.ext
  change h1MultiplierAmbient n m hm C0 C1 hb0 hb1
      (unweightedSmoothPair n (dirichletTestToTop n U φ)) =
    unweightedSmoothPair n (dirichletTestToTop n U (h1MultiplyTest n U m hm φ))
  rw [h1MultiplierAmbient_smooth_pair]
  congr 1

theorem h1Multiplier_preserves_dirichlet (n : ℕ) (U : Opens (EuclideanSpace ℝ (Fin n)))
    (m : EuclideanSpace ℝ (Fin n) → ℝ) (hm : ContDiff ℝ ∞ m) (C0 C1 : ℝ)
    (hb0 : ∀ x, ‖m x‖ ≤ C0) (hb1 : ∀ x, ‖gradient m x‖ ≤ C1)
    (v : unweightedSobolevGraph n) (hv : v ∈ dirichletSobolev n U) :
    h1Multiplier n m hm C0 C1 hb0 hb1 v ∈ dirichletSobolev n U := by
  let L := h1Multiplier n m hm C0 C1 hb0 hb1
  have hcore : ((dirichletTestToH1 n U).range).map L.toLinearMap ≤
      (dirichletTestToH1 n U).range := by
    rintro z ⟨y, ⟨φ, rfl⟩, rfl⟩
    exact ⟨h1MultiplyTest n U m hm φ, (h1Multiplier_dirichlet_test n U m hm C0 C1 hb0 hb1 φ).symm⟩
  have h := (((dirichletTestToH1 n U).range).topologicalClosure_map L).trans
    (Submodule.topologicalClosure_mono hcore)
  exact h ⟨v, hv, rfl⟩

def dirichletMultiplier (n : ℕ) (U : Opens (EuclideanSpace ℝ (Fin n)))
    (m : EuclideanSpace ℝ (Fin n) → ℝ) (hm : ContDiff ℝ ∞ m) (C0 C1 : ℝ)
    (hb0 : ∀ x, ‖m x‖ ≤ C0) (hb1 : ∀ x, ‖gradient m x‖ ≤ C1) :
    dirichletSobolev n U →L[ℝ] dirichletSobolev n U :=
  ((h1Multiplier n m hm C0 C1 hb0 hb1).domRestrict (dirichletSobolev n U)).codRestrict
    (dirichletSobolev n U) (fun v => h1Multiplier_preserves_dirichlet n U m hm C0 C1 hb0 hb1 v v.property)

theorem dirichletMultiplier_value (n : ℕ) (U : Opens (EuclideanSpace ℝ (Fin n)))
    (m : EuclideanSpace ℝ (Fin n) → ℝ) (hm : ContDiff ℝ ∞ m) (C0 C1 : ℝ)
    (hb0 : ∀ x, ‖m x‖ ≤ C0) (hb1 : ∀ x, ‖gradient m x‖ ≤ C1)
    (v : dirichletSobolev n U) :
    (dirichletValue n U (dirichletMultiplier n U m hm C0 C1 hb0 hb1 v) :
      EuclideanSpace ℝ (Fin n) → ℝ) =ᵐ[volume] fun x => m x * dirichletValue n U v x :=
  h1Multiplier_value n m hm C0 C1 hb0 hb1 v

theorem dirichletMultiplier_gradient (n : ℕ) (U : Opens (EuclideanSpace ℝ (Fin n)))
    (m : EuclideanSpace ℝ (Fin n) → ℝ) (hm : ContDiff ℝ ∞ m) (C0 C1 : ℝ)
    (hb0 : ∀ x, ‖m x‖ ≤ C0) (hb1 : ∀ x, ‖gradient m x‖ ≤ C1)
    (v : dirichletSobolev n U) :
    (dirichletGradient n U (dirichletMultiplier n U m hm C0 C1 hb0 hb1 v) :
      EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) =ᵐ[volume]
      fun x => m x • dirichletGradient n U v x + dirichletValue n U v x • gradient m x :=
  h1Multiplier_gradient n m hm C0 C1 hb0 hb1 v

end AffineFKProof
