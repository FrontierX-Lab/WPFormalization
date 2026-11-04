import WPFormalization.External.WeilPeterssonGeometry

/-! Explicit classical hyperbolic-geometric objects used by the applications.

`Primitive` means unoriented primitive closed geodesics, including nonsimple ones.
`shortPrimitive` is a complete finite length catalog, not a chosen subset.
For positive genus, `planarSide` records the cusp labels on the unique genus-zero
side of a planar separating simple curve. No planar-side convention at genus zero
is used in the large-genus application. `None` includes every nonplanar curve.

The moduli spaces and WP measure are precisely those of the explicit family G.
The fields below do not assert existence of a concrete instance, any integration
formula, a moment estimate, or an asymptotic conclusion. Their geometric
construction, local finiteness of the primitive length spectrum and Borel
measurability of the counts remain classical phase-two obligations.
-/
noncomputable section
universe u v w
namespace WP.External
open MeasureTheory

structure HyperbolicCurveGeometry {P : PsiTheory}
    (G : WeilPeterssonGeometry.{u,v} P) where
  Primitive : (g n : ℕ) → G.Moduli g n (fun _ => 0) → Type w
  length : ∀ {g n : ℕ} {X : G.Moduli g n (fun _ => 0)}, Primitive g n X → ℝ
  length_pos : ∀ {g n : ℕ} {X : G.Moduli g n (fun _ => 0)} (γ : Primitive g n X),
    0 < length γ
  simple : ∀ {g n : ℕ} {X : G.Moduli g n (fun _ => 0)}, Primitive g n X → Prop
  planarSide : ∀ {g n : ℕ} {X : G.Moduli g n (fun _ => 0)},
    Primitive g n X → Option (Finset (Fin n))
  planar_simple : ∀ {g n : ℕ} {X : G.Moduli g n (fun _ => 0)}
    (γ : Primitive g n X) (S : Finset (Fin n)), planarSide γ = some S → simple γ
  planar_stable : ∀ {g n : ℕ} {X : G.Moduli g n (fun _ => 0)}
    (γ : Primitive g n X) (S : Finset (Fin n)), planarSide γ = some S → 2 ≤ S.card
  shortPrimitive : ∀ {g n : ℕ} (X : G.Moduli g n (fun _ => 0)) (L : ℝ),
    Finset (Primitive g n X)
  mem_shortPrimitive : ∀ {g n : ℕ} (X : G.Moduli g n (fun _ => 0)) (L : ℝ)
    (γ : Primitive g n X), γ ∈ shortPrimitive X L ↔ length γ ≤ L
  measurable_primitiveCount : ∀ (g n : ℕ) (L : ℝ),
    Measurable (fun X : G.Moduli g n (fun _ => 0) =>
      Nat.card {γ : Primitive g n X // length γ ≤ L})
  measurable_planarCount : ∀ (g n k : ℕ) (L : ℝ),
    Measurable (fun X : G.Moduli g n (fun _ => 0) =>
      Nat.card {γ : Primitive g n X // length γ ≤ L ∧
        ∃ S : Finset (Fin n), planarSide γ = some S ∧ S.card = k})

namespace HyperbolicCurveGeometry
variable {P : PsiTheory} {G : WeilPeterssonGeometry.{u,v} P}
    (H : HyperbolicCurveGeometry.{u,v,w} G) {g n : ℕ}

/-- All unoriented primitive closed geodesics up to physical length L. -/
def primitiveCount (X : G.Moduli g n (fun _ => 0)) (L : ℝ) : ℕ :=
  Nat.card {γ : H.Primitive g n X // H.length γ ≤ L}

/-- Curves whose planar side contains exactly k labeled cusps. -/
def planarCount (X : G.Moduli g n (fun _ => 0)) (k : ℕ) (L : ℝ) : ℕ :=
  Nat.card {γ : H.Primitive g n X // H.length γ ≤ L ∧
    ∃ S : Finset (Fin n), H.planarSide γ = some S ∧ S.card = k}

/-- The original two-cusp pants count N_L. -/
def pantsCount (X : G.Moduli g n (fun _ => 0)) (L : ℝ) : ℕ :=
  H.planarCount X 2 L

theorem measurable_pantsCount (L : ℝ) :
    Measurable (fun X : G.Moduli g n (fun _ => 0) => H.pantsCount X L) :=
  H.measurable_planarCount g n 2 L

end HyperbolicCurveGeometry

/-- Normalization of the given geometric WP measure, without choosing an instance.
On stable moduli spaces the total mass is finite. Positivity must be proved or
supplied before this measure may be used as a probability measure. -/
def wpProbability {P : PsiTheory} (G : WeilPeterssonGeometry.{u,v} P) (g n : ℕ) :
    Measure (G.Moduli g n (fun _ => 0)) :=
  (G.wpMeasure g n (fun _ => 0) Set.univ)⁻¹ • G.wpMeasure g n (fun _ => 0)

theorem wpProbability_isProbabilityMeasure {P : PsiTheory}
    (G : WeilPeterssonGeometry.{u,v} P) (g n : ℕ) (hst : Stable g n)
    (hpos : G.wpMeasure g n (fun _ => 0) Set.univ ≠ 0) :
    IsProbabilityMeasure (wpProbability G g n) := by
  apply isProbabilityMeasure_iff.mpr
  simp only [wpProbability, Measure.smul_apply, smul_eq_mul]
  exact ENNReal.inv_mul_cancel hpos (G.finite_volume g n _ hst (by simp))

end WP.External
