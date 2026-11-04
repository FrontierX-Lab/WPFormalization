import WPFormalization.External.HyperbolicCurveGeometry

/-! The actual planar-side cusp mark of an unoriented primitive geodesic. -/
noncomputable section
universe u v w
namespace WP.RandomGeometry
open WP.External
variable {P : PsiTheory} {G : WeilPeterssonGeometry.{u,v} P}
    (H : HyperbolicCurveGeometry.{u,v,w} G) {g n : ℕ} {X : G.Moduli g n (fun _=>0)}

def IsPlanarPrimitive (γ : H.Primitive g n X) : Prop :=
  ∃S : Finset (Fin n),H.planarSide γ=some S

def planarPrimitiveCuspType (γ : H.Primitive g n X) : ℕ :=
  ((H.planarSide γ).getD ∅).card

lemma planarPrimitiveCuspType_of_side (γ : H.Primitive g n X) (S : Finset (Fin n))
    (hS : H.planarSide γ=some S) : planarPrimitiveCuspType H γ=S.card := by
  simp [planarPrimitiveCuspType,hS]

lemma planarPrimitiveCuspType_spec (γ : H.Primitive g n X) (k : ℕ) :
    IsPlanarPrimitive H γ ∧ planarPrimitiveCuspType H γ=k ↔
      ∃S : Finset (Fin n),H.planarSide γ=some S ∧ S.card=k := by
  constructor
  · rintro ⟨⟨S,hS⟩,hk⟩
    exact ⟨S,hS,(planarPrimitiveCuspType_of_side H γ S hS).symm.trans hk⟩
  · rintro ⟨S,hS,hk⟩
    exact ⟨⟨S,hS⟩,(planarPrimitiveCuspType_of_side H γ S hS).trans hk⟩

lemma planarPrimitiveCuspType_ge_two (γ : H.Primitive g n X) (hγ : IsPlanarPrimitive H γ) :
    2≤planarPrimitiveCuspType H γ := by
  obtain ⟨S,hS⟩ := hγ
  rw [planarPrimitiveCuspType_of_side H γ S hS]
  exact H.planar_stable γ S hS

lemma planarPrimitiveCuspType_le_cusps (γ : H.Primitive g n X) (hγ : IsPlanarPrimitive H γ) :
    planarPrimitiveCuspType H γ≤n := by
  obtain ⟨S,hS⟩ := hγ
  rw [planarPrimitiveCuspType_of_side H γ S hS]
  simpa using Finset.card_le_univ S

end WP.RandomGeometry
