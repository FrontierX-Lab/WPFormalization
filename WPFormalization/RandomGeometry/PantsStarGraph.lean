import Mathlib
noncomputable section
namespace WP.RandomGeometry

def StarRelation {V E : Type*} (root leaf : E → V) (a b : V) : Prop :=
  ∃ e, (a = root e ∧ b = leaf e) ∨ (a = leaf e ∧ b = root e)

lemma star_reachable {V E : Type*} (root leaf : E → V)
    (hleaf : Function.Injective leaf) (hsep : ∀ i j, root i ≠ leaf j)
    (e0 : E) {v : V}
    (hp : Relation.ReflTransGen (StarRelation root leaf) (root e0) v) :
    v = root e0 ∨ ∃ e, v = leaf e ∧ root e = root e0 := by
  induction hp with
  | refl => exact Or.inl rfl
  | @tail b c hb hbc ih =>
    rcases hbc with ⟨e, (⟨he, hc⟩ | ⟨he, hc⟩)⟩
    · rcases ih with hi | ⟨i, hi, hri⟩
      · exact Or.inr ⟨e, hc, he.symm.trans hi⟩
      · exact (hsep e i (he.symm.trans hi)).elim
    · rcases ih with hi | ⟨i, hi, hri⟩
      · exact (hsep e0 e (hi.symm.trans he)).elim
      · have hie : i = e := hleaf (hi.symm.trans he)
        subst i
        exact Or.inl (hc.trans hri)

lemma connected_leaf_graph_star {V E : Type*} (root leaf : E → V)
    (hleaf : Function.Injective leaf) (hsep : ∀ i j, root i ≠ leaf j)
    (e0 : E) (hconnected : ∀ v : V,
      Relation.ReflTransGen (StarRelation root leaf) (root e0) v) :
    (∀ e, root e = root e0) ∧ (∀ v : V, v = root e0 ∨ ∃ e, v = leaf e) := by
  constructor
  · intro e
    rcases star_reachable root leaf hleaf hsep e0 (hconnected (root e)) with h | ⟨i,h,_⟩
    · exact h
    · exact (hsep e i h).elim
  · intro v
    rcases star_reachable root leaf hleaf hsep e0 (hconnected v) with h | ⟨i,h,_⟩
    · exact Or.inl h
    · exact Or.inr ⟨i,h⟩

/-- A connected graph all of whose edges has a distinct leaf is an actual star,
including its exact number of vertices and the distinguished root. -/
def connectedLeafGraphEquiv {V E : Type*} (root leaf : E → V)
    (hleaf : Function.Injective leaf) (hsep : ∀ i j, root i ≠ leaf j)
    (e0 : E) (hconnected : ∀ v : V,
      Relation.ReflTransGen (StarRelation root leaf) (root e0) v) :
    Option E ≃ V := by
  classical
  let f : Option E → V := fun e => match e with | none => root e0 | some i => leaf i
  have hf : Function.Bijective f := by
    constructor
    · intro a b hab
      cases a with
      | none => cases b with
        | none => rfl
        | some j => exact (hsep e0 j hab).elim
      | some i => cases b with
        | none => exact (hsep e0 i hab.symm).elim
        | some j => exact congrArg some (hleaf hab)
    · intro v
      rcases (connected_leaf_graph_star root leaf hleaf hsep e0 hconnected).2 v with h | ⟨i,h⟩
      · exact ⟨none,h.symm⟩
      · exact ⟨some i,h.symm⟩
  exact Equiv.ofBijective f hf

@[simp] lemma connectedLeafGraphEquiv_none {V E : Type*} (root leaf : E → V)
    (hleaf : Function.Injective leaf) (hsep : ∀ i j, root i ≠ leaf j)
    (e0 : E) (hconnected : ∀ v : V,
      Relation.ReflTransGen (StarRelation root leaf) (root e0) v) :
    connectedLeafGraphEquiv root leaf hleaf hsep e0 hconnected none = root e0 := rfl

@[simp] lemma connectedLeafGraphEquiv_some {V E : Type*} (root leaf : E → V)
    (hleaf : Function.Injective leaf) (hsep : ∀ i j, root i ≠ leaf j)
    (e0 : E) (hconnected : ∀ v : V,
      Relation.ReflTransGen (StarRelation root leaf) (root e0) v) (i : E) :
    connectedLeafGraphEquiv root leaf hleaf hsep e0 hconnected (some i) = leaf i := rfl

end WP.RandomGeometry
