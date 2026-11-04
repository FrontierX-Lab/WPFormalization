import WPFormalization.RandomGeometry.PantsCutClassification
import WPFormalization.RandomGeometry.PantsStarGraph

/-! The actual cut of disjoint two-cusp curves is a star, with a single root. -/
noncomputable section
namespace WP.RandomGeometry
open WP.External
variable {n r : ℕ} (D : MulticurveCutData n r)
    (leaf : Fin r → Fin D.components) (hleaf : ∀ e, PantsLeafData D e (leaf e))

def pantsLeafRoot (e : Fin r) : Fin D.components :=
  if D.edgeVertex (e,0) = leaf e then D.edgeVertex (e,1) else D.edgeVertex (e,0)

include hleaf

lemma pantsLeaf_endpoints (e : Fin r) :
    (D.edgeVertex (e,0) = pantsLeafRoot D leaf e ∧ D.edgeVertex (e,1) = leaf e) ∨
    (D.edgeVertex (e,0) = leaf e ∧ D.edgeVertex (e,1) = pantsLeafRoot D leaf e) := by
  have hi := (pantsLeaf_edge_iff D e (leaf e) (hleaf e) e).2 rfl
  by_cases h0 : D.edgeVertex (e,0) = leaf e
  · exact Or.inr ⟨h0, by simp [pantsLeafRoot,h0]⟩
  · exact Or.inl ⟨by simp [pantsLeafRoot,h0], hi.resolve_left h0⟩

lemma pantsLeafRoot_ne_leaf_self (e : Fin r) : pantsLeafRoot D leaf e ≠ leaf e := by
  have hn : ¬ (D.edgeVertex (e,0) = leaf e ∧ D.edgeVertex (e,1) = leaf e) := by
    have hm : e ∉ D.internalEdges {leaf e} := by rw [(hleaf e).no_internal]; simp
    simpa only [MulticurveCutData.internalEdges, Finset.mem_filter,
      Finset.mem_univ, true_and, Finset.mem_singleton] using hm
  by_cases h0 : D.edgeVertex (e,0) = leaf e
  · simpa only [pantsLeafRoot, if_pos h0] using fun he => hn ⟨h0,he⟩
  · simpa only [pantsLeafRoot, if_neg h0] using h0

lemma pantsLeafRoot_ne_leaf (i j : Fin r) : pantsLeafRoot D leaf i ≠ leaf j := by
  intro he
  have hi : D.edgeVertex (i,0) = leaf j ∨ D.edgeVertex (i,1) = leaf j := by
    rcases pantsLeaf_endpoints D leaf hleaf i with h | h
    · exact Or.inl (h.1.trans he)
    · exact Or.inr (h.2.trans he)
  have hij : i = j := (pantsLeaf_edge_iff D j (leaf j) (hleaf j) i).1 hi
  subst j
  exact pantsLeafRoot_ne_leaf_self D leaf hleaf i he

lemma cut_adjacent_star_iff (a b : Fin D.components) :
    D.AdjacentWithin Finset.univ a b ↔ StarRelation (pantsLeafRoot D leaf) leaf a b := by
  constructor
  · rintro ⟨_,_,e,h⟩
    rcases pantsLeaf_endpoints D leaf hleaf e with he | he
    · refine ⟨e, ?_⟩
      rcases h with h | h
      · exact Or.inl ⟨h.1.symm.trans he.1, h.2.symm.trans he.2⟩
      · exact Or.inr ⟨h.1.symm.trans he.2, h.2.symm.trans he.1⟩
    · refine ⟨e, ?_⟩
      rcases h with h | h
      · exact Or.inr ⟨h.1.symm.trans he.1, h.2.symm.trans he.2⟩
      · exact Or.inl ⟨h.1.symm.trans he.2, h.2.symm.trans he.1⟩
  · rintro ⟨e,h⟩
    refine ⟨Finset.mem_univ _,Finset.mem_univ _,e,?_⟩
    rcases pantsLeaf_endpoints D leaf hleaf e with he | he
    · rcases h with h | h
      · exact Or.inl ⟨he.1.trans h.1.symm, he.2.trans h.2.symm⟩
      · exact Or.inr ⟨he.2.trans h.1.symm, he.1.trans h.2.symm⟩
    · rcases h with h | h
      · exact Or.inr ⟨he.2.trans h.1.symm, he.1.trans h.2.symm⟩
      · exact Or.inl ⟨he.1.trans h.1.symm, he.2.trans h.2.symm⟩

/-- An explicit equivalence between the cut components and the root plus its
ordered pants leaves; connectedness rules out extra components. -/
def pantsCutVertexEquiv (hconnected : D.ConnectedWithin Finset.univ) (e0 : Fin r) :
    Option (Fin r) ≃ Fin D.components :=
  connectedLeafGraphEquiv (pantsLeafRoot D leaf) leaf (pantsLeaf_injective D leaf hleaf)
    (pantsLeafRoot_ne_leaf D leaf hleaf) e0 (by
      intro v
      have hp := hconnected.2 (pantsLeafRoot D leaf e0) (Finset.mem_univ _) v (Finset.mem_univ _)
      exact Relation.ReflTransGen.mono (fun a b h =>
        (cut_adjacent_star_iff D leaf hleaf a b).1 h) _ _ hp)

lemma pantsCut_components (hconnected : D.ConnectedWithin Finset.univ) (e0 : Fin r) :
    D.components = r+1 := by
  have hc := Fintype.card_congr (pantsCutVertexEquiv D leaf hleaf hconnected e0)
  simpa only [Fintype.card_option, Fintype.card_fin] using hc.symm

@[simp] lemma pantsCutVertexEquiv_none
    (hconnected : D.ConnectedWithin Finset.univ) (e0 : Fin r) :
    pantsCutVertexEquiv D leaf hleaf hconnected e0 none = pantsLeafRoot D leaf e0 := rfl

@[simp] lemma pantsCutVertexEquiv_some
    (hconnected : D.ConnectedWithin Finset.univ) (e0 i : Fin r) :
    pantsCutVertexEquiv D leaf hleaf hconnected e0 (some i) = leaf i := rfl

lemma pantsCut_genus_root (g : ℕ)
    (hconnected : D.ConnectedWithin Finset.univ) (e0 : Fin r)
    (heuler : (∑ c, D.genus c) + r + 1 = g + D.components) :
    D.genus (pantsLeafRoot D leaf e0) = g := by
  have hc := pantsCut_components D leaf hleaf hconnected e0
  have hs := (pantsCutVertexEquiv D leaf hleaf hconnected e0).sum_comp D.genus
  have hs0 : (∑ c, D.genus c) = D.genus (pantsLeafRoot D leaf e0) := by
    simpa only [Fintype.sum_option, pantsCutVertexEquiv_none,
      pantsCutVertexEquiv_some, fun i => (hleaf i).genus_zero,
      Finset.sum_const_zero, add_zero] using hs.symm
  omega

end WP.RandomGeometry
