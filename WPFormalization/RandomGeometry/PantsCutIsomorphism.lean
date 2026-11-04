import WPFormalization.RandomGeometry.PantsCutLabels

/-! The actual cut is isomorphic to the labeled pants star. -/
noncomputable section
namespace WP.RandomGeometry
open WP.External
variable {n r : ℕ} (D : MulticurveCutData n r)
    (leaf : Fin r → Fin D.components) (hleaf : ∀e, PantsLeafData D e (leaf e))
    (hconnected : D.ConnectedWithin Finset.univ) (e0 : Fin r)

def pantsStarVertexEquiv : Fin (r+1) ≃ Fin D.components :=
  (finSuccEquiv r).trans (pantsCutVertexEquiv D leaf hleaf hconnected e0)

@[simp] lemma pantsStarVertexEquiv_zero :
    pantsStarVertexEquiv D leaf hleaf hconnected e0 0 = pantsLeafRoot D leaf e0 := rfl

@[simp] lemma pantsStarVertexEquiv_succ (i : Fin r) :
    pantsStarVertexEquiv D leaf hleaf hconnected e0 i.succ = leaf i := by
  simp [pantsStarVertexEquiv]

include hleaf hconnected e0 in
lemma pantsLeafRoot_eq (i : Fin r) :
    pantsLeafRoot D leaf i = pantsLeafRoot D leaf e0 := by
  apply (connected_leaf_graph_star (pantsLeafRoot D leaf) leaf
    (pantsLeaf_injective D leaf hleaf) (pantsLeafRoot_ne_leaf D leaf hleaf) e0 ?_).1
  intro v
  exact Relation.ReflTransGen.mono (fun a b h =>
    (cut_adjacent_star_iff D leaf hleaf a b).1 h) _ _
    (hconnected.2 _ (Finset.mem_univ _) v (Finset.mem_univ _))

/-- This statement is about the actual component genera, original cusp
labels, and actual curve-side incidences, not a replacement recursion model. -/
def pantsCutStarIso (g : ℕ)
    (heuler : (∑c, D.genus c) + r + 1 = g + D.components) :
    MulticurveCutData.Isomorphism (pantsCutGraph g n r (pantsCutLabels D leaf hleaf)) D := by
  classical
  let f := pantsCutLabels D leaf hleaf
  let v := pantsStarVertexEquiv D leaf hleaf hconnected e0
  have hv0 : v (0 : Fin (r+1)) = pantsLeafRoot D leaf e0 := rfl
  have hvs (i : Fin r) : v i.succ = leaf i :=
    pantsStarVertexEquiv_succ D leaf hleaf hconnected e0 i
  refine ⟨v, fun e => decide (D.edgeVertex (e,0) = leaf e), ?_, ?_, ?_⟩
  · intro c
    refine Fin.cases ?_ (fun i => ?_) c
    · change D.genus (v (0 : Fin (r+1))) = g
      rw [hv0]
      exact pantsCut_genus_root D leaf hleaf g hconnected e0 heuler
    · change D.genus (v i.succ) = 0
      rw [hvs]
      exact (hleaf i).genus_zero
  · intro j
    by_cases hj : ∃p : Fin r × Fin 2, f.val p = j
    · rcases hj with ⟨p,hp⟩
      subst j
      rw [pantsCutGraph_cusp_pair]
      exact (pantsStarVertexEquiv_succ D leaf hleaf hconnected e0 p.1).trans
        (pantsCutLabels_vertex D leaf hleaf p.1 p.2).symm
    · have hc0 : (pantsCutGraph g n r f).cuspVertex j = (0 : Fin (r+1)) := by
        change (if h : ∃p : Fin r × Fin 2, f.val p = j then h.choose.1.succ else 0) = (0 : Fin (r+1))
        exact dif_neg hj
      rw [hc0]
      change pantsLeafRoot D leaf e0 = D.cuspVertex j
      rcases (pantsCutVertexEquiv D leaf hleaf hconnected e0).surjective (D.cuspVertex j) with ⟨c,hc⟩
      cases c with
      | none => exact hc
      | some i =>
        have hi : D.cuspVertex j = leaf i := hc.symm
        rcases pantsCutLabels_covers_leaf D leaf hleaf i j hi with ⟨a,ha⟩
        exact (hj ⟨(i,a),ha⟩).elim
  · intro e j
    change v (if j = 0 then (0 : Fin (r+1)) else e.succ) =
      D.edgeVertex (e, if decide (D.edgeVertex (e,0) = leaf e) then j.rev else j)
    have hr := pantsLeafRoot_eq D leaf hleaf hconnected e0 e
    have he := pantsLeaf_endpoints D leaf hleaf e
    fin_cases j <;> by_cases h0 : D.edgeVertex (e,0) = leaf e
    · have h1 : D.edgeVertex (e,1) = pantsLeafRoot D leaf e := by
        simpa [pantsLeafRoot,h0]
      have hh : v (0 : Fin (r+1)) = D.edgeVertex (e,1) :=
        hv0.trans (hr.symm.trans h1.symm)
      simpa [pantsCutGraph,h0] using hh
    · have hh : v (0 : Fin (r+1)) = D.edgeVertex (e,0) :=
        hv0.trans (hr.symm.trans (by simp [pantsLeafRoot,h0]))
      simpa [pantsCutGraph,h0] using hh
    · have hh : v e.succ = D.edgeVertex (e,0) := (hvs e).trans h0.symm
      simpa [pantsCutGraph,h0] using hh
    · have h1 : D.edgeVertex (e,1) = leaf e := by
        exact (pantsLeaf_edge_iff D e (leaf e) (hleaf e) e).2 rfl |>.resolve_left h0
      have hh : v e.succ = D.edgeVertex (e,1) := (hvs e).trans h1.symm
      simpa [pantsCutGraph,h0] using hh

end WP.RandomGeometry
