import WPFormalization.RandomGeometry.PlanarCutTreeGenus
import WPFormalization.RandomGeometry.PantsCutClassification
noncomputable section
set_option maxHeartbeats 0
namespace WP.RandomGeometry.PlanarCut
open WP.External Finset
variable {n r : ℕ} (D : MulticurveCutData n r)

def nonrootVertices (root : Fin D.components) : Finset (Fin D.components) :=
  univ.erase root

def planarCuspCount (root : Fin D.components) : ℕ :=
  (D.cuspSet (nonrootVertices D root)).card

def rootEdges (root : Fin D.components) : Finset (Fin r) :=
  univ.filter (fun e => D.edgeVertex (e,0)=root ∨ D.edgeVertex (e,1)=root)

def rootDegree (root : Fin D.components) : ℕ := (rootEdges D root).card

lemma rootDegree_le (root : Fin D.components) : rootDegree D root≤r := by
  classical
  simpa [rootDegree,rootEdges] using (card_le_card (filter_subset
    (fun e : Fin r=>D.edgeVertex (e,0)=root ∨ D.edgeVertex (e,1)=root) univ))

lemma nonroot_card (hc : D.ConnectedWithin univ) (hcuts : ∀e,∃U,D.IsSide e U)
    (root : Fin D.components) : (nonrootVertices D root).card=r := by
  have hcard := card_erase_add_one (mem_univ root)
  simp only [card_univ,Fintype.card_fin] at hcard
  have hQ := components_eq_edges_add_one D hc hcuts
  change (univ.erase root).card=r
  omega

lemma crossing_nonroot_eq (hcuts : ∀e,∃U,D.IsSide e U) (root : Fin D.components) :
    D.crossingEdges (nonrootVertices D root)=rootEdges D root := by
  classical
  ext e
  have hn := endpoints_ne D hcuts e
  have hn' : ¬ (D.edgeVertex (e,0)=root ∧ D.edgeVertex (e,1)=root) := by
    rintro ⟨h0,h1⟩;exact hn (h0.trans h1.symm)
  simp only [rootEdges,MulticurveCutData.crossingEdges,nonrootVertices,
    mem_filter,mem_univ,true_and,mem_erase,ne_eq,and_true]
  unfold Xor
  tauto

lemma internal_nonroot_add_degree (root : Fin D.components) :
    (D.internalEdges (nonrootVertices D root)).card+rootDegree D root=r := by
  classical
  have heq : D.internalEdges (nonrootVertices D root)=univ.filter
      (fun e=>¬(D.edgeVertex (e,0)=root ∨ D.edgeVertex (e,1)=root)) := by
    ext e
    simp [MulticurveCutData.internalEdges,nonrootVertices]
  rw [heq,rootDegree,rootEdges,add_comm]
  simpa using (card_filter_add_card_filter_not (s:=univ)
    (fun e : Fin r=>D.edgeVertex (e,0)=root ∨ D.edgeVertex (e,1)=root))

lemma planarCuspCount_lower (hc : D.ConnectedWithin univ)
    (hcuts : ∀e,∃U,D.IsSide e U) (root : Fin D.components)
    (hzero : ∀c,c≠root → D.genus c=0)
    (hstable : ∀c,2<2*D.genus c+D.boundaryCount c) :
    r+rootDegree D root≤planarCuspCount D root := by
  classical
  have hs : 3*(nonrootVertices D root).card≤
      ∑c∈nonrootVertices D root,D.boundaryCount c := by
    calc
      _ = ∑_c∈nonrootVertices D root,3 := by simp [Nat.mul_comm]
      _ ≤ _ := by
        apply sum_le_sum
        intro c hc
        have hz := hzero c (mem_erase.mp hc).1
        have hh := hstable c
        omega
  have hi := WP.RandomGeometry.cut_boundary_incidence_sum D (nonrootVertices D root)
  have hc' := nonroot_card D hc hcuts root
  have hcros := crossing_nonroot_eq D hcuts root
  have hpart := internal_nonroot_add_degree D root
  change 3*(nonrootVertices D root).card≤_ at hs
  rw [hc',hi,hcros] at hs
  change r+(rootEdges D root).card≤(D.cuspSet (nonrootVertices D root)).card
  change _+ (rootEdges D root).card=r at hpart
  omega

lemma root_not_mem_planar_side (hc : D.ConnectedWithin univ)
    (hcuts : ∀e,∃U,D.IsSide e U) (root : Fin D.components) (hroot : 0<D.genus root)
    (e : Fin r) (U : Finset (Fin D.components)) (hU : D.IsSide e U)
    (hgU : D.SideGenus U 0) : root∉U := by
  intro hm
  have := planar_side_genus_zero D hc hcuts e U hU hgU root hm
  omega

lemma planarCuspCount_upper (hc : D.ConnectedWithin univ)
    (side : Fin r → Finset (Fin D.components)) (hside : ∀e,D.IsSide e (side e))
    (hgenus : ∀e,D.SideGenus (side e) 0) (root : Fin D.components)
    (hroot : 0<D.genus root) (k : Fin r → ℕ)
    (hk : ∀e,(D.cuspSet (side e)).card=k e) :
    planarCuspCount D root≤∑e,k e := by
  classical
  have hcuts : ∀e,∃U,D.IsSide e U := fun e=>⟨side e,hside e⟩
  have hsub : D.cuspSet (nonrootVertices D root)⊆univ.biUnion (fun e=>D.cuspSet (side e)) := by
    intro i hi
    have hne : D.cuspVertex i≠root := by
      simpa [MulticurveCutData.cuspSet,nonrootVertices] using hi
    obtain ⟨e,hsep⟩ := exists_separating_side D hc side hside root (D.cuspVertex i) hne.symm
    have hn := root_not_mem_planar_side D hc hcuts root hroot e (side e) (hside e) (hgenus e)
    have him : D.cuspVertex i∈side e := by unfold Xor at hsep;tauto
    apply mem_biUnion.mpr
    refine ⟨e,mem_univ _,?_⟩
    simpa only [MulticurveCutData.cuspSet,mem_filter,mem_univ,true_and] using him
  exact (card_le_card hsub).trans (card_biUnion_le.trans (by simp only [hk];exact le_rfl))

end WP.RandomGeometry.PlanarCut
