import WPFormalization.RandomGeometry.PlanarCutTreeGraph
noncomputable section
set_option maxHeartbeats 0
namespace WP.RandomGeometry.PlanarCut
open WP.External Finset
variable {n r : ℕ} (D : MulticurveCutData n r)

lemma graph_induce_connected (U : Finset (Fin D.components))
    (hc : D.ConnectedWithin U) : ((graph D).induce (U : Set _)).Connected := by
  haveI : Nonempty {c // c∈U} := ⟨⟨hc.1.choose,hc.1.choose_spec⟩⟩
  refine ⟨?_⟩
  intro a b
  have hp := hc.2 a.val a.property b.val b.property
  have haux : ∀ {x y} (hx : x∈U) (hy : y∈U),
      Relation.ReflTransGen (D.AdjacentWithin U) x y →
      ((graph D).induce (U : Set _)).Reachable ⟨x,hx⟩ ⟨y,hy⟩ := by
    intro x y hx hy hp
    revert hy
    induction hp with
    | refl => intro _;exact .rfl
    | @tail y z hp hadj ih =>
      intro hz
      by_cases heq : y=z
      · subst z;exact ih hz
      · exact (ih hadj.1).trans (SimpleGraph.Adj.reachable
          (show ((graph D).induce (U : Set _)).Adj ⟨y,hadj.1⟩ ⟨z,hz⟩ from
            ⟨heq,hadj.2.2⟩))
  exact haux a.property b.property hp

lemma internal_mem_iff (U : Finset (Fin D.components)) (e : Fin r) :
    e∈D.internalEdges U ↔ D.edgeVertex (e,0)∈U ∧ D.edgeVertex (e,1)∈U := by
  classical
  simp [MulticurveCutData.internalEdges]

def internalEdgePairEquiv (hcuts : ∀e,∃U,D.IsSide e U)
    (U : Finset (Fin D.components)) :
    {e : Fin r // e∈D.internalEdges U} ≃ ((graph D).induce (U : Set _)).edgeSet :=
  Equiv.ofBijective (fun e => ⟨s(
    ⟨D.edgeVertex (e.val,0),((internal_mem_iff D U e.val).1 e.property).1⟩,
    ⟨D.edgeVertex (e.val,1),((internal_mem_iff D U e.val).1 e.property).2⟩),by
      apply ((graph D).induce (U : Set _)).mem_edgeSet.mpr
      exact ⟨endpoints_ne D hcuts e.val,e.val,Or.inl ⟨rfl,rfl⟩⟩⟩) (by
        constructor
        · intro a b hab
          apply Subtype.ext
          apply edgePair_injective D hcuts
          have hh := congrArg (fun p => Sym2.map (fun c : {c // c∈U} => c.val) p.val) hab
          exact hh
        · rintro ⟨p,hp⟩
          induction p using Sym2.inductionOn with
          | _ a b =>
            obtain ⟨_,e,he|he⟩ := ((graph D).induce (U : Set _)).mem_edgeSet.mp hp
            all_goals
              have hm : e∈D.internalEdges U := by
                apply (internal_mem_iff D U e).2
                rcases he with ⟨h0,h1⟩
                first | exact ⟨h0 ▸ a.property,h1 ▸ b.property⟩ |
                  exact ⟨h1 ▸ b.property,h0 ▸ a.property⟩
              refine ⟨⟨e,hm⟩,Subtype.ext ?_⟩
              rcases he with ⟨h0,h1⟩
              first
              | exact congrArg₂ Sym2.mk (Subtype.ext h0) (Subtype.ext h1)
              | exact (congrArg₂ Sym2.mk (Subtype.ext h1) (Subtype.ext h0)).trans Sym2.eq_swap)

lemma internal_card_add_one (hc : D.ConnectedWithin univ)
    (hcuts : ∀e,∃U,D.IsSide e U) (U : Finset (Fin D.components))
    (hU : D.ConnectedWithin U) : (D.internalEdges U).card+1=U.card := by
  have ht : ((graph D).induce (U : Set _)).IsTree :=
    ⟨graph_induce_connected D U hU,(graph_isTree D hc hcuts).isAcyclic.induce _⟩
  have hh := (SimpleGraph.isTree_iff_connected_and_card.mp ht).2
  have he : Nat.card ((graph D).induce (U : Set _)).edgeSet=(D.internalEdges U).card := by
    rw [←Nat.card_congr (internalEdgePairEquiv D hcuts U)]
    simp [Nat.card_eq_fintype_card]
  rw [he] at hh
  have hu : Nat.card (U : Set (Fin D.components))=U.card := by
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_coe U
  rwa [hu] at hh

lemma planar_side_genus_zero (hc : D.ConnectedWithin univ)
    (hcuts : ∀e,∃U,D.IsSide e U) (e : Fin r) (U : Finset (Fin D.components))
    (hU : D.IsSide e U) (hg : D.SideGenus U 0) : ∀ c∈U,D.genus c=0 := by
  have hcard := internal_card_add_one D hc hcuts U hU.2.2.2.1
  have hz : (∑c∈U,D.genus c)=0 := by
    unfold MulticurveCutData.SideGenus at hg
    omega
  exact (Finset.sum_eq_zero_iff).1 hz


lemma mem_iff_of_reachable_delete (e : Fin r) (U : Finset (Fin D.components))
    (hU : D.IsSide e U) {a b : Fin D.components}
    (hp : ((graph D).deleteEdges {edgePair D e}).Reachable a b) : (a∈U ↔ b∈U) := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at hp
  induction hp with
  | refl => exact Iff.rfl
  | tail hp hadj ih => exact ih.trans (mem_iff_of_adj_delete D e U hU hadj)

lemma exists_separating_side (hc : D.ConnectedWithin univ)
    (side : Fin r → Finset (Fin D.components)) (hside : ∀e,D.IsSide e (side e))
    (a b : Fin D.components) (hne : a≠b) :
    ∃e,Xor (a∈side e) (b∈side e) := by
  classical
  obtain ⟨p,hp⟩ := (graph_connected D hc a b).exists_isPath
  cases p with
  | nil => exact (hne rfl).elim
  | @cons a c b hab p =>
    obtain ⟨_,e,he|he⟩ := hab
    all_goals
      let U := side e
      have hU := hside e
      have hedge : edgePair D e=s(a,c) := by
        rcases he with ⟨h0,h1⟩
        first | exact congrArg₂ Sym2.mk h0 h1 |
          exact (congrArg₂ Sym2.mk h1 h0).trans Sym2.eq_swap
      have hnot : edgePair D e∉p.edges := by
        intro hm
        rw [hedge] at hm
        exact (SimpleGraph.Walk.cons_isPath_iff _ _).1 hp |>.2
          (p.fst_mem_support_of_mem_edges hm)
      have hcb := mem_iff_of_reachable_delete D e U hU (p.toDeleteEdge _ hnot).reachable
      have hx : Xor (a∈U) (c∈U) := by
        have hx := side_crossing D e U hU
        rcases he with ⟨h0,h1⟩
        first | exact h0 ▸ h1 ▸ hx | exact (h1 ▸ h0 ▸ hx).symm
      exact ⟨e,by unfold Xor at *;tauto⟩

lemma genus_sum_eq {g : ℕ} (hc : D.ConnectedWithin univ)
    (hcuts : ∀e,∃U,D.IsSide e U)
    (heuler : (∑c,D.genus c)+r+1=g+D.components) : (∑c,D.genus c)=g := by
  have := components_eq_edges_add_one D hc hcuts
  omega

lemma exists_unique_genus_root {g : ℕ} (hg : 1≤g) (hc : D.ConnectedWithin univ)
    (heuler : (∑c,D.genus c)+r+1=g+D.components)
    (hplanar : ∀e,∃U,D.IsSide e U ∧ D.SideGenus U 0) :
    ∃root : Fin D.components,D.genus root=g ∧ ∀c,c≠root → D.genus c=0 := by
  classical
  choose side hside hgenus using hplanar
  have hcuts : ∀e,∃U,D.IsSide e U := fun e=>⟨side e,hside e⟩
  have hsum := genus_sum_eq D hc hcuts heuler
  have hpos : 0<∑c,D.genus c := by omega
  obtain ⟨root,_,hroot⟩ := Finset.sum_pos_iff.mp hpos
  have hz : ∀c,c≠root → D.genus c=0 := by
    intro c hne
    by_contra hcz
    obtain ⟨e,hsep⟩ := exists_separating_side D hc side hside root c hne.symm
    have hzero := planar_side_genus_zero D hc hcuts e (side e) (hside e) (hgenus e)
    unfold Xor at hsep
    rcases hsep with ⟨hr,_⟩|⟨hcm,_⟩
    · have := hzero root hr;omega
    · exact hcz (hzero c hcm)
  refine ⟨root,?_,hz⟩
  have hsingle : (∑c,D.genus c)=D.genus root := by
    rw [Finset.sum_eq_single root]
    · intro c _ h;exact hz c h
    · simp
  omega


/-- A canonical finite vertex enumeration with the specified actual root first.
Other vertices are enumerated by their original finite component labels. -/
def vertexEquivRoot (hc : D.ConnectedWithin univ)
    (hcuts : ∀e,∃U,D.IsSide e U) (root : Fin D.components) :
    Fin (r+1) ≃ Fin D.components :=
  let E := finCongr (components_eq_edges_add_one D hc hcuts).symm
  E.trans (Equiv.swap (E 0) root)

@[simp] lemma vertexEquivRoot_zero (hc : D.ConnectedWithin univ)
    (hcuts : ∀e,∃U,D.IsSide e U) (root : Fin D.components) :
    vertexEquivRoot D hc hcuts root 0=root := by
  simp [vertexEquivRoot]

end WP.RandomGeometry.PlanarCut
