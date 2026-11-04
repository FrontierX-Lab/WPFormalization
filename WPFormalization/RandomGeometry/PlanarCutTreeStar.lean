import WPFormalization.RandomGeometry.PlanarCutTreeBudget
import WPFormalization.RandomGeometry.GeneralPlanarStarCutSides
noncomputable section
set_option maxHeartbeats 0
namespace WP.RandomGeometry.PlanarCut
open WP.External Finset
variable {n r : ℕ} (D : MulticurveCutData n r)

def starLeaf (root : Fin D.components) (e : Fin r) : Fin D.components :=
  if D.edgeVertex (e,0)=root then D.edgeVertex (e,1) else D.edgeVertex (e,0)

lemma rootEdges_eq_univ (root : Fin D.components) (hd : rootDegree D root=r) :
    rootEdges D root=univ := by
  classical
  apply eq_of_subset_of_card_le (subset_univ _)
  simpa [rootDegree] using hd.ge

lemma edge_incident_root (root : Fin D.components) (hd : rootDegree D root=r) (e : Fin r) :
    D.edgeVertex (e,0)=root ∨ D.edgeVertex (e,1)=root := by
  have hm : e∈rootEdges D root := by rw [rootEdges_eq_univ D root hd];simp
  exact (mem_filter.mp hm).2

lemma starLeaf_endpoints (root : Fin D.components) (hd : rootDegree D root=r) (e : Fin r) :
    (D.edgeVertex (e,0)=root ∧ D.edgeVertex (e,1)=starLeaf D root e) ∨
    (D.edgeVertex (e,1)=root ∧ D.edgeVertex (e,0)=starLeaf D root e) := by
  by_cases h0 : D.edgeVertex (e,0)=root
  · exact Or.inl ⟨h0,by simp [starLeaf,h0]⟩
  · exact Or.inr ⟨(edge_incident_root D root hd e).resolve_left h0,by simp [starLeaf,h0]⟩

lemma starLeaf_ne_root (hcuts : ∀e,∃U,D.IsSide e U)
    (root : Fin D.components) (hd : rootDegree D root=r) (e : Fin r) :
    starLeaf D root e≠root := by
  have hn := endpoints_ne D hcuts e
  rcases starLeaf_endpoints D root hd e with ⟨h0,h1⟩|⟨h0,h1⟩ <;>
    intro h <;> apply hn <;> rw [h0,h1,h]

lemma edgePair_starLeaf (root : Fin D.components) (hd : rootDegree D root=r) (e : Fin r) :
    edgePair D e=s(root,starLeaf D root e) := by
  rcases starLeaf_endpoints D root hd e with ⟨h0,h1⟩|⟨h0,h1⟩ <;>
    simp only [edgePair,h0,h1,Sym2.eq_swap]

lemma starLeaf_injective (hcuts : ∀e,∃U,D.IsSide e U)
    (root : Fin D.components) (hd : rootDegree D root=r) : Function.Injective (starLeaf D root) := by
  intro e f hef
  apply edgePair_injective D hcuts
  rw [edgePair_starLeaf D root hd e,edgePair_starLeaf D root hd f,hef]

def starVertexEquiv (hc : D.ConnectedWithin univ) (hcuts : ∀e,∃U,D.IsSide e U)
    (root : Fin D.components) (hd : rootDegree D root=r) : Fin (r+1) ≃ Fin D.components :=
  let v : Option (Fin r) → Fin D.components := fun c=>c.elim root (starLeaf D root)
  (finSuccEquiv r).trans (Equiv.ofBijective v (by
    apply (Fintype.bijective_iff_injective_and_card v).mpr
    constructor
    · intro a b hab
      cases a with
      | none =>
        cases b with
        | none => rfl
        | some b => exact (starLeaf_ne_root D hcuts root hd b hab.symm).elim
      | some a =>
        cases b with
        | none => exact (starLeaf_ne_root D hcuts root hd a hab).elim
        | some b => exact congrArg some (starLeaf_injective D hcuts root hd hab)
    · simp only [Fintype.card_option,Fintype.card_fin]
      exact (components_eq_edges_add_one D hc hcuts).symm))

@[simp] lemma starVertexEquiv_zero (hc : D.ConnectedWithin univ)
    (hcuts : ∀e,∃U,D.IsSide e U) (root : Fin D.components) (hd : rootDegree D root=r) :
    starVertexEquiv D hc hcuts root hd 0=root := rfl

@[simp] lemma starVertexEquiv_succ (hc : D.ConnectedWithin univ)
    (hcuts : ∀e,∃U,D.IsSide e U) (root : Fin D.components) (hd : rootDegree D root=r) (i : Fin r) :
    starVertexEquiv D hc hcuts root hd i.succ=starLeaf D root i := by simp [starVertexEquiv]

lemma side_eq_singleton_starLeaf (hc : D.ConnectedWithin univ)
    (hcuts : ∀e,∃U,D.IsSide e U) (root : Fin D.components) (hd : rootDegree D root=r)
    (e : Fin r) (U : Finset (Fin D.components)) (hU : D.IsSide e U) (hn : root∉U) :
    U={starLeaf D root e} := by
  classical
  have hmem : starLeaf D root e∈U := by
    have hx := side_crossing D e U hU
    rcases starLeaf_endpoints D root hd e with ⟨h0,h1⟩|⟨h0,h1⟩ <;>
      rw [h0,h1] at hx <;> unfold Xor at hx <;> tauto
  ext c
  obtain ⟨c,rfl⟩ := (starVertexEquiv D hc hcuts root hd).surjective c
  refine Fin.cases ?_ (fun f=>?_) c
  · simp [hn,(starLeaf_ne_root D hcuts root hd e).symm]
  · rw [starVertexEquiv_succ]
    by_cases hfe : f=e
    · subst f;simp [hmem]
    · have hnf : starLeaf D root f∉U := by
        intro hf
        have hi := side_mem_iff_of_ne D e f U hU hfe
        rcases starLeaf_endpoints D root hd f with ⟨h0,h1⟩|⟨h0,h1⟩ <;>
          rw [h0,h1] at hi <;> tauto
      have hne : starLeaf D root f≠starLeaf D root e :=
        fun h=>hfe (starLeaf_injective D hcuts root hd h)
      simp [hnf,hne]


lemma exists_generalPlanarStar_iso {g : ℕ} (hg : 1≤g) (k : Fin r → ℕ)
    (hc : D.ConnectedWithin univ)
    (heuler : (∑c,D.genus c)+r+1=g+D.components)
    (hplanar : ∀e,∃S,D.PlanarSide e S ∧ S.card=k e)
    (root : Fin D.components) (hroot : D.genus root=g)
    (hzero : ∀c,c≠root → D.genus c=0) (hd : rootDegree D root=r) :
    ∃f : WP.RandomGeometry.PlanarLabelBlocks n r k,
      Nonempty (MulticurveCutData.Isomorphism
        (WP.RandomGeometry.generalPlanarStarCut g n r k f) D) := by
  classical
  choose S hp hcard using hplanar
  choose U hside hgenus hlabels using hp
  have hcuts : ∀e,∃U,D.IsSide e U := fun e=>⟨U e,hside e⟩
  have hpos : 0<D.genus root := by omega
  have hsing (e) : U e={starLeaf D root e} :=
    side_eq_singleton_starLeaf D hc hcuts root hd e (U e) (hside e)
      (root_not_mem_planar_side D hc hcuts root hpos e (U e) (hside e) (hgenus e))
  have hcusp (e) : (D.cuspSet {starLeaf D root e}).card=k e := by
    rw [←hsing e,hlabels e]
    exact hcard e
  let blocks : WP.RandomGeometry.UnorderedLabelBlocks n r k := ⟨
    fun e=>D.cuspSet {starLeaf D root e},hcusp,by
      intro e f hef
      apply Finset.disjoint_left.mpr
      intro j hj hj'
      have h1 : D.cuspVertex j=starLeaf D root e := by
        simpa only [MulticurveCutData.cuspSet,mem_filter,mem_univ,true_and,mem_singleton] using hj
      have h2 : D.cuspVertex j=starLeaf D root f := by
        simpa only [MulticurveCutData.cuspSet,mem_filter,mem_univ,true_and,mem_singleton] using hj'
      exact hef (starLeaf_injective D hcuts root hd (h1.symm.trans h2))⟩
  let f := blocks.sorted
  have hfsets (e) : f.labelSet e=D.cuspSet {starLeaf D root e} := by
    change (WP.RandomGeometry.blocksOfEmbedding blocks.sorted.val).labelSet e=_
    rw [WP.RandomGeometry.blocksOfEmbedding_sorted]
    rfl
  have hrow (p : Σe,Fin (k e)) : D.cuspVertex (f.val p)=starLeaf D root p.1 := by
    have hm := f.apply_mem_labelSet p.1 p.2
    rw [hfsets] at hm
    simpa only [MulticurveCutData.cuspSet,mem_filter,mem_univ,true_and,mem_singleton] using hm
  let v := starVertexEquiv D hc hcuts root hd
  have hv0 : v 0=root := starVertexEquiv_zero D hc hcuts root hd
  have hvs (e) : v e.succ=starLeaf D root e := starVertexEquiv_succ D hc hcuts root hd e
  refine ⟨f,⟨⟨v,fun e=>decide (D.edgeVertex (e,0)=starLeaf D root e),?_,?_,?_⟩⟩⟩
  · intro c
    refine Fin.cases ?_ (fun e=>?_) c
    · change D.genus (v 0)=g
      rw [hv0,hroot]
    · change D.genus (v e.succ)=0
      rw [hvs]
      exact hzero _ (starLeaf_ne_root D hcuts root hd e)
  · intro j
    change v ((WP.RandomGeometry.generalPlanarStarCut g n r k f).cuspVertex j)=D.cuspVertex j
    by_cases hj : ∃p : Σe,Fin (k e),f.val p=j
    · obtain ⟨p,rfl⟩ := hj
      rw [WP.RandomGeometry.generalPlanarStarCut_cusp_apply]
      exact (hvs p.1).trans (hrow p).symm
    · rw [(WP.RandomGeometry.generalPlanarStarCut_cusp_root_iff g n r k f j).mpr hj,hv0]
      obtain ⟨c,hc⟩ := v.surjective (D.cuspVertex j)
      revert hc
      refine Fin.cases ?_ (fun e=>?_) c
      · intro hc;simpa only [hv0] using hc
      · intro hc
        have hm : j∈f.labelSet e := by
          rw [hfsets]
          have hh : D.cuspVertex j=starLeaf D root e := hc.symm.trans (hvs e)
          simpa [MulticurveCutData.cuspSet] using hh
        obtain ⟨a,ha⟩ := (f.mem_labelSet e j).1 hm
        exact (hj ⟨⟨e,a⟩,ha⟩).elim
  · intro e j
    change v (if j=0 then 0 else e.succ)=
      D.edgeVertex (e,if decide (D.edgeVertex (e,0)=starLeaf D root e) then j.rev else j)
    have hends := starLeaf_endpoints D root hd e
    have hn := starLeaf_ne_root D hcuts root hd e
    fin_cases j <;> by_cases h0 : D.edgeVertex (e,0)=starLeaf D root e
    · have h1 : D.edgeVertex (e,1)=root := by
        rcases hends with h|h
        · exact (hn (h0.symm.trans h.1)).elim
        · exact h.1
      simpa [h0] using hv0.trans h1.symm
    · have h1 : D.edgeVertex (e,0)=root := by rcases hends with h|h <;> tauto
      simpa [h0] using hv0.trans h1.symm
    · simpa [h0] using (hvs e).trans h0.symm
    · have h1 : D.edgeVertex (e,1)=starLeaf D root e := by rcases hends with h|h <;> tauto
      simpa [h0] using (hvs e).trans h1.symm


lemma rootDegree_pos (hc : D.ConnectedWithin univ) (hcuts : ∀e,∃U,D.IsSide e U)
    (hr : 0<r) (root : Fin D.components) : 0<rootDegree D root := by
  classical
  have hQ := components_eq_edges_add_one D hc hcuts
  have hcard : 1<Fintype.card (Fin D.components) := by simp only [Fintype.card_fin];omega
  haveI := Fintype.one_lt_card_iff_nontrivial.mp hcard
  obtain ⟨c,hcne⟩ := exists_ne root
  obtain ⟨a,ha⟩ := (graph_connected D hc root c).nonempty_neighborSet_left hcne.symm
  obtain ⟨_,e,he|he⟩ := ha
  all_goals
    apply Finset.card_pos.mpr
    refine ⟨e,mem_filter.mpr ⟨mem_univ _,?_⟩⟩
    tauto

lemma nonstar_rootDegree_lt {g : ℕ} (hg : 1≤g) (k : Fin r → ℕ)
    (hc : D.ConnectedWithin univ)
    (heuler : (∑c,D.genus c)+r+1=g+D.components)
    (hplanar : ∀e,∃S,D.PlanarSide e S ∧ S.card=k e)
    (root : Fin D.components) (hroot : D.genus root=g)
    (hzero : ∀c,c≠root → D.genus c=0)
    (hns : ¬ ∃f : WP.RandomGeometry.PlanarLabelBlocks n r k,
      Nonempty (MulticurveCutData.Isomorphism
        (WP.RandomGeometry.generalPlanarStarCut g n r k f) D)) :
    rootDegree D root<r := by
  have hd := rootDegree_le D root
  by_contra hn
  have hd' : rootDegree D root=r := by omega
  exact hns (exists_generalPlanarStar_iso D hg k hc heuler hplanar root hroot hzero hd')

lemma nonstar_rootDegree_le {g : ℕ} (hg : 1≤g) (k : Fin r → ℕ)
    (hc : D.ConnectedWithin univ)
    (heuler : (∑c,D.genus c)+r+1=g+D.components)
    (hplanar : ∀e,∃S,D.PlanarSide e S ∧ S.card=k e)
    (root : Fin D.components) (hroot : D.genus root=g)
    (hzero : ∀c,c≠root → D.genus c=0)
    (hns : ¬ ∃f : WP.RandomGeometry.PlanarLabelBlocks n r k,
      Nonempty (MulticurveCutData.Isomorphism
        (WP.RandomGeometry.generalPlanarStarCut g n r k f) D)) :
    rootDegree D root≤r-1 := by
  have := nonstar_rootDegree_lt D hg k hc heuler hplanar root hroot hzero hns
  omega

lemma one_edge_exists_generalPlanarStar_iso {g : ℕ} (hg : 1≤g) (hr : r=1)
    (k : Fin r → ℕ) (hc : D.ConnectedWithin univ)
    (heuler : (∑c,D.genus c)+r+1=g+D.components)
    (hplanar : ∀e,∃S,D.PlanarSide e S ∧ S.card=k e) :
    ∃f : WP.RandomGeometry.PlanarLabelBlocks n r k,
      Nonempty (MulticurveCutData.Isomorphism
        (WP.RandomGeometry.generalPlanarStarCut g n r k f) D) := by
  have hp : ∀e,∃U,D.IsSide e U ∧ D.SideGenus U 0 := by
    intro e
    obtain ⟨S,⟨U,hU,hgU,_⟩,_⟩ := hplanar e
    exact ⟨U,hU,hgU⟩
  have hcuts : ∀e,∃U,D.IsSide e U := fun e=>let ⟨U,hU,_⟩:=hp e;⟨U,hU⟩
  obtain ⟨root,hroot,hzero⟩ := exists_unique_genus_root D hg hc heuler hp
  have hd : rootDegree D root=r := by
    have := rootDegree_pos D hc hcuts (by omega) root
    have := rootDegree_le D root
    omega
  exact exists_generalPlanarStar_iso D hg k hc heuler hplanar root hroot hzero hd


/-- The complete actual-cut classification and cusp budget, with only the
original connected/stable/Euler/planar-side premises. In particular the unique
genus root and the tree structure are conclusions. -/
lemma planarCut_tree_root_budget {g : ℕ} (hg : 1≤g) (k : Fin r → ℕ)
    (hc : D.ConnectedWithin univ) (hstable : ∀c,2<2*D.genus c+D.boundaryCount c)
    (heuler : (∑c,D.genus c)+r+1=g+D.components)
    (hplanar : ∀e,∃S,D.PlanarSide e S ∧ S.card=k e) :
    (graph D).IsTree ∧ D.components=r+1 ∧
    ∃root : Fin D.components,D.genus root=g ∧ (∀c,c≠root → D.genus c=0) ∧
      planarCuspCount D root≤∑e,k e ∧ r+rootDegree D root≤planarCuspCount D root ∧
      rootDegree D root≤r ∧ (0<r → 0<rootDegree D root) ∧
      (rootDegree D root=r → ∃f : WP.RandomGeometry.PlanarLabelBlocks n r k,
        Nonempty (MulticurveCutData.Isomorphism
          (WP.RandomGeometry.generalPlanarStarCut g n r k f) D)) ∧
      ((¬ ∃f : WP.RandomGeometry.PlanarLabelBlocks n r k,
        Nonempty (MulticurveCutData.Isomorphism
          (WP.RandomGeometry.generalPlanarStarCut g n r k f) D)) → rootDegree D root≤r-1) := by
  have hplanar0 := hplanar
  choose S hp hcard using hplanar
  choose side hside hgenus hlabels using hp
  have hcuts : ∀e,∃U,D.IsSide e U := fun e=>⟨side e,hside e⟩
  have hplanar' : ∀e,∃U,D.IsSide e U ∧ D.SideGenus U 0 := fun e=>⟨side e,hside e,hgenus e⟩
  obtain ⟨root,hroot,hzero⟩ := exists_unique_genus_root D hg hc heuler hplanar'
  have hpos : 0<D.genus root := by omega
  refine ⟨graph_isTree D hc hcuts,components_eq_edges_add_one D hc hcuts,
    root,hroot,hzero,?_,?_,rootDegree_le D root,?_,?_,?_⟩
  · apply planarCuspCount_upper D hc side hside hgenus root hpos k
    intro e
    rw [hlabels e]
    exact hcard e
  · exact planarCuspCount_lower D hc hcuts root hzero hstable
  · intro hr;exact rootDegree_pos D hc hcuts hr root
  · intro hd;exact exists_generalPlanarStar_iso D hg k hc heuler hplanar0 root hroot hzero hd
  · intro hns;exact nonstar_rootDegree_le D hg k hc heuler hplanar0 root hroot hzero hns

end WP.RandomGeometry.PlanarCut
