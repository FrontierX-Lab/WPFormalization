import WPFormalization.Critical.CutSingleRootStar
import WPFormalization.Critical.CutRestrictionCombinatorics
import WPFormalization.RandomGeometry.PantsCutIsomorphism
noncomputable section
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false
universe aa bb cc dd
namespace WP.Critical
open WP.External WP.RandomGeometry Finset
open scoped Classical

lemma pantsLeaf_degree {n t : ℕ} (D : MulticurveCutData n t)
    (e : Fin t) (c : Fin D.components) (h : PantsLeafData D e c) :
    CutGraphData.degree D c=1 := by
  have hcusps : CutGraphData.cuspCount D c=2 := by
    simpa only [CutGraphData.cuspCount,MulticurveCutData.cuspSet,
      Finset.mem_singleton,Fintype.card_subtype] using h.two_cusps
  have hb := pantsLeaf_boundaryCount D e c h
  have he := CutGraphData.boundaryCount_eq D c
  omega

abbrev mixedPantsPart {n r k : ℕ} (D : MulticurveCutData n (r+k)) : MulticurveCutData n r where
  components := D.components
  genus := D.genus
  cuspVertex := D.cuspVertex
  edgeVertex p := D.edgeVertex (p.1.castAdd k,p.2)

lemma mixedPantsPart_leaf {n r k : ℕ} (D : MulticurveCutData n (r+k))
    (leaf : Fin r → Fin D.components)
    (hleaf : ∀i,PantsLeafData D (i.castAdd k) (leaf i)) (i : Fin r) :
    PantsLeafData (mixedPantsPart D) i (leaf i) := by
  refine ⟨(hleaf i).genus_zero,(hleaf i).two_cusps,?_,?_⟩
  · ext e
    have he := congrArg (fun s : Finset (Fin (r+k)) => e.castAdd k ∈ s) (hleaf i).no_internal
    simpa only [MulticurveCutData.internalEdges,mem_filter,mem_univ,true_and,notMem_empty,
      mixedPantsPart] using he.to_iff
  · ext e
    have he := congrArg (fun s : Finset (Fin (r+k)) => e.castAdd k ∈ s) (hleaf i).crossing
    simpa only [MulticurveCutData.crossingEdges,mem_filter,mem_univ,true_and,mem_singleton,
      mixedPantsPart,Fin.castAdd_inj] using he.to_iff

variable {P : PsiTheory} {G : WeilPeterssonGeometry.{aa,bb} P}
    {H : HyperbolicCurveGeometry.{aa,bb,cc} G} (T : MulticurveTopology.{aa,bb,cc,dd} G H)
    (RG : MulticurveRestrictionGeometry G H T)
    {g n r k : ℕ} {X : G.Moduli g n (fun _ => 0)} (o : T.Orbit g n (r+k))
    (γ : Fin (r+k) → H.Primitive g n X) (ho : T.orbitMem o X γ)
    (root : Fin (T.cut o).components)
    (hroot : Stable ((T.cut o).genus root) (CutGraphData.degree (T.cut o) root))
    (hother : ∀c,c≠root → (T.cut o).genus c=0 ∧ CutGraphData.degree (T.cut o) c=1)
    (leaf : Fin r → Fin (T.cut o).components)
    (hleaf : ∀i,PantsLeafData (T.cut o) (i.castAdd k) (leaf i))
    (hloop : ∀i : Fin k,IsNonseparating T (γ (Fin.natAdd r i)))
include hroot hleaf in
lemma survivingMixed_leaf_ne_root (i : Fin r) : leaf i≠root := by
  intro he
  have hg := (hleaf i).genus_zero
  have hd := pantsLeaf_degree (T.cut o) (i.castAdd k) (leaf i) (hleaf i)
  rw [he] at hg hd
  unfold Stable at hroot
  omega

include RG ho hroot hother hleaf hloop in
lemma survivingMixed_vertices_covered (c : Fin (T.cut o).components) :
    c=root ∨ ∃i : Fin r,c=leaf i := by
  by_cases hc : c=root
  · exact Or.inl hc
  obtain ⟨e,he,hi⟩ := CutGraphData.single_root_degree_one_endpoints (T.cut o) root c
    (T.cut_connected o) hc (fun b hb => (hother b hb).2)
  refine Fin.addCases (fun j => ?_) (fun j => ?_) e he hi
  · intro he hi
    have hmem := (pantsLeaf_edge_iff (T.cut o) (j.castAdd k) (leaf j) (hleaf j) (j.castAdd k)).2 rfl
    have hlne := survivingMixed_leaf_ne_root T o root hroot leaf hleaf j
    rcases he with he|he <;> rcases hmem with hl|hl
    · exact (hlne (hl.symm.trans he.1)).elim
    · exact Or.inr ⟨j,he.2.symm.trans hl⟩
    · exact Or.inr ⟨j,he.1.symm.trans hl⟩
    · exact (hlne (hl.symm.trans he.2)).elim
  · intro he hi
    exact (actual_nonseparating_not_only_edge T RG o γ ho (Fin.natAdd r j) (hloop j)
      c root (Ne.symm hc) hi).elim

include hroot hleaf in
lemma survivingMixed_leaf_injective : Function.Injective leaf := by
  intro i j he
  have hi := (hleaf i).crossing
  rw [he,(hleaf j).crossing] at hi
  have hh : i.castAdd k=j.castAdd k := Finset.singleton_inj.mp hi.symm
  apply Fin.ext
  have heq:=congrArg Fin.val hh
  exact heq

include RG ho hroot hother hleaf hloop in
noncomputable def survivingMixedActualVertexEquiv : Fin (r+1) ≃ Fin (T.cut o).components := by
  let f : Fin (r+1) → Fin (T.cut o).components := Fin.cases root leaf
  apply Equiv.ofBijective f
  constructor
  · intro a b he
    refine Fin.cases (fun h => ?_) (fun i h => ?_) a he
    · refine Fin.cases (fun _ => rfl) (fun j h => ?_) b h
      exact (survivingMixed_leaf_ne_root T o root hroot leaf hleaf j h.symm).elim
    · refine Fin.cases (fun h => ?_) (fun j h => ?_) b h
      · exact (survivingMixed_leaf_ne_root T o root hroot leaf hleaf i h).elim
      · exact congrArg Fin.succ (survivingMixed_leaf_injective T o root hroot leaf hleaf h)
  · intro c
    rcases survivingMixed_vertices_covered T RG o γ ho root hroot hother leaf hleaf hloop c with hc|⟨i,hc⟩
    · exact ⟨0,hc.symm⟩
    · exact ⟨i.succ,hc.symm⟩
include RG ho hroot hother hleaf hloop in
lemma survivingMixed_loop_endpoints (i : Fin k) (j : Fin 2) :
    (T.cut o).edgeVertex (Fin.natAdd r i,j)=root := by
  rcases survivingMixed_vertices_covered T RG o γ ho root hroot hother leaf hleaf hloop
    ((T.cut o).edgeVertex (Fin.natAdd r i,j)) with h|⟨a,ha⟩
  · exact h
  · have he : Fin.natAdd r i=a.castAdd k :=
      (pantsLeaf_edge_iff (T.cut o) (a.castAdd k) (leaf a) (hleaf a) (Fin.natAdd r i)).mp (by
        fin_cases j
        · exact Or.inl ha
        · exact Or.inr ha)
    have hh:=congrArg Fin.val he
    simp only [Fin.val_natAdd,Fin.val_castAdd] at hh
    omega

include RG ho hroot hother hleaf hloop in
lemma survivingMixed_root_genus : (T.cut o).genus root=g-k := by
  let v := survivingMixedActualVertexEquiv T RG o γ ho root hroot hother leaf hleaf hloop
  have hc := Fintype.card_congr v
  simp only [Fintype.card_fin] at hc
  have hs : (∑c,(T.cut o).genus c)=(T.cut o).genus root := by
    have he := v.sum_comp (T.cut o).genus
    change (∑c : Fin (r+1),(T.cut o).genus (Fin.cases root leaf c))=_ at he
    simp only [Fin.sum_univ_succ,Fin.cases_zero,Fin.cases_succ,
      fun i => (hleaf i).genus_zero,sum_const_zero,add_zero] at he
    exact he.symm
  have he := T.cut_euler o
  rw [hs] at he
  omega

include RG ho hroot hother hleaf hloop in
noncomputable def survivingMixedClassificationIso :
    (survivingMixedCutGraph g n r k
      (pantsCutLabels (mixedPantsPart (T.cut o)) leaf (mixedPantsPart_leaf (T.cut o) leaf hleaf))).Isomorphism (T.cut o) := by
  classical
  let D := T.cut o
  let Dp := mixedPantsPart D
  let hp := mixedPantsPart_leaf D leaf hleaf
  let f := pantsCutLabels Dp leaf hp
  let v := survivingMixedActualVertexEquiv T RG o γ ho root hroot hother leaf hleaf hloop
  have hv0 : v (0 : Fin (r+1))=root := rfl
  have hvs (i : Fin r) : v i.succ=leaf i := rfl
  have hne (i : Fin r) : leaf i≠root := survivingMixed_leaf_ne_root T o root hroot leaf hleaf i
  have hend (i : Fin r) :
      (D.edgeVertex (i.castAdd k,0)=root ∧ D.edgeVertex (i.castAdd k,1)=leaf i) ∨
      (D.edgeVertex (i.castAdd k,0)=leaf i ∧ D.edgeVertex (i.castAdd k,1)=root) := by
    obtain ⟨e,he,_⟩ := CutGraphData.single_root_degree_one_endpoints D root (leaf i)
      (T.cut_connected o) (hne i) (fun b hb => (hother b hb).2)
    have hi := (pantsLeaf_edge_iff D (i.castAdd k) (leaf i) (hleaf i) e).mp (by
      rcases he with he|he
      · exact Or.inr he.2
      · exact Or.inl he.1)
    exact hi ▸ he
  change (survivingMixedCutGraph g n r k f).Isomorphism D
  refine ⟨v,Fin.append (fun i => decide (D.edgeVertex (i.castAdd k,0)=leaf i)) (fun _ => false),?_,?_,?_⟩
  · intro c
    refine Fin.cases ?_ (fun i => ?_) c
    · exact survivingMixed_root_genus T RG o γ ho root hroot hother leaf hleaf hloop
    · exact (hleaf i).genus_zero
  · intro j
    by_cases hj : ∃p : Fin r×Fin 2,f.val p=j
    · obtain ⟨p,hpair⟩ := hj
      subst j
      change v ((pantsCutGraph (g-k) n r f).cuspVertex (f.val p))=D.cuspVertex (f.val p)
      rw [pantsCutGraph_cusp_pair,hvs]
      exact (pantsCutLabels_vertex Dp leaf hp p.1 p.2).symm
    · have hz : (survivingMixedCutGraph g n r k f).cuspVertex j=(0 : Fin (r+1)) := dif_neg hj
      rw [hz]
      change v (0 : Fin (r+1))=D.cuspVertex j
      rw [hv0]
      rcases survivingMixed_vertices_covered T RG o γ ho root hroot hother leaf hleaf hloop (D.cuspVertex j) with h|⟨i,hi⟩
      · exact h.symm
      · obtain ⟨a,ha⟩ := pantsCutLabels_covers_leaf Dp leaf hp i j hi
        exact (hj ⟨(i,a),ha⟩).elim
  · intro e j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) e
    · simp only [survivingMixedCutGraph,Fin.addCases_left,Fin.append_left]
      change v (if j=0 then (0 : Fin (r+1)) else i.succ)=
        D.edgeVertex (i.castAdd k,if decide (D.edgeVertex (i.castAdd k,0)=leaf i) then j.rev else j)
      have he := hend i
      fin_cases j <;> by_cases h0 : D.edgeVertex (i.castAdd k,0)=leaf i
      · have h1 : D.edgeVertex (i.castAdd k,1)=root := by
          rcases he with he|he
          · exact (hne i (h0.symm.trans he.1)).elim
          · exact he.2
        simpa [h0] using hv0.trans h1.symm
      · have hr : D.edgeVertex (i.castAdd k,0)=root := by tauto
        simpa [h0] using hv0.trans hr.symm
      · simpa [h0] using (hvs i).trans h0.symm
      · have h1 : D.edgeVertex (i.castAdd k,1)=leaf i := by tauto
        simpa [h0] using (hvs i).trans h1.symm
    · simpa [survivingMixedCutGraph] using hv0.trans
        (survivingMixed_loop_endpoints T RG o γ ho root hroot hother leaf hleaf hloop i j).symm

lemma singleRoot_of_partition {n t u : ℕ} (D : MulticurveCutData n t)
    (hpart : CutDataHasPartition D u 0 1) :
    ∃root : Fin D.components, Stable (D.genus root) (CutGraphData.degree D root) ∧
      ∀c,c≠root → D.genus c=0 ∧ CutGraphData.degree D c=1 := by
  obtain ⟨R,hR⟩ := hpart
  refine ⟨R.stableVertex 0,hR.2.2 0,?_⟩
  intro c hc
  rcases hcase : R.vertices c with i|i
  · have he : c=R.oneVertex i := by
      apply R.vertices.injective
      simp only [CutVertexPartition.oneVertex,Equiv.apply_symm_apply,hcase]
    exact he ▸ hR.1 i
  · rcases i with i|i
    · exact Fin.elim0 i
    · have he : c=R.stableVertex 0 := by
        apply R.vertices.injective
        simp only [CutVertexPartition.stableVertex,Equiv.apply_symm_apply,hcase,Fin.eq_zero i]
      exact (hc he).elim

include RG ho in
lemma survivingMixed_classify_partition (hg : 1≤g) (u : ℕ)
    (hpart : CutDataHasPartition (T.cut o) u 0 1)
    (hpants : ∀i : Fin r,∃S : Finset (Fin n),
      H.planarSide (γ (i.castAdd k))=some S ∧ S.card=2)
    (hnonsep : ∀i : Fin k,IsNonseparating T (γ (Fin.natAdd r i))) :
    ∃f : PantsLabels n r, Nonempty ((survivingMixedCutGraph g n r k f).Isomorphism (T.cut o)) := by
  have hp (i : Fin r) : ∃c : Fin (T.cut o).components,
      PantsLeafData (T.cut o) (i.castAdd k) c := by
    obtain ⟨S,hS,hcard⟩ := hpants i
    exact planar_two_cusp_leaf (T.cut o) (T.cut_stable o) (i.castAdd k) S
      ((T.planarSide_iff o X γ ho hg (i.castAdd k) S).mp hS) hcard
  choose leaf hleaf using hp
  obtain ⟨root,hr,hother⟩ := singleRoot_of_partition (T.cut o) hpart
  let f := pantsCutLabels (mixedPantsPart (T.cut o)) leaf (mixedPantsPart_leaf (T.cut o) leaf hleaf)
  exact ⟨f,⟨survivingMixedClassificationIso T RG o γ ho root hr hother leaf hleaf hnonsep⟩⟩

end WP.Critical
