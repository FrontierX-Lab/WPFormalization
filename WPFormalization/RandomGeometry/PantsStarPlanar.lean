import WPFormalization.RandomGeometry.PantsStarTopology
import WPFormalization.RandomGeometry.PantsCutClassification

/-! Every canonical pants edge cuts off its actual two labeled cusps. -/
noncomputable section
namespace WP.RandomGeometry
open WP.External

set_option backward.isDefEq.respectTransparency false in
lemma pantsStar_leafData (g n r : ℕ) (f : PantsLabels n r) (i : Fin r) :
    PantsLeafData (pantsCutGraph g n r f) i i.succ := by
  classical
  refine ⟨by simp [pantsCutGraph],?_,?_,?_⟩
  · simpa [MulticurveCutData.cuspSet,Fintype.card_subtype] using
      (Fintype.card_congr (pantsStarLeafCuspEquiv g n r f i)).symm
  · ext j
    simp [MulticurveCutData.internalEdges,pantsCutGraph,eq_comm]
  · ext j
    simp [MulticurveCutData.crossingEdges,pantsCutGraph,Xor,eq_comm]

lemma pantsStar_planarSide (g n r : ℕ) (f : PantsLabels n r) (i : Fin r) :
    (pantsCutGraph g n r f).PlanarSide i
      ((pantsCutGraph g n r f).cuspSet {i.succ}) := by
  classical
  let D := pantsCutGraph g n r f
  let leaf : Fin D.components := i.succ
  let root : Fin D.components := ⟨0,by change 0 < r+1; omega⟩
  let V := Finset.univ \ ({leaf} : Finset (Fin D.components))
  have hroot : root ∈ V := by
    simp only [V,Finset.mem_sdiff,Finset.mem_univ,true_and,Finset.mem_singleton]
    intro h
    have hh := congrArg Fin.val h
    change 0=i.val+1 at hh
    omega
  have hadj (j : Fin r) (hj : j.succ ∈ V) : D.AdjacentWithin V root j.succ := by
    refine ⟨hroot,hj,j,Or.inl ?_⟩
    constructor <;> simp [D,pantsCutGraph,root]
  have hadj' (j : Fin r) (hj : j.succ ∈ V) : D.AdjacentWithin V j.succ root := by
    refine ⟨hj,hroot,j,Or.inr ?_⟩
    constructor <;> simp [D,pantsCutGraph,root]
  have hr (c : Fin D.components) : c ∈ V → Relation.ReflTransGen (D.AdjacentWithin V) root c := by
    refine Fin.cases (fun _ => Relation.ReflTransGen.refl)
      (fun j hj => Relation.ReflTransGen.single (hadj j hj)) c
  have hr' (c : Fin D.components) : c ∈ V → Relation.ReflTransGen (D.AdjacentWithin V) c root := by
    refine Fin.cases (fun _ => Relation.ReflTransGen.refl)
      (fun j hj => Relation.ReflTransGen.single (hadj' j hj)) c
  have hconn : D.ConnectedWithin V := by
    refine ⟨⟨root,hroot⟩,?_⟩
    intro a ha b hb
    exact (hr' a ha).trans (hr b hb)
  have hsconn : D.ConnectedWithin {leaf} := by
    refine ⟨Finset.singleton_nonempty _,?_⟩
    intro a ha b hb
    rw [Finset.mem_singleton] at ha hb
    subst a
    subst b
    exact Relation.ReflTransGen.refl
  have hp := pantsStar_leafData g n r f i
  refine ⟨{leaf},⟨Finset.singleton_nonempty _,⟨root,hroot⟩,hp.crossing,hsconn,hconn⟩,?_,rfl⟩
  have hg0 : D.genus leaf=0 := hp.genus_zero
  have hi0 : D.internalEdges {leaf}=∅ := hp.no_internal
  have he : D.genus leaf+(D.internalEdges {leaf}).card+1=1+0 := by rw [hg0,hi0]; simp
  simpa only [MulticurveCutData.SideGenus,Finset.sum_singleton,Finset.card_singleton] using he

end WP.RandomGeometry
