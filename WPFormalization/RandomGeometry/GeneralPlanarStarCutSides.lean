import WPFormalization.RandomGeometry.GeneralPlanarStarCutTopology

/-! Each ordered canonical star edge cuts off exactly its own labeled leaf. -/
noncomputable section
namespace WP.RandomGeometry
open WP.External

set_option backward.isDefEq.respectTransparency false in
lemma generalPlanarStarCut_leaf_no_internal (g n r : ℕ) (k : Fin r → ℕ)
    (f : PlanarLabelBlocks n r k) (i : Fin r) :
    (generalPlanarStarCut g n r k f).internalEdges {i.succ} = ∅ := by
  classical
  ext j
  simp [MulticurveCutData.internalEdges,generalPlanarStarCut,eq_comm]

set_option backward.isDefEq.respectTransparency false in
lemma generalPlanarStarCut_leaf_crossing (g n r : ℕ) (k : Fin r → ℕ)
    (f : PlanarLabelBlocks n r k) (i : Fin r) :
    (generalPlanarStarCut g n r k f).crossingEdges {i.succ} = {i} := by
  classical
  ext j
  simp [MulticurveCutData.crossingEdges,generalPlanarStarCut,Xor,eq_comm]

lemma generalPlanarStarCut_planarSide (g n r : ℕ) (k : Fin r → ℕ)
    (f : PlanarLabelBlocks n r k) (i : Fin r) :
    (generalPlanarStarCut g n r k f).PlanarSide i (f.labelSet i) := by
  classical
  let D := generalPlanarStarCut g n r k f
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
    constructor <;> simp [D,generalPlanarStarCut,root]
  have hadj' (j : Fin r) (hj : j.succ ∈ V) : D.AdjacentWithin V j.succ root := by
    refine ⟨hj,hroot,j,Or.inr ?_⟩
    constructor <;> simp [D,generalPlanarStarCut,root]
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
  refine ⟨{leaf},⟨Finset.singleton_nonempty _,⟨root,hroot⟩,
    generalPlanarStarCut_leaf_crossing g n r k f i,hsconn,hconn⟩,?_,?_⟩
  · have hg0 : D.genus leaf=0 := by simp [D,generalPlanarStarCut,leaf]
    have hi0 : D.internalEdges {leaf}=∅ := generalPlanarStarCut_leaf_no_internal g n r k f i
    have he : D.genus leaf+(D.internalEdges {leaf}).card+1=1+0 := by rw [hg0,hi0]; simp
    simpa only [MulticurveCutData.SideGenus,Finset.sum_singleton,Finset.card_singleton] using he
  · exact generalPlanarStarCut_cuspSet_leaf g n r k f i

end WP.RandomGeometry
