import WPFormalization.Critical.CutCanonicalPartition
import WPFormalization.Critical.CutFiniteSkeletonCover
import WPFormalization.Critical.CutSingleRootStar
noncomputable section
set_option maxHeartbeats 0
namespace WP.Critical
open WP.External WP.RandomGeometry Finset
open scoped Classical

lemma cutConnected_singleton {n t : ℕ} (D : MulticurveCutData n t) (c : Fin D.components) :
    D.ConnectedWithin {c} := by
  refine ⟨singleton_nonempty _,?_⟩
  intro a ha b hb
  rw [mem_singleton] at ha hb
  subst a b
  exact Relation.ReflTransGen.refl

lemma oneEdge_planar_leaf {n : ℕ} (D : MulticurveCutData n 1)
    (hcomp : D.components=2) (c a : Fin D.components) (hne : c≠a)
    (hg : D.genus c=0) (hd : CutGraphData.degree D c=1) :
    D.PlanarSide 0 (D.cuspSet {c}) := by
  have hcover (b : Fin D.components) : b=c ∨ b=a := by
    have hval : c.val≠a.val := fun h => hne (Fin.ext h)
    have hc := c.isLt
    have ha := a.isLt
    have hb := b.isLt
    by_cases hbc : b.val=c.val
    · exact Or.inl (Fin.ext hbc)
    · exact Or.inr (Fin.ext (by omega))
  obtain ⟨⟨e,s⟩,hs,hu⟩ := CutGraphData.degree_one_unique_halfEdge D c hd
  have he : e=0 := Fin.eq_zero e
  subst e
  have hother : D.edgeVertex (0,s.rev)=a := by
    rcases hcover (D.edgeVertex (0,s.rev)) with hc|ha
    · have hh := congrArg Prod.snd (hu (0,s.rev) hc)
      fin_cases s <;> simp at hh
    · exact ha
  have hor : (D.edgeVertex (0,0)=c ∧ D.edgeVertex (0,1)=a) ∨
      (D.edgeVertex (0,0)=a ∧ D.edgeVertex (0,1)=c) := by
    fin_cases s
    · exact Or.inl ⟨hs,hother⟩
    · exact Or.inr ⟨hother,hs⟩
  have hni : D.internalEdges {c}=∅ := by
    ext j
    rw [Fin.eq_zero j]
    rcases hor with h|h <;> simp [MulticurveCutData.internalEdges,h.1,h.2,hne,hne.symm]
  have hcross : D.crossingEdges {c}={0} := by
    ext j
    rw [Fin.eq_zero j]
    rcases hor with h|h <;> simp [MulticurveCutData.crossingEdges,h.1,h.2,hne,hne.symm,Xor]
  have hcompl : univ\({c} : Finset (Fin D.components))={a} := by
    ext b
    simp only [mem_sdiff,mem_univ,true_and,mem_singleton]
    constructor
    · intro hb
      exact (hcover b).resolve_left hb
    · intro hb
      subst b
      exact hne.symm
  refine ⟨{c},⟨singleton_nonempty _,?_,hcross,cutConnected_singleton D c,?_⟩,?_,rfl⟩
  · rw [hcompl]
    exact singleton_nonempty _
  · rw [hcompl]
    exact cutConnected_singleton D a
  · simp only [MulticurveCutData.SideGenus,sum_singleton,card_singleton,hg,hni,card_empty]

lemma oneEdge_singleRoot_nonPants_marked {n u : ℕ} (D : MulticurveCutData n 1)
    (hconn : D.ConnectedWithin univ)
    (hstable : ∀c,Stable (D.genus c) (D.boundaryCount c))
    (hcomp : D.components≠1) (hpart : CutDataHasPartition D u 0 1)
    (hnoPants : ¬∃S : Finset (Fin n),D.PlanarSide 0 S ∧ S.card=2) :
    CutDataHasMarkedPartition D u 0 1 := by
  have hle := CutGraphData.components_le_twice_edges D (by omega) hconn
  have hpos : 0<D.components := by
    obtain ⟨c,hc⟩ := hconn.1
    exact Nat.zero_lt_of_lt c.isLt
  have hc2 : D.components=2 := by omega
  obtain ⟨R,hR⟩ := hpart
  have hu := R.components_eq
  have hu1 : u=1 := by omega
  let i : Fin u := ⟨0,by omega⟩
  let c := R.oneVertex i
  let a := R.stableVertex 0
  have hne : c≠a := by
    intro he
    have hh := congrArg R.vertices he
    simpa only [c,a,CutVertexPartition.oneVertex,CutVertexPartition.stableVertex,
      Equiv.apply_symm_apply,reduceCtorEq] using hh
  have hplanar : D.PlanarSide 0 (D.cuspSet {c}) :=
    oneEdge_planar_leaf D hc2 c a hne (hR.1 i).1 (hR.1 i).2
  have hcard : CutGraphData.cuspCount D c=(D.cuspSet {c}).card := by
    simp only [CutGraphData.cuspCount,MulticurveCutData.cuspSet,mem_singleton,Fintype.card_subtype]
  have hnot2 : CutGraphData.cuspCount D c≠2 := by
    intro h2
    exact hnoPants ⟨_,hplanar,hcard ▸ h2⟩
  have hst := hstable c
  have hb := CutGraphData.boundaryCount_eq D c
  have hg0 : D.genus c=0 := (hR.1 i).1
  have hd1 : CutGraphData.degree D c=1 := (hR.1 i).2
  unfold Stable at hst
  refine ⟨R,i,hR,?_⟩
  change 3≤CutGraphData.cuspCount D c
  omega
end WP.Critical
