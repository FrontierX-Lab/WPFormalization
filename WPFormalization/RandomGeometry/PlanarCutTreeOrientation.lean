import WPFormalization.RandomGeometry.PlanarCutTreeBudget
noncomputable section
set_option maxHeartbeats 0
namespace WP.RandomGeometry.PlanarCut
open WP.External Finset
variable {n r : ℕ} (D : MulticurveCutData n r)

def childEnd (side : Fin r → Finset (Fin D.components)) (e : Fin r) : Fin D.components :=
  if D.edgeVertex (e,0)∈side e then D.edgeVertex (e,0) else D.edgeVertex (e,1)

def parentEnd (side : Fin r → Finset (Fin D.components)) (e : Fin r) : Fin D.components :=
  if D.edgeVertex (e,0)∈side e then D.edgeVertex (e,1) else D.edgeVertex (e,0)

lemma parent_child_endpoints (side : Fin r → Finset (Fin D.components)) (e : Fin r) :
    (D.edgeVertex (e,0)=parentEnd D side e ∧ D.edgeVertex (e,1)=childEnd D side e) ∨
    (D.edgeVertex (e,1)=parentEnd D side e ∧ D.edgeVertex (e,0)=childEnd D side e) := by
  classical
  by_cases h0 : D.edgeVertex (e,0)∈side e <;> simp [parentEnd,childEnd,h0]

lemma child_mem_parent_not (side : Fin r → Finset (Fin D.components))
    (hside : ∀e,D.IsSide e (side e)) (e : Fin r) :
    childEnd D side e∈side e ∧ parentEnd D side e∉side e := by
  classical
  have hx := side_crossing D e (side e) (hside e)
  by_cases h0 : D.edgeVertex (e,0)∈side e <;>
    simp [childEnd,parentEnd,h0] <;> unfold Xor at hx <;> tauto

lemma oriented_parent_representation (hc : D.ConnectedWithin univ)
    (side : Fin r → Finset (Fin D.components)) (hside : ∀e,D.IsSide e (side e))
    (hgenus : ∀e,D.SideGenus (side e) 0) (root : Fin D.components)
    (hroot : 0<D.genus root) (e : Fin r) :
    childEnd D side e≠root ∧
      ((D.edgeVertex (e,0)=parentEnd D side e ∧ D.edgeVertex (e,1)=childEnd D side e) ∨
       (D.edgeVertex (e,1)=parentEnd D side e ∧ D.edgeVertex (e,0)=childEnd D side e)) ∧
      Relation.ReflTransGen (D.AdjacentWithin (univ\side e)) root (parentEnd D side e) := by
  have hcuts : ∀e,∃U,D.IsSide e U := fun e=>⟨side e,hside e⟩
  have hn := root_not_mem_planar_side D hc hcuts root hroot e (side e) (hside e) (hgenus e)
  have hm := child_mem_parent_not D side hside e
  refine ⟨?_,parent_child_endpoints D side e,?_⟩
  · intro he;exact hn (he ▸ hm.1)
  · apply (hside e).2.2.2.2.2 root _ (parentEnd D side e) _
    · simpa using hn
    · simpa using hm.2

end WP.RandomGeometry.PlanarCut
