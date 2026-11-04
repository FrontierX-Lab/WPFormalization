import WPFormalization.Critical.CutActualEstimate
import WPFormalization.Critical.SurvivingMixedCurveTypes
import WPFormalization.RandomGeometry.PantsCutClassification
noncomputable section
set_option maxHeartbeats 0
namespace WP.Critical
open WP.External WP.RandomGeometry Finset
open scoped Classical
namespace CutGraphData
variable {n t : ℕ} (D : MulticurveCutData n t)

lemma degree_one_unique_halfEdge (c : Fin D.components) (hc : degree D c=1) :
    ∃p : Fin t×Fin 2, D.edgeVertex p=c ∧ ∀q, D.edgeVertex q=c → q=p := by
  obtain ⟨p,hp⟩ := Fintype.card_eq_one_iff.mp hc
  exact ⟨p.val,p.property,fun q hq => congrArg Subtype.val (hp ⟨q,hq⟩)⟩

lemma connected_not_adjacent_degree_one (root c a : Fin D.components)
    (hconn : D.ConnectedWithin univ) (hc : c≠root) (ha : a≠root)
    (e : Fin t) (he : (D.edgeVertex (e,0)=c ∧ D.edgeVertex (e,1)=a) ∨
      (D.edgeVertex (e,1)=c ∧ D.edgeVertex (e,0)=a))
    (hic : ∀p : Fin t×Fin 2,D.edgeVertex p=c → p.1=e)
    (hia : ∀p : Fin t×Fin 2,D.edgeVertex p=a → p.1=e) : False := by
  have hb {b : Fin D.components} (h : Relation.ReflTransGen (D.AdjacentWithin univ) c b) : b=c ∨ b=a := by
    induction h with
    | refl => exact Or.inl rfl
    | @tail b d h hbd ih =>
      obtain ⟨_,_,j,hor⟩ := hbd
      have hj : j=e := by
        rcases ih with hb|hb <;> rcases hor with hh|hh
        · exact hic (j,0) (hh.1.trans hb)
        · exact hic (j,1) (hh.1.trans hb)
        · exact hia (j,0) (hh.1.trans hb)
        · exact hia (j,1) (hh.1.trans hb)
      subst j
      rcases he with hh|hh <;> rcases hor with hq|hq
      · exact Or.inr (hq.2.symm.trans hh.2)
      · exact Or.inl (hq.2.symm.trans hh.1)
      · exact Or.inl (hq.2.symm.trans hh.1)
      · exact Or.inr (hq.2.symm.trans hh.2)
  rcases hb (hconn.2 c (mem_univ _) root (mem_univ _)) with heq|heq
  · exact hc heq.symm
  · exact ha heq.symm

lemma single_root_degree_one_endpoints (root c : Fin D.components)
    (hconn : D.ConnectedWithin univ) (hc : c≠root)
    (hdeg : ∀b,b≠root → degree D b=1) :
    ∃ e : Fin t,
      ((D.edgeVertex (e,0)=root ∧ D.edgeVertex (e,1)=c) ∨
       (D.edgeVertex (e,0)=c ∧ D.edgeVertex (e,1)=root)) ∧
      (∀p : Fin t×Fin 2,D.edgeVertex p=c → p.1=e) := by
  obtain ⟨⟨e,s⟩,hs,hu⟩ := degree_one_unique_halfEdge D c (hdeg c hc)
  let a := D.edgeVertex (e,s.rev)
  have ha : a≠c := by
    intro ha
    have heq := congrArg Prod.snd (hu (e,s.rev) ha)
    fin_cases s <;> simp at heq
  have hinc : ∀p : Fin t×Fin 2,D.edgeVertex p=c → p.1=e := by
    intro p hp
    exact congrArg Prod.fst (hu p hp)
  have he : (D.edgeVertex (e,0)=c ∧ D.edgeVertex (e,1)=a) ∨
      (D.edgeVertex (e,1)=c ∧ D.edgeVertex (e,0)=a) := by
    fin_cases s
    · exact Or.inl ⟨hs,rfl⟩
    · exact Or.inr ⟨hs,rfl⟩
  have haroot : a=root := by
    by_contra hane
    obtain ⟨p,hp,hpu⟩ := degree_one_unique_halfEdge D a (hdeg a hane)
    have hia : ∀q : Fin t×Fin 2,D.edgeVertex q=a → q.1=e := by
      intro q hq
      have hp0 := hpu (e,s.rev) rfl
      exact congrArg Prod.fst ((hpu q hq).trans hp0.symm)
    exact connected_not_adjacent_degree_one D root c a hconn hc hane e he hinc hia
  refine ⟨e,?_,hinc⟩
  rw [haroot] at he
  exact he.imp (fun h => Or.inr h) (fun h => Or.inl ⟨h.2,h.1⟩) |>.elim id id
end CutGraphData
end WP.Critical
