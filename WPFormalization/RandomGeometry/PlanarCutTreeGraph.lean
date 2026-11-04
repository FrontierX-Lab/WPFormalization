import WPFormalization.External.MulticurveCutData
import Mathlib.Combinatorics.SimpleGraph.Acyclic
/-! The graph of an actual cut with a separating side at every edge is a tree.
All edges and vertices retain their original labels. Loops and parallel edges
are excluded from the actual side witnesses, not assumed away. -/
noncomputable section
set_option maxHeartbeats 0
namespace WP.RandomGeometry.PlanarCut
open WP.External Finset
variable {n r : ℕ} (D : MulticurveCutData n r)

def graph : SimpleGraph (Fin D.components) where
  Adj a b := a≠b ∧ ∃e : Fin r,
    (D.edgeVertex (e,0)=a ∧ D.edgeVertex (e,1)=b) ∨
    (D.edgeVertex (e,1)=a ∧ D.edgeVertex (e,0)=b)
  symm := ⟨by rintro a b ⟨hne,e,he|he⟩ <;> exact ⟨hne.symm,e,by tauto⟩⟩
  loopless := ⟨by intro a h; exact h.1 rfl⟩

def edgePair (e : Fin r) : Sym2 (Fin D.components) :=
  s(D.edgeVertex (e,0),D.edgeVertex (e,1))

lemma crossing_iff (U : Finset (Fin D.components)) (e : Fin r) :
    e∈D.crossingEdges U ↔ Xor (D.edgeVertex (e,0)∈U) (D.edgeVertex (e,1)∈U) := by
  classical
  simp [MulticurveCutData.crossingEdges]

lemma side_crossing (e : Fin r) (U : Finset (Fin D.components)) (hU : D.IsSide e U) :
    Xor (D.edgeVertex (e,0)∈U) (D.edgeVertex (e,1)∈U) := by
  apply (crossing_iff D U e).1
  rw [hU.2.2.1]
  simp

lemma side_mem_iff_of_ne (e f : Fin r) (U : Finset (Fin D.components))
    (hU : D.IsSide e U) (hf : f≠e) :
    D.edgeVertex (f,0)∈U ↔ D.edgeVertex (f,1)∈U := by
  have hn : f∉D.crossingEdges U := by rw [hU.2.2.1];simpa using hf
  rw [crossing_iff] at hn
  unfold Xor at hn
  tauto

lemma endpoints_ne (hcuts : ∀e,∃U,D.IsSide e U) (e : Fin r) :
    D.edgeVertex (e,0)≠D.edgeVertex (e,1) := by
  obtain ⟨U,hU⟩ := hcuts e
  have hx := side_crossing D e U hU
  intro he
  rw [he] at hx
  simpa only [xor_self] using hx

lemma edgePair_injective (hcuts : ∀e,∃U,D.IsSide e U) : Function.Injective (edgePair D) := by
  intro e f he
  obtain ⟨U,hU⟩ := hcuts e
  have hx := side_crossing D e U hU
  by_contra hne
  have hh := side_mem_iff_of_ne D e f U hU (Ne.symm hne)
  change s(_,_)=s(_,_) at he
  rcases Sym2.eq_iff.mp he with he|he <;> rcases he with ⟨h0,h1⟩ <;>
    rw [h0,h1] at hx <;> unfold Xor at hx <;> tauto

lemma graph_connected (hc : D.ConnectedWithin univ) : (graph D).Connected := by
  haveI : Nonempty (Fin D.components) := ⟨hc.1.choose⟩
  refine ⟨?_⟩
  intro a b
  rw [SimpleGraph.reachable_iff_reflTransGen]
  have hp := hc.2 a (mem_univ _) b (mem_univ _)
  induction hp with
  | refl => exact .refl
  | @tail b c hp hadj ih =>
    by_cases heq : b=c
    · subst c; exact ih
    · exact ih.tail ⟨heq,hadj.2.2⟩

lemma mem_iff_of_adj_delete (e : Fin r) (U : Finset (Fin D.components))
    (hU : D.IsSide e U) {a b : Fin D.components}
    (hab : ((graph D).deleteEdges {edgePair D e}).Adj a b) : (a∈U ↔ b∈U) := by
  obtain ⟨hgraph,hn⟩ := SimpleGraph.deleteEdges_adj.mp hab
  obtain ⟨hne,f,hf|hf⟩ := hgraph
  all_goals
    have hfe : f≠e := by
      intro h
      subst f
      apply hn
      simp only [Set.mem_singleton_iff,edgePair]
      rcases hf with ⟨rfl,rfl⟩
      first | rfl | exact Sym2.eq_swap
    have hm := side_mem_iff_of_ne D e f U hU hfe
    rcases hf with ⟨h0,h1⟩
    first | exact h0 ▸ h1 ▸ hm | exact h1 ▸ h0 ▸ hm.symm

lemma edgePair_bridge (e : Fin r) (U : Finset (Fin D.components))
    (hU : D.IsSide e U) : (graph D).IsBridge (edgePair D e) := by
  change ¬ ((graph D).deleteEdges {edgePair D e}).Reachable
    (D.edgeVertex (e,0)) (D.edgeVertex (e,1))
  intro hp
  have hpres : ∀ {a b}, ((graph D).deleteEdges {edgePair D e}).Reachable a b →
      (a∈U ↔ b∈U) := by
    intro a b hp
    rw [SimpleGraph.reachable_iff_reflTransGen] at hp
    induction hp with
    | refl => exact Iff.rfl
    | tail hp hadj ih => exact ih.trans (mem_iff_of_adj_delete D e U hU hadj)
  have heq := hpres hp
  have hx := side_crossing D e U hU
  unfold Xor at hx
  tauto

lemma graph_isTree (hc : D.ConnectedWithin univ) (hcuts : ∀e,∃U,D.IsSide e U) :
    (graph D).IsTree := by
  refine ⟨graph_connected D hc,SimpleGraph.isAcyclic_iff_forall_adj_isBridge.mpr ?_⟩
  intro a b hab
  obtain ⟨_,e,he|he⟩ := hab
  all_goals
    obtain ⟨U,hU⟩ := hcuts e
    have hb := edgePair_bridge D e U hU
    rcases he with ⟨rfl,rfl⟩
    first | exact hb | simpa only [edgePair,Sym2.eq_swap] using hb

def edgePairEquiv (hcuts : ∀e,∃U,D.IsSide e U) : Fin r ≃ (graph D).edgeSet :=
  Equiv.ofBijective (fun e => ⟨edgePair D e,by
    exact (graph D).mem_edgeSet.mpr ⟨endpoints_ne D hcuts e,e,Or.inl ⟨rfl,rfl⟩⟩⟩) (by
      constructor
      · intro a b hab
        exact edgePair_injective D hcuts (congrArg Subtype.val hab)
      · rintro ⟨p,hp⟩
        induction p using Sym2.inductionOn with
        | _ a b =>
          obtain ⟨_,e,he|he⟩ := (graph D).mem_edgeSet.mp hp
          all_goals
            refine ⟨e,Subtype.ext ?_⟩
            rcases he with ⟨rfl,rfl⟩
            first | rfl | exact Sym2.eq_swap)

lemma components_eq_edges_add_one (hc : D.ConnectedWithin univ)
    (hcuts : ∀e,∃U,D.IsSide e U) : D.components=r+1 := by
  have ht := (SimpleGraph.isTree_iff_connected_and_card.mp (graph_isTree D hc hcuts)).2
  have he : Nat.card (graph D).edgeSet=r := by
    rw [←Nat.card_congr (edgePairEquiv D hcuts)]
    simp
  simpa only [he,Nat.card_eq_fintype_card,Fintype.card_fin] using ht.symm

end WP.RandomGeometry.PlanarCut
