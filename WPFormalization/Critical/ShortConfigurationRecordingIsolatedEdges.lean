import WPFormalization.Critical.ShortConfigurationRecordingActualCut
noncomputable section
set_option maxHeartbeats 0
universe u v
namespace WP.Critical.ShortConfiguration
open Set Finset WP.External.HyperbolicPacking WP.External.ShortFillingGeometry
open WP.External.ShortRegularNeighborhoodGeometry WP.External.ShortLoopStraighteningGeometry
open scoped Classical
variable (B:BorderedGeometry.{u,v}) {r:ℕ} (γ:Fin r→B.curves.Primitive)

def isolatedIndices : Finset (Fin r) :=
  univ.filter (fun i=>∀j,j≠i→Disjoint (B.curves.trace (γ i)) (B.curves.trace (γ j)))

def isolatedGeodesics : Finset B.curves.Primitive :=
  (isolatedIndices B γ).image γ

lemma isolatedGeodesics_card_le : (isolatedGeodesics B γ).card ≤ r :=
  Finset.card_image_le.trans (Finset.card_filter_le _ _ |>.trans_eq (by simp))

lemma isolatedGeodesics_length_le (hinj:Function.Injective γ) :
    (∑δ∈isolatedGeodesics B γ,B.curves.length δ) ≤ ∑i,B.curves.length (γ i) := by
  rw [isolatedGeodesics,Finset.sum_image (fun i hi j hj he=>hinj he)]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    (fun i hi hnot=>(B.curves.representative (γ i)).period_pos.le)

lemma isolatedGeodesics_disjoint {δ ε:B.curves.Primitive}
    (hδ:δ∈isolatedGeodesics B γ) (hε:ε∈isolatedGeodesics B γ) (hne:δ≠ε) :
    Disjoint (B.curves.trace δ) (B.curves.trace ε) := by
  obtain ⟨i,hi,rfl⟩:=Finset.mem_image.mp hδ
  obtain ⟨j,hj,rfl⟩:=Finset.mem_image.mp hε
  exact (Finset.mem_filter.mp hi).2 j (fun h=>hne (h.symm ▸ rfl))

variable (N:EmbeddedNetwork.{u,0} B.surface.Point) (D:NeighborhoodData N)
  (C:WP.External.FiniteCyclicIntervalGeometry.Classics)
  (hcomplete:B.surface.domain=univ) (LS:LoopStraighteningClassics B hcomplete)

def augmentedGeodesics : Finset B.curves.Primitive :=
  essentialGeodesics B N D C hcomplete LS ∪ isolatedGeodesics B γ

lemma augmentedGeodesics_simple (hsimple:∀i,SimpleTrace B (γ i))
    {δ:B.curves.Primitive} (hδ:δ∈augmentedGeodesics B γ N D C hcomplete LS) :
    SimpleTrace B δ := by
  rcases Finset.mem_union.mp hδ with hδ|hδ
  · exact essentialGeodesics_simple B N D C hcomplete LS hδ
  · obtain ⟨i,hi,rfl⟩:=Finset.mem_image.mp hδ
    exact hsimple i

lemma augmentedGeodesics_disjoint (hsimple:∀i,SimpleTrace B (γ i))
    (htrace:∀i,B.curves.trace (γ i)⊆N.support)
    {δ ε:B.curves.Primitive}
    (hδ:δ∈augmentedGeodesics B γ N D C hcomplete LS)
    (hε:ε∈augmentedGeodesics B γ N D C hcomplete LS) (hne:δ≠ε) :
    Disjoint (B.curves.trace δ) (B.curves.trace ε) := by
  rcases Finset.mem_union.mp hδ with hd|hd <;>
    rcases Finset.mem_union.mp hε with he|he
  · exact essentialGeodesics_disjoint B N D C hcomplete LS hd he hne
  · obtain ⟨i,hi,rfl⟩:=Finset.mem_image.mp he
    exact ((essentialGeodesics_edge_or_disjoint B N D C hcomplete LS
      (hsimple i) (htrace i) hd).resolve_left (Ne.symm hne)).symm
  · obtain ⟨i,hi,rfl⟩:=Finset.mem_image.mp hd
    exact (essentialGeodesics_edge_or_disjoint B N D C hcomplete LS
      (hsimple i) (htrace i) he).resolve_left hne
  · exact isolatedGeodesics_disjoint B γ hd he hne

lemma augmentedGeodesics_card_le :
    (augmentedGeodesics B γ N D C hcomplete LS).card ≤ 2*Nat.card N.Edge+r :=
  (Finset.card_union_le _ _).trans (Nat.add_le_add
    (essentialGeodesics_card_le B N D C hcomplete LS) (isolatedGeodesics_card_le B γ))

lemma augmentedGeodesics_length_le (hinj:Function.Injective γ) :
    (∑δ∈augmentedGeodesics B γ N D C hcomplete LS,B.curves.length δ) ≤
      2*(∑e,(N.finish e-N.start e))+(∑i,B.curves.length (γ i)) := by
  have he:=Finset.sum_union_inter (s₁:=essentialGeodesics B N D C hcomplete LS)
    (s₂:=isolatedGeodesics B γ) (f:=B.curves.length)
  have hn:0 ≤ ∑δ∈essentialGeodesics B N D C hcomplete LS∩isolatedGeodesics B γ,
      B.curves.length δ:=Finset.sum_nonneg (fun δ hδ=>(B.curves.representative δ).period_pos.le)
  have hs:=essentialGeodesics_length_le B N D C hcomplete LS
  have hi:=isolatedGeodesics_length_le B γ hinj
  dsimp [augmentedGeodesics]
  linarith

lemma nonisolated_not_mem_essentialGeodesics (hinj:Function.Injective γ)
    (hsimple:∀i,SimpleTrace B (γ i)) (htrace:∀i,B.curves.trace (γ i)⊆N.support)
    (i:Fin r) (hi:i∉isolatedIndices B γ) :
    γ i∉essentialGeodesics B N D C hcomplete LS := by
  have hnot:¬∀j,j≠i→Disjoint (B.curves.trace (γ i)) (B.curves.trace (γ j)):=by
    simpa [isolatedIndices] using hi
  push_neg at hnot
  obtain ⟨j,hji,hnd⟩:=hnot
  intro hmem
  have ho:=essentialGeodesics_edge_or_disjoint B N D C hcomplete LS
    (hsimple j) (htrace j) hmem
  rcases ho with he|hd
  · exact hji (hinj he)
  · exact hnd hd.symm

lemma nonisolated_disjoint_augmented (hinj:Function.Injective γ)
    (hsimple:∀i,SimpleTrace B (γ i)) (htrace:∀i,B.curves.trace (γ i)⊆N.support)
    (i:Fin r) (hi:i∉isolatedIndices B γ) {δ:B.curves.Primitive}
    (hδ:δ∈augmentedGeodesics B γ N D C hcomplete LS) :
    Disjoint (B.curves.trace (γ i)) (B.curves.trace δ) := by
  rcases Finset.mem_union.mp hδ with hδ|hδ
  · exact (essentialGeodesics_edge_or_disjoint B N D C hcomplete LS
      (hsimple i) (htrace i) hδ).resolve_left (fun he=>
      nonisolated_not_mem_essentialGeodesics B γ N D C hcomplete LS hinj hsimple htrace i hi (he.symm ▸ hδ))
  · obtain ⟨j,hj,rfl⟩:=Finset.mem_image.mp hδ
    have hji:j≠i:=by
      intro he
      exact hi (he ▸ hj)
    exact ((Finset.mem_filter.mp hj).2 i (Ne.symm hji)).symm

end WP.Critical.ShortConfiguration
