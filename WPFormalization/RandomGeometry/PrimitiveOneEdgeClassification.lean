import WPFormalization.Critical.CutGraphData
import WPFormalization.RandomGeometry.PantsOrbitLabels

/-! Exhaustive local classification of the actual one-edge cut: one connected
component, or two components, and a zero-genus component is a genuine planar
side of this same cut. -/
noncomputable section
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false
universe u v w z
namespace WP.RandomGeometry
open WP.External Finset
namespace OneEdgeCut
variable {n : ℕ} (D : MulticurveCutData n 1)

lemma components_pos (hc : D.ConnectedWithin univ) : 0<D.components := by
  obtain ⟨c,hc⟩ := hc.1
  exact lt_of_le_of_lt (Nat.zero_le c.val) c.isLt

lemma components_le_two (hc : D.ConnectedWithin univ) : D.components≤2 := by
  have h := Fintype.card_le_of_surjective D.edgeVertex
    (WP.Critical.CutGraphData.edgeVertex_surjective D (by norm_num) hc)
  simpa using h

lemma components_one_or_two (hc : D.ConnectedWithin univ) :
    D.components=1 ∨ D.components=2 := by
  have hp := components_pos D hc
  have hu := components_le_two D hc
  omega

lemma edgeVertex_injective (hc : D.ConnectedWithin univ) (hQ : D.components=2) :
    Function.Injective D.edgeVertex := by
  have he : Fintype.card (Fin 1×Fin 2)=Fintype.card (Fin D.components) := by simp [hQ]
  exact (Fintype.bijective_iff_surjective_and_card _).mpr
    ⟨WP.Critical.CutGraphData.edgeVertex_surjective D (by norm_num) hc,he⟩ |>.1

lemma endpoints_ne (hc : D.ConnectedWithin univ) (hQ : D.components=2) :
    D.edgeVertex (0,0)≠D.edgeVertex (0,1) := by
  intro he
  have h := edgeVertex_injective D hc hQ he
  exact (by decide : (0 : Fin 2)≠1) (congrArg Prod.snd h)

lemma vertex_endpoints (hc : D.ConnectedWithin univ) (c : Fin D.components) :
    c=D.edgeVertex (0,0) ∨ c=D.edgeVertex (0,1) := by
  obtain ⟨⟨e,j⟩,he⟩ := WP.Critical.CutGraphData.edgeVertex_surjective D (by norm_num) hc c
  have he0 : e=0 := Subsingleton.elim _ _
  subst e
  fin_cases j <;> simp_all

lemma complement_singleton (hc : D.ConnectedWithin univ) (hQ : D.components=2)
    (c : Fin D.components) : ∃d : Fin D.components,d≠c ∧ univ\{c}={d} := by
  rcases vertex_endpoints D hc c with hc0|hc1
  · refine ⟨D.edgeVertex (0,1),?_,?_⟩
    · simpa [hc0] using (endpoints_ne D hc hQ).symm
    · ext a
      simp only [mem_sdiff,mem_univ,true_and,mem_singleton]
      constructor
      · intro ha
        rcases vertex_endpoints D hc a with ha0|ha1
        · exact (ha (ha0.trans hc0.symm)).elim
        · exact ha1
      · rintro rfl
        simpa [hc0] using (endpoints_ne D hc hQ).symm
  · refine ⟨D.edgeVertex (0,0),?_,?_⟩
    · simpa [hc1] using endpoints_ne D hc hQ
    · ext a
      simp only [mem_sdiff,mem_univ,true_and,mem_singleton]
      constructor
      · intro ha
        rcases vertex_endpoints D hc a with ha0|ha1
        · exact ha0
        · exact (ha (ha1.trans hc1.symm)).elim
      · rintro rfl
        simpa [hc1] using endpoints_ne D hc hQ

lemma singleton_connected (c : Fin D.components) : D.ConnectedWithin {c} := by
  refine ⟨singleton_nonempty _,?_⟩
  intro a ha b hb
  rw [mem_singleton] at ha hb
  subst a
  subst b
  exact Relation.ReflTransGen.refl

lemma singleton_isSide (hc : D.ConnectedWithin univ) (hQ : D.components=2)
    (c : Fin D.components) : D.IsSide 0 {c} := by
  obtain ⟨d,hd,hcomp⟩ := complement_singleton D hc hQ c
  refine ⟨singleton_nonempty _,hcomp ▸ singleton_nonempty _,?_,
    singleton_connected D c,hcomp ▸ singleton_connected D d⟩
  apply Finset.ext
  intro e
  have he : e=0 := Subsingleton.elim _ _
  subst e
  simp only [MulticurveCutData.crossingEdges,mem_filter,mem_univ,true_and,mem_singleton]
  rcases vertex_endpoints D hc c with hc0|hc1
  · simp [hc0,(endpoints_ne D hc hQ).symm]
  · simp [hc1,endpoints_ne D hc hQ]

lemma singleton_internal_empty (hc : D.ConnectedWithin univ) (hQ : D.components=2)
    (c : Fin D.components) : D.internalEdges {c}=∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro e he
  obtain ⟨_,h0,h1⟩ := mem_filter.mp he
  have he0 : e=0 := Subsingleton.elim _ _
  subst e
  apply endpoints_ne D hc hQ
  exact (mem_singleton.mp h0).trans (mem_singleton.mp h1).symm

lemma genus_zero_planarSide (hc : D.ConnectedWithin univ) (hQ : D.components=2)
    (c : Fin D.components) (hg0 : D.genus c=0) :
    D.PlanarSide 0 (D.cuspSet {c}) := by
  refine ⟨{c},singleton_isSide D hc hQ c,?_,rfl⟩
  simp [MulticurveCutData.SideGenus,hg0,singleton_internal_empty D hc hQ c]

end OneEdgeCut
variable {P : PsiTheory} {G : WeilPeterssonGeometry.{u,v} P}
    {H : HyperbolicCurveGeometry.{u,v,w} G} (T : MulticurveTopology.{u,v,w,z} G H)

lemma primitive_one_edge_nonplanar_cases {g n : ℕ} (hg : 1≤g) (o : T.Orbit g n 1)
    (X : G.Moduli g n (fun _=>0)) (γ : Fin 1→H.Primitive g n X)
    (ho : T.orbitMem o X γ) (hnoplanar : H.planarSide (γ 0)=none) :
    (T.cut o).components=1 ∨
      ((T.cut o).components=2 ∧ ∀c,1≤(T.cut o).genus c) := by
  rcases OneEdgeCut.components_one_or_two (T.cut o) (T.cut_connected o) with h1|h2
  · exact Or.inl h1
  · right
    refine ⟨h2,?_⟩
    intro c
    by_contra hz
    have hzero : (T.cut o).genus c=0 := by omega
    have hs := OneEdgeCut.genus_zero_planarSide (T.cut o) (T.cut_connected o) h2 c hzero
    have hh := (T.planarSide_iff o X γ ho hg 0 _).mpr hs
    rw [hnoplanar] at hh
    cases hh

end WP.RandomGeometry
