import WPFormalization.External.ShortFillingGeometry
noncomputable section
set_option maxHeartbeats 0
namespace WP.Critical.ShortConfiguration
open Set

/- A connected set disjoint from actual cuts lies in one unique actual
connected component. This topological step is proved, not a recording field. -/
lemma preconnected_unique_component {X : Type*} [TopologicalSpace X]
    (U W : Set X) (hW : W.Nonempty) (hpre : IsPreconnected W) (hsub : W⊆U) :
    ∃!c:ConnectedComponents U,∀p (hp:p∈W),ConnectedComponents.mk ⟨p,hsub hp⟩=c := by
  obtain ⟨p,hp⟩ := hW
  refine ⟨ConnectedComponents.mk ⟨p,hsub hp⟩,?_,?_⟩
  · intro q hq
    have hh := hpre.subset_connectedComponentIn hp hsub hq
    rw [connectedComponentIn_eq_image (hsub hp)] at hh
    obtain ⟨q',hq',he⟩ := hh
    have hqe : q'=(⟨q,hsub hq⟩ : U) := Subtype.ext he
    rw [hqe] at hq'
    exact ConnectedComponents.coe_eq_coe'.mpr hq'
  · intro c hc
    exact (hc p hp).symm

open WP.External WP.External.HyperbolicPacking WP.External.ShortFillingGeometry

lemma cut_realization_unique_piece {P : WP.PsiTheory}
    {G : WeilPeterssonGeometry P} {H : HyperbolicCurveGeometry G}
    {A : AmbientRealization H} {T : MulticurveTopology G H}
    {g n k : ℕ} {o : T.Orbit g n k} {X : G.Moduli g n (fun _=>0)}
    {κ : Fin k→H.Primitive g n X} {hκ : T.orbitMem o X κ}
    (R : CutComponentRealization A T o X κ hκ)
    (W : Set (A.model g n X).surface.Point) (hW : W.Nonempty)
    (hpre : IsPreconnected W) (hsub : W⊆cutComplement A κ) :
    ∃!c:Fin (T.cut o).components,W⊆(R.piece c).point '' intrinsicInterior (R.piece c).model := by
  obtain ⟨q,hq,hqunique⟩ := preconnected_unique_component (cutComplement A κ) W hW hpre hsub
  refine ⟨R.componentEquiv q,?_,?_⟩
  · intro p hp
    rw [R.image_eq]
    exact ⟨hsub hp,congrArg R.componentEquiv (hq p hp)⟩
  · intro c hc
    obtain ⟨p,hp⟩ := hW
    obtain ⟨hpu,he⟩ := (R.image_eq c ▸ hc hp)
    exact he.symm.trans (congrArg R.componentEquiv (hq p hp))

end WP.Critical.ShortConfiguration
