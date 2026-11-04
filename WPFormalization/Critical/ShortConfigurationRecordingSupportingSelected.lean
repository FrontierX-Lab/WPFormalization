import WPFormalization.Critical.ShortConfigurationRecordingSupportingIdentification
import WPFormalization.Critical.ShortConfigurationRecordingPieceCut

noncomputable section
set_option maxHeartbeats 0
universe u v w z q
namespace WP.Critical.ShortConfiguration
open Set Finset WP.External WP.External.HyperbolicPacking WP.External.ShortFillingGeometry
open WP.External.ShortIntrinsicRegionGeometry WP.External.ShortIntrinsicBoundaryGeometry
open WP.External.ShortSupportingPieceGeometry
open scoped Classical

lemma supporting_trace_subset_carrier {B : BorderedGeometry.{u,v}}
    (s : Finset B.curves.Primitive) (γ : B.curves.Primitive) (hγ : γ∈s) :
    B.curves.trace γ⊆carrier B s := by
  intro p hp
  exact Set.mem_iUnion.mpr ⟨γ,Set.mem_iUnion.mpr ⟨hγ,hp⟩⟩

lemma supporting_carrier_nonempty {B : BorderedGeometry.{u,v}}
    (s : Finset B.curves.Primitive) (hs : s.Nonempty) : (carrier B s).Nonempty := by
  obtain ⟨γ,hγ⟩:=hs
  obtain ⟨p,hp⟩:=primitive_trace_nonempty B γ
  exact ⟨p,supporting_trace_subset_carrier s γ hγ hp⟩

lemma supporting_carrier_subset_image {B : BorderedGeometry.{u,v}}
    {s : Finset B.curves.Primitive} (S : SupportingPieceData B s) :
    carrier B s⊆S.piece.point '' intrinsicInterior S.piece.model := by
  intro p hp
  obtain ⟨γ,hγ⟩:=Set.mem_iUnion.mp hp
  obtain ⟨hγs,hγp⟩:=Set.mem_iUnion.mp hγ
  exact S.contains γ hγs hγp

/-- The selected set is the literal finite image of the component choices. -/
def supportingSelectedSet {ι α : Type*} [Fintype ι] [DecidableEq α] (select : ι→α) : Finset α :=
  Finset.univ.image select

lemma supportingSelectedSet_card_le {ι α : Type*} [Fintype ι] [DecidableEq α] (select : ι→α) :
    (supportingSelectedSet select).card≤Fintype.card ι :=
  Finset.card_image_le.trans_eq (by simp)

variable {P : WP.PsiTheory} {G : WeilPeterssonGeometry.{u,v} P}
  {H : HyperbolicCurveGeometry.{u,v,w} G}
  {A : AmbientRealization H} {T : MulticurveTopology.{u,v,w,z} G H}
  {g n k : ℕ} {o : T.Orbit g n k} {X : G.Moduli g n (fun _=>0)}
  {κ : Fin k→H.Primitive g n X} {hκ : T.orbitMem o X κ}

/-- Connected actual carrier avoiding the cuts determines a component; the
existing supporting identification theorem proves equality of the open images. -/
lemma supporting_exists_actual_cut_component
    {s : Finset (A.model g n X).curves.Primitive}
    (S : SupportingPieceData (A.model g n X) s) (hs : s.Nonempty)
    (R : CutComponentRealization A T o X κ hκ)
    (AR : ∀c,IntrinsicRegionData (A.model g n X) (R.piece c))
    (BR : ∀c,IntrinsicBoundaryData (A.model g n X) (R.piece c))
    (hconn : IsPreconnected (carrier (A.model g n X) s))
    (havoid : carrier (A.model g n X) s⊆cutComplement A κ)
    (hboundary : ∀j,∃e,S.piece.primitiveProjection (S.piece.boundary.curve j)=
      A.primitiveEquiv g n X (κ e)) :
    ∃c,S.piece.point '' intrinsicInterior S.piece.model=
      (R.piece c).point '' intrinsicInterior (R.piece c).model := by
  obtain ⟨c,hc,_⟩:=cut_realization_unique_piece R _
    (supporting_carrier_nonempty s hs) hconn havoid
  refine ⟨c,supporting_piece_eq_actual_cut_piece S hs R AR BR c ?_ hboundary⟩
  intro γ hγ
  exact (supporting_trace_subset_carrier s γ hγ).trans hc

/-- A raw frontier-in-cut-union condition also suffices. Minimality first
puts the entire supporting image in the carrier's actual cut component. -/
lemma supporting_exists_actual_cut_component_of_frontier
    {s : Finset (A.model g n X).curves.Primitive}
    (S : SupportingPieceData (A.model g n X) s) (hs : s.Nonempty)
    (R : CutComponentRealization A T o X κ hκ)
    (AR : ∀c,IntrinsicRegionData (A.model g n X) (R.piece c))
    (BR : ∀c,IntrinsicBoundaryData (A.model g n X) (R.piece c))
    (hconn : IsPreconnected (carrier (A.model g n X) s))
    (havoid : carrier (A.model g n X) s⊆cutComplement A κ)
    (hfrontier : frontier (S.piece.point '' intrinsicInterior S.piece.model)⊆
      ⋃e,(A.model g n X).curves.trace (A.primitiveEquiv g n X (κ e))) :
    ∃c,S.piece.point '' intrinsicInterior S.piece.model=
      (R.piece c).point '' intrinsicInterior (R.piece c).model := by
  obtain ⟨c,hc,_⟩:=cut_realization_unique_piece R _
    (supporting_carrier_nonempty s hs) hconn havoid
  have hminimal:=S.minimal (R.piece c) (AR c) (BR c) (by
    intro γ hγ
    exact (supporting_trace_subset_carrier s γ hγ).trans hc)
  have hwhole : S.piece.point '' intrinsicInterior S.piece.model⊆cutComplement A κ := by
    intro p hp
    obtain ⟨hpu,_⟩:=R.image_eq c ▸ hminimal hp
    exact hpu
  have hne : (S.piece.point '' intrinsicInterior S.piece.model).Nonempty :=
    (supporting_carrier_nonempty s hs).mono (supporting_carrier_subset_image S)
  obtain ⟨d,hd,_⟩:=open_region_eq_actual_cut_piece R _ S.piece.image_open
    S.piece.image_connected hne hwhole hfrontier
  exact ⟨d,hd⟩

lemma supporting_cut_component_negativeEuler_eq
    {s : Finset (A.model g n X).curves.Primitive}
    (S : SupportingPieceData (A.model g n X) s)
    (R : CutComponentRealization A T o X κ hκ)
    (AR : ∀c,IntrinsicRegionData (A.model g n X) (R.piece c))
    (c : Fin (T.cut o).components)
    (heq : S.piece.point '' intrinsicInterior S.piece.model=
      (R.piece c).point '' intrinsicInterior (R.piece c).model) :
    (R.piece c).model.negativeEuler=S.piece.model.negativeEuler := by
  apply negativeEuler_eq_of_area_eq
  exact (AR c).area_image.symm.trans
    ((congrArg (A.model g n X).surface.area heq.symm).trans S.region.area_image)

/-- Finite image selection from proved actual image equalities. The Euler
bound is transferred through actual area equality, only for selected pieces. -/
lemma exists_supporting_selected_indices_of_same_images
    {ι : Type q} [Fintype ι]
    (s : ι→Finset (A.model g n X).curves.Primitive)
    (S : ∀a,SupportingPieceData (A.model g n X) (s a))
    (R : CutComponentRealization A T o X κ hκ)
    (AR : ∀c,IntrinsicRegionData (A.model g n X) (R.piece c))
    (K : ℝ) (hK : ∀a,((S a).piece.model.negativeEuler:ℝ)≤K)
    (himages : ∀a,∃c,(S a).piece.point '' intrinsicInterior (S a).piece.model=
      (R.piece c).point '' intrinsicInterior (R.piece c).model) :
    ∃select : ι→Fin (T.cut o).components,
      (∀a,(S a).piece.point '' intrinsicInterior (S a).piece.model=
        (R.piece (select a)).point '' intrinsicInterior (R.piece (select a)).model) ∧
      (supportingSelectedSet select).card≤Fintype.card ι ∧
      (∀c∈supportingSelectedSet select,((R.piece c).model.negativeEuler:ℝ)≤K) ∧
      (∀γ : (A.model g n X).curves.Primitive,
        (∃a,(A.model g n X).curves.trace γ⊆carrier (A.model g n X) (s a))→
        ∃c∈supportingSelectedSet select,
          (A.model g n X).curves.trace γ⊆
            (R.piece c).point '' intrinsicInterior (R.piece c).model) := by
  choose select hselect using himages
  refine ⟨select,hselect,supportingSelectedSet_card_le select,?_,?_⟩
  · intro c hc
    obtain ⟨a,_,rfl⟩:=Finset.mem_image.mp hc
    rw [supporting_cut_component_negativeEuler_eq (S a) R AR (select a) (hselect a)]
    exact hK a
  · intro γ hγ
    obtain ⟨a,ha⟩:=hγ
    refine ⟨select a,Finset.mem_image.mpr ⟨a,Finset.mem_univ _,rfl⟩,?_⟩
    rw [←hselect a]
    exact ha.trans (supporting_carrier_subset_image (S a))

/-- Actual supporting pieces produce a finite selected cut-component set.
All carrier, boundary and Euler premises are ordinary frontend obligations. -/
lemma exists_supporting_selected_indices
    {ι : Type q} [Fintype ι]
    (s : ι→Finset (A.model g n X).curves.Primitive)
    (S : ∀a,SupportingPieceData (A.model g n X) (s a))
    (hs : ∀a,(s a).Nonempty)
    (R : CutComponentRealization A T o X κ hκ)
    (AR : ∀c,IntrinsicRegionData (A.model g n X) (R.piece c))
    (BR : ∀c,IntrinsicBoundaryData (A.model g n X) (R.piece c))
    (hconn : ∀a,IsPreconnected (carrier (A.model g n X) (s a)))
    (havoid : ∀a,carrier (A.model g n X) (s a)⊆cutComplement A κ)
    (hboundary : ∀a j,∃e,(S a).piece.primitiveProjection ((S a).piece.boundary.curve j)=
      A.primitiveEquiv g n X (κ e))
    (K : ℝ) (hK : ∀a,((S a).piece.model.negativeEuler:ℝ)≤K) :
    ∃select : ι→Fin (T.cut o).components,
      (∀a,(S a).piece.point '' intrinsicInterior (S a).piece.model=
        (R.piece (select a)).point '' intrinsicInterior (R.piece (select a)).model) ∧
      (supportingSelectedSet select).card≤Fintype.card ι ∧
      (∀c∈supportingSelectedSet select,((R.piece c).model.negativeEuler:ℝ)≤K) ∧
      (∀γ : (A.model g n X).curves.Primitive,
        (∃a,(A.model g n X).curves.trace γ⊆carrier (A.model g n X) (s a))→
        ∃c∈supportingSelectedSet select,
          (A.model g n X).curves.trace γ⊆
            (R.piece c).point '' intrinsicInterior (R.piece c).model) := by
  apply exists_supporting_selected_indices_of_same_images s S R AR K hK
  intro a
  exact supporting_exists_actual_cut_component (S a) (hs a) R AR BR
    (hconn a) (havoid a) (hboundary a)

lemma exists_supporting_selected_indices_of_frontier
    {ι : Type q} [Fintype ι]
    (s : ι→Finset (A.model g n X).curves.Primitive)
    (S : ∀a,SupportingPieceData (A.model g n X) (s a))
    (hs : ∀a,(s a).Nonempty)
    (R : CutComponentRealization A T o X κ hκ)
    (AR : ∀c,IntrinsicRegionData (A.model g n X) (R.piece c))
    (BR : ∀c,IntrinsicBoundaryData (A.model g n X) (R.piece c))
    (hconn : ∀a,IsPreconnected (carrier (A.model g n X) (s a)))
    (havoid : ∀a,carrier (A.model g n X) (s a)⊆cutComplement A κ)
    (hfrontier : ∀a,frontier ((S a).piece.point '' intrinsicInterior (S a).piece.model)⊆
      ⋃e,(A.model g n X).curves.trace (A.primitiveEquiv g n X (κ e)))
    (K : ℝ) (hK : ∀a,((S a).piece.model.negativeEuler:ℝ)≤K) :
    ∃select : ι→Fin (T.cut o).components,
      (∀a,(S a).piece.point '' intrinsicInterior (S a).piece.model=
        (R.piece (select a)).point '' intrinsicInterior (R.piece (select a)).model) ∧
      (supportingSelectedSet select).card≤Fintype.card ι ∧
      (∀c∈supportingSelectedSet select,((R.piece c).model.negativeEuler:ℝ)≤K) ∧
      (∀γ : (A.model g n X).curves.Primitive,
        (∃a,(A.model g n X).curves.trace γ⊆carrier (A.model g n X) (s a))→
        ∃c∈supportingSelectedSet select,
          (A.model g n X).curves.trace γ⊆
            (R.piece c).point '' intrinsicInterior (R.piece c).model) := by
  apply exists_supporting_selected_indices_of_same_images s S R AR K hK
  intro a
  exact supporting_exists_actual_cut_component_of_frontier (S a) (hs a) R AR BR
    (hconn a) (havoid a) (hfrontier a)

end WP.Critical.ShortConfiguration
