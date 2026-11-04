import WPFormalization.External.ShortFillingGeometry
import WPFormalization.Critical.ShortConfigurationRecordingGrid
noncomputable section
set_option maxHeartbeats 0
namespace WP.Critical.ShortConfiguration
open Set
open WP.External.HyperbolicPacking WP.External.ShortFillingGeometry
open scoped Classical

lemma segmentScale_pos {L : ℝ} (hL : 0<L) : 0<segmentScale L := by
  apply Real.log_pos
  apply (one_lt_div (Real.sinh_pos_iff.mpr (by positivity : 0<L/4))).mpr
  exact Real.sinh_lt_cosh _

def intersectionParams (B : BorderedGeometry) (γ δ : B.curves.Primitive) : Set (ℝ×ℝ) :=
  {p | p.1∈Ico 0 (B.curves.length γ) ∧ p.2∈Ico 0 (B.curves.length δ) ∧
    curveParam B γ p.1=curveParam B δ p.2}

lemma intersection_params_finite_card_bound (B : BorderedGeometry) (H : SegmentClassics B)
    (γ δ : B.curves.Primitive) (hγ : SimpleTrace B γ) (hδ : SimpleTrace B δ)
    (hne : γ≠δ) (L : ℝ) (hL : 0<L) (hγL : B.curves.length γ≤L) (hδL : B.curves.length δ≤L) :
    (intersectionParams B γ δ).Finite ∧
    Nat.card (intersectionParams B γ δ)≤(Nat.floor (L/segmentScale L)+1)^2 := by
  apply grid_finite_card_bound _ L (segmentScale_pos hL)
  · intro p hp
    exact ⟨⟨hp.1.1,hp.1.2.le.trans hγL⟩,⟨hp.2.1.1,hp.2.1.2.le.trans hδL⟩⟩
  · intro p hp q hq hpq
    have hs : p.1≠q.1 := by
      intro he
      have ht : p.2=q.2 := hδ hp.2.1 hq.2.1 (by rw [←hp.2.2,←hq.2.2,he])
      exact hpq (Prod.ext he ht)
    have ht : p.2≠q.2 := by
      intro he
      exact hs (hγ hp.1 hq.1 (by rw [hp.2.2,hq.2.2,he]))
    exact H.endpoint_comparison γ δ hγ hδ hne L hL hγL hδL
      p.1 q.1 p.2 q.2 hp.1 hq.1 hp.2.1 hq.2.1 hs ht hp.2.2 hq.2.2

lemma curveParam_periodic (B : BorderedGeometry) (γ : B.curves.Primitive) :
    Function.Periodic (curveParam B γ) (B.curves.length γ) := by
  intro t
  have h := (B.surface.fibers ((B.curves.representative γ).axis t)
    ((B.curves.representative γ).in_domain t)
    ((B.curves.representative γ).deck.val ((B.curves.representative γ).axis t))
    (B.surface.invariant _ _ ((B.curves.representative γ).in_domain t))).mpr
    ⟨(B.curves.representative γ).deck,rfl⟩
  rw [(B.curves.representative γ).translates] at h
  exact h.symm

lemma trace_has_period_parameter (B : BorderedGeometry) (γ : B.curves.Primitive)
    (p : B.surface.Point) (hp : p∈B.curves.trace γ) :
    ∃t∈Ico 0 (B.curves.length γ),curveParam B γ t=p := by
  obtain ⟨_,⟨t,rfl⟩,rfl⟩ := hp
  have hpos : 0<B.curves.length γ := (B.curves.representative γ).period_pos
  refine ⟨toIcoMod hpos 0 t,toIcoMod_mem_Ico' hpos t,?_⟩
  exact (curveParam_periodic B γ).sub_zsmul_eq (toIcoDiv hpos 0 t)

lemma intersection_trace_finite_card_bound (B : BorderedGeometry) (H : SegmentClassics B)
    (γ δ : B.curves.Primitive) (hγ : SimpleTrace B γ) (hδ : SimpleTrace B δ)
    (hne : γ≠δ) (L : ℝ) (hL : 0<L) (hγL : B.curves.length γ≤L) (hδL : B.curves.length δ≤L) :
    (B.curves.trace γ∩B.curves.trace δ).Finite ∧
    Nat.card {p : B.surface.Point //p∈B.curves.trace γ∩B.curves.trace δ}≤(Nat.floor (L/segmentScale L)+1)^2 := by
  obtain ⟨hf,hcard⟩ := intersection_params_finite_card_bound B H γ δ hγ hδ hne L hL hγL hδL
  let f : (intersectionParams B γ δ)→{p : B.surface.Point //p∈B.curves.trace γ∩B.curves.trace δ} := fun p=>
    ⟨curveParam B γ p.val.1,⟨⟨_,⟨p.val.1,rfl⟩,rfl⟩,
      ⟨_,⟨p.val.2,rfl⟩,p.property.2.2.symm⟩⟩⟩
  have hs : Function.Surjective f := by
    intro p
    obtain ⟨s,hs,hes⟩ := trace_has_period_parameter B γ p.val p.property.1
    obtain ⟨t,ht,het⟩ := trace_has_period_parameter B δ p.val p.property.2
    refine ⟨⟨(s,t),hs,ht,hes.trans het.symm⟩,?_⟩
    exact Subtype.ext hes
  haveI : Finite (intersectionParams B γ δ) := hf.to_subtype
  haveI : Finite {p : B.surface.Point //p∈B.curves.trace γ∩B.curves.trace δ} := Finite.of_surjective f hs
  exact ⟨Set.toFinite _,(Nat.card_le_card_of_surjective f hs).trans hcard⟩

end WP.Critical.ShortConfiguration
