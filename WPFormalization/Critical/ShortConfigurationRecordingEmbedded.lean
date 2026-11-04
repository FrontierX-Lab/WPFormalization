import WPFormalization.Critical.ShortConfigurationRecordingArcs
noncomputable section
set_option maxHeartbeats 0
universe u v
namespace WP.Critical.ShortConfiguration
open Set Finset
open WP.External.HyperbolicPacking WP.External.ShortFillingGeometry
open scoped Classical

/- General finite embedded graph data on the actual metric space. Loops and
multiple edges are retained; parameter intervals are genuine realized arcs.
This is a definition, not an external existence/bounded-recording field. -/
structure EmbeddedNetwork (X : Type u) [MetricSpace X] where
  vertices : Finset X
  Edge : Type v
  [edgeFinite : Fintype Edge]
  start : Edge→ℝ
  finish : Edge→ℝ
  curve : Edge→ℝ→X
  interval_pos : ∀e,start e<finish e
  lipschitz : ∀e,LipschitzWith 1 (curve e)
  start_vertex : ∀e,curve e (start e)∈vertices
  finish_vertex : ∀e,curve e (finish e)∈vertices
  interval_injective : ∀e,Set.InjOn (curve e) (Ico (start e) (finish e))
  interior_avoids : ∀e,Disjoint (curve e '' Ioo (start e) (finish e)) (vertices : Set X)
  interiors_disjoint : ∀e f,e≠f→Disjoint (curve e '' Ioo (start e) (finish e))
    (curve f '' Ioo (start f) (finish f))
  vertices_covered : ∀p∈vertices,∃e,curve e (start e)=p

attribute [instance] EmbeddedNetwork.edgeFinite

def EmbeddedNetwork.support {X : Type u} [MetricSpace X] (N : EmbeddedNetwork X) : Set X :=
  ⋃e,N.curve e '' Icc (N.start e) (N.finish e)

variable (B : BorderedGeometry) (H : SegmentClassics B) {r : ℕ}
    (γ : Fin r→B.curves.Primitive) (hinj : Function.Injective γ)
    (hsimple : ∀i,SimpleTrace B (γ i)) (L : ℝ) (hL : 0<L)
    (hlength : ∀i,B.curves.length (γ i)≤L)

local notation "P" => breakpoints B H γ hinj hsimple L hL hlength
local notation "E" => NetworkEdges B H γ hinj hsimple L hL hlength

lemma networkPoints_has_parameter {p : B.surface.Point}
    (hp : p∈networkPoints B H γ hinj hsimple L hL hlength) :
    ∃i t,t∈P i ∧ curveParam B (γ i) t=p := by
  rcases mem_union.mp hp with hv|hv
  · obtain ⟨i,j,hij,hi,hj⟩ := (crossingVertices_mem B H γ hinj hsimple L hL hlength p).mp hv
    obtain ⟨t,ht,hpt⟩ := trace_has_period_parameter B (γ i) p hi
    refine ⟨i,t,mem_insert_of_mem ?_,hpt⟩
    apply (crossingParameterSet_finite_card B H γ hinj hsimple L hL hlength i).1.mem_toFinset.mpr
    exact ⟨ht,hpt ▸ hv⟩
  · obtain ⟨i,hi,rfl⟩ := mem_image.mp hv
    exact ⟨i,0,zero_mem_breakpoints B H γ hinj hsimple L hL hlength i,rfl⟩

lemma networkPoints_start_covered {p : B.surface.Point}
    (hp : p∈networkPoints B H γ hinj hsimple L hL hlength) :
    ∃e:E,curveParam B (γ e.1) (arcStart B H γ hinj hsimple L hL hlength e)=p := by
  obtain ⟨i,t,ht,hpt⟩ := networkPoints_has_parameter B H γ hinj hsimple L hL hlength hp
  let j := ((P i).orderIsoOfFin rfl).symm ⟨t,ht⟩
  have hj : subdivisionStart (P i) j=t := congrArg Subtype.val (((P i).orderIsoOfFin rfl).apply_symm_apply ⟨t,ht⟩)
  refine ⟨⟨i,j⟩,?_⟩
  change curveParam B (γ i) (subdivisionStart (P i) j)=p
  rw [hj]
  exact hpt

def tupleEmbeddedNetwork : EmbeddedNetwork B.surface.Point where
  vertices := networkPoints B H γ hinj hsimple L hL hlength
  Edge := E
  edgeFinite := show Fintype (Σi:Fin r,Fin (P i).card) from inferInstance
  start := arcStart B H γ hinj hsimple L hL hlength
  finish := arcEnd B H γ hinj hsimple L hL hlength
  curve e := curveParam B (γ e.1)
  interval_pos := arcStart_lt_end B H γ hinj hsimple L hL hlength
  lipschitz e := curveParam_lipschitz B (γ e.1)
  start_vertex := arcStart_point_mem_network B H γ hinj hsimple L hL hlength
  finish_vertex := arcEnd_point_mem_network B H γ hinj hsimple L hL hlength
  interval_injective e := by
    intro x hx y hy he
    have hx0 := arcStart_nonneg B H γ hinj hsimple L hL hlength e
    have hend := arcEnd_le_period B H γ hinj hsimple L hL hlength e
    exact hsimple e.1 ⟨hx0.trans hx.1,hx.2.trans_le hend⟩
      ⟨hx0.trans hy.1,hy.2.trans_le hend⟩ he
  interior_avoids := arcInterior_avoids_network B H γ hinj hsimple L hL hlength
  interiors_disjoint e f hef := Set.disjoint_left.mpr (fun _ hp hq=>hef
    (arcInteriors_injective B H γ hinj hsimple L hL hlength e f hp hq))
  vertices_covered _ hp := networkPoints_start_covered B H γ hinj hsimple L hL hlength hp

lemma tupleEmbeddedNetwork_support :
    (tupleEmbeddedNetwork B H γ hinj hsimple L hL hlength).support=⋃i,B.curves.trace (γ i) :=
  network_arc_support B H γ hinj hsimple L hL hlength

lemma tupleEmbeddedNetwork_vertices_bound :
    (tupleEmbeddedNetwork B H γ hinj hsimple L hL hlength).vertices.card≤
      r*r*(Nat.floor (L/segmentScale L)+1)^2+r :=
  networkPoints_card_le B H γ hinj hsimple L hL hlength

lemma tupleEmbeddedNetwork_edges_bound :
    Nat.card (tupleEmbeddedNetwork B H γ hinj hsimple L hL hlength).Edge≤
      r*(r*r*(Nat.floor (L/segmentScale L)+1)^2+1) :=
  networkEdges_card_le B H γ hinj hsimple L hL hlength

end WP.Critical.ShortConfiguration
