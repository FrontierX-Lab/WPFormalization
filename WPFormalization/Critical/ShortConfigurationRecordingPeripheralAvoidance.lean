import WPFormalization.Critical.ShortConfigurationRecordingDiskAvoidance
import WPFormalization.External.ShortPeripheralAxialGeometry
noncomputable section
set_option maxHeartbeats 0
universe u v w
namespace WP.Critical.ShortConfiguration
open Set WP.External.HyperbolicPacking WP.External.ShortLoopStraighteningGeometry
open WP.External.ShortFillingGeometry
open WP.External.ShortComplementaryRegionGeometry WP.External.ShortPeripheralAxialGeometry

variable (B:BorderedGeometry.{u,v}) (hcomplete:B.surface.domain=univ)
  (H:LoopStraighteningClassics B hcomplete) (P:PeripheralAxialClassics B hcomplete)

include hcomplete P in
lemma actual_primitive_disjoint_cusp
    {f:WP.External.ShortLoopStraighteningGeometry.ClosedLoop B.surface.Point}
    (E:CuspEndBoundedBy f) (γ:B.curves.Primitive)
    (hboundary:Disjoint (B.curves.trace γ) f.trace) :
    Disjoint (B.curves.trace γ) (range E.map) := by
  apply preconnected_avoids_closed_of_frontier (range E.map) (B.curves.trace γ)
    E.closedEmbedding.isClosed_range (primitive_trace_preconnected B γ)
    (P.cusp_no_axial f E γ)
  rwa [E.frontier_eq]

include hcomplete H in
lemma actual_primitives_disjoint_disk {ι:Type w} (γ:ι→B.curves.Primitive)
    {f:WP.External.ShortLoopStraighteningGeometry.ClosedLoop B.surface.Point}
    (E:DiskBoundedBy f) (hboundary:Disjoint (⋃i,B.curves.trace (γ i)) f.trace) :
    Disjoint (⋃i,B.curves.trace (γ i)) (range E.map) := by
  apply Set.disjoint_left.mpr
  intro p hp he
  obtain ⟨i,hi⟩:=Set.mem_iUnion.mp hp
  exact Set.disjoint_left.mp (actual_primitive_disjoint_disk B hcomplete H E (γ i)
    (hboundary.mono_left (Set.subset_iUnion (fun j=>B.curves.trace (γ j)) i))) hi he

include hcomplete P in
lemma actual_primitives_disjoint_cusp {ι:Type w} (γ:ι→B.curves.Primitive)
    {f:WP.External.ShortLoopStraighteningGeometry.ClosedLoop B.surface.Point}
    (E:CuspEndBoundedBy f) (hboundary:Disjoint (⋃i,B.curves.trace (γ i)) f.trace) :
    Disjoint (⋃i,B.curves.trace (γ i)) (range E.map) := by
  apply Set.disjoint_left.mpr
  intro p hp he
  obtain ⟨i,hi⟩:=Set.mem_iUnion.mp hp
  exact Set.disjoint_left.mp (actual_primitive_disjoint_cusp B hcomplete P E (γ i)
    (hboundary.mono_left (Set.subset_iUnion (fun j=>B.curves.trace (γ j)) i))) hi he

include hcomplete H P in
lemma actual_primitive_in_annulus_simple
    {f g:WP.External.ShortLoopStraighteningGeometry.ClosedLoop B.surface.Point}
    (E:AnnulusBetween f g) (hf:f.Simple) (hp:f.PositiveHomotopyLength)
    (γ:B.curves.Primitive) (hγ:B.curves.trace γ⊆range E.map) : SimpleTrace B γ :=
  H.simple_representative γ f hf (P.annulus_axial_class f g E γ hf hp hγ)

include hcomplete H P in
lemma actual_primitives_in_annulus_equal
    {f g:WP.External.ShortLoopStraighteningGeometry.ClosedLoop B.surface.Point}
    (E:AnnulusBetween f g) (hf:f.Simple) (hp:f.PositiveHomotopyLength)
    (γ δ:B.curves.Primitive) (hγ:B.curves.trace γ⊆range E.map)
    (hδ:B.curves.trace δ⊆range E.map) : γ=δ := by
  apply (H.class_eq γ δ).mp
  exact ClosedLoop.unoriented_trans (P.annulus_axial_class f g E γ hf hp hγ)
    (ClosedLoop.unoriented_symm (P.annulus_axial_class f g E δ hf hp hδ))

include hcomplete H P in
lemma actual_nonsimple_not_contained_annulus
    {f g:WP.External.ShortLoopStraighteningGeometry.ClosedLoop B.surface.Point}
    (E:AnnulusBetween f g) (hf:f.Simple) (hp:f.PositiveHomotopyLength)
    (γ:B.curves.Primitive) (hγ:¬SimpleTrace B γ) : ¬B.curves.trace γ⊆range E.map :=
  fun hs=>hγ (actual_primitive_in_annulus_simple B hcomplete H P E hf hp γ hs)

end WP.Critical.ShortConfiguration
