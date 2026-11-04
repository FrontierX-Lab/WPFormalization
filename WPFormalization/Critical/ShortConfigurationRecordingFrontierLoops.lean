import WPFormalization.Critical.ShortConfigurationRecordingLoopHomotopy
noncomputable section
universe u v
namespace WP.Critical.ShortConfiguration
open Set WP.External.ShortRegularNeighborhoodGeometry
open WP.External.ShortLoopStraighteningGeometry
variable {X:Type u} [MetricSpace X] (N:EmbeddedNetwork.{u,v} X)
lemma NeighborhoodData.frontierLoop_simple (D:NeighborhoodData N)
    (l:WP.External.ShortLoopStraighteningGeometry.ClosedLoop (BoundaryWalkSpace N D.rotation))
    (hl:l.Simple) : (NeighborhoodData.frontierLoop N D l).Simple := by
  intro a ha b hb he
  apply hl ha hb
  apply D.boundaryHomeo.injective
  exact Subtype.ext (Subtype.ext he)

lemma NeighborhoodData.frontierLoop_disjoint (D:NeighborhoodData N)
    (l m:WP.External.ShortLoopStraighteningGeometry.ClosedLoop (BoundaryWalkSpace N D.rotation))
    (hlm:Disjoint l.trace m.trace) :
    Disjoint (NeighborhoodData.frontierLoop N D l).trace
      (NeighborhoodData.frontierLoop N D m).trace := by
  apply Set.disjoint_left.mpr
  rintro p ⟨t,ht⟩ ⟨s,hs⟩
  have he:D.boundaryHomeo (l.map t)=D.boundaryHomeo (m.map s):=
    Subtype.ext (Subtype.ext (ht.trans hs.symm))
  have heq:l.map t=m.map s:=D.boundaryHomeo.injective he
  exact Set.disjoint_left.mp hlm ⟨t,rfl⟩ ⟨s,heq.symm⟩

lemma NeighborhoodData.frontierLoop_disjoint_support (D:NeighborhoodData N)
    (l:WP.External.ShortLoopStraighteningGeometry.ClosedLoop (BoundaryWalkSpace N D.rotation)) :
    Disjoint (NeighborhoodData.frontierLoop N D l).trace N.support := by
  apply Set.disjoint_left.mpr
  rintro p ⟨t,ht⟩ hp
  have hf:(D.boundaryHomeo (l.map t)).val.val∈frontier D.region:=
    (D.boundaryHomeo (l.map t)).property
  change (D.boundaryHomeo (l.map t)).val.val=p at ht
  have hs:(D.boundaryHomeo (l.map t)).val.val∈interior D.region:=
    ht.symm ▸ D.support_interior hp
  exact hf.2 hs

end WP.Critical.ShortConfiguration
