import WPFormalization.Critical.ShortConfigurationRecordingCycleLength
import WPFormalization.Critical.ShortConfigurationRecordingFrontierLoops
import WPFormalization.Critical.ShortConfigurationRecordingBoundaryComparison
noncomputable section
set_option maxHeartbeats 0
universe u v z
namespace WP.Critical.ShortConfiguration
open Set Finset WP.External.HyperbolicPacking WP.External.ShortFillingGeometry
open WP.External.ShortRegularNeighborhoodGeometry WP.External.ShortLoopStraighteningGeometry
open scoped Classical ENNReal
variable (B:BorderedGeometry.{u,v}) (N:EmbeddedNetwork.{u,z} B.surface.Point)
  (D:NeighborhoodData N) (C:WP.External.FiniteCyclicIntervalGeometry.Classics)

def frontierCycle (c:D.rotation.BoundaryCycle N) :
    WP.External.ShortLoopStraighteningGeometry.ClosedLoop B.surface.Point :=
  NeighborhoodData.frontierLoop N D (cycleClosedLoop N D.rotation C c)

def cycleWidth (c:D.rotation.BoundaryCycle N) :ℝ :=
  ∑d∈D.rotation.cycleDarts N c,(N.finish d.1-N.start d.1)

lemma cycleWidth_nonneg (c:D.rotation.BoundaryCycle N) : 0≤cycleWidth B N D c := by
  exact Finset.sum_nonneg (fun d hd=>(sub_pos.mpr (N.interval_pos d.1)).le)

lemma frontierCycle_simple (c:D.rotation.BoundaryCycle N) : (frontierCycle B N D C c).Simple :=
  NeighborhoodData.frontierLoop_simple N D _ (cycleClosedLoop_simple N D.rotation C c)

lemma frontierCycle_disjoint {c d:D.rotation.BoundaryCycle N} (hne:c≠d) :
    Disjoint (frontierCycle B N D C c).trace (frontierCycle B N D C d).trace :=
  NeighborhoodData.frontierLoop_disjoint N D _ _
    (cycleClosedLoop_traces_disjoint N D.rotation C hne)

lemma frontierCycle_disjoint_support (c:D.rotation.BoundaryCycle N) :
    Disjoint (frontierCycle B N D C c).trace N.support :=
  NeighborhoodData.frontierLoop_disjoint_support N D _

lemma frontierCycle_homotopic_walk (c:D.rotation.BoundaryCycle N) :
    (frontierCycle B N D C c).FreelyHomotopic
      (ClosedLoop.postcompose (cycleClosedLoop N D.rotation C c) (boundaryWalk N D.rotation)) :=
  NeighborhoodData.frontier_homotopic_walk N D _

def EssentialCycle := {c:D.rotation.BoundaryCycle N // (frontierCycle B N D C c).PositiveHomotopyLength}

instance : Fintype (EssentialCycle B N D C) :=
  inferInstanceAs (Fintype {c:D.rotation.BoundaryCycle N // (frontierCycle B N D C c).PositiveHomotopyLength})

def essentialFrontier (c:EssentialCycle B N D C) :
    WP.External.ShortLoopStraighteningGeometry.ClosedLoop B.surface.Point := frontierCycle B N D C c.val

lemma essentialFrontier_simple (c:EssentialCycle B N D C) : (essentialFrontier B N D C c).Simple :=
  frontierCycle_simple B N D C c.val

lemma essentialFrontier_positive (c:EssentialCycle B N D C) :
    (essentialFrontier B N D C c).PositiveHomotopyLength := c.property

lemma essentialFrontier_disjoint {c d:EssentialCycle B N D C} (hne:c≠d) :
    Disjoint (essentialFrontier B N D C c).trace (essentialFrontier B N D C d).trace :=
  frontierCycle_disjoint B N D C (fun h=>hne (Subtype.ext h))

lemma essential_cycleWidth_sum_le :
    ∑c:EssentialCycle B N D C,cycleWidth B N D c.val≤2*∑e,(N.finish e-N.start e) := by
  have h:=Fintype.sum_subtype_add_sum_subtype
    (fun c:D.rotation.BoundaryCycle N=>(frontierCycle B N D C c).PositiveHomotopyLength)
    (cycleWidth B N D)
  have hn:0≤∑c:{c:D.rotation.BoundaryCycle N // ¬(frontierCycle B N D C c).PositiveHomotopyLength},
      cycleWidth B N D c.val:=Finset.sum_nonneg (fun c hc=>cycleWidth_nonneg B N D c.val)
  have ht:(∑c:D.rotation.BoundaryCycle N,cycleWidth B N D c)=2*∑e,(N.finish e-N.start e):=
    D.rotation.sum_boundary_weights N (fun e=>N.finish e-N.start e)
  calc
    _ ≤ (∑c:EssentialCycle B N D C,cycleWidth B N D c.val)+
        ∑c:{c:D.rotation.BoundaryCycle N // ¬(frontierCycle B N D C c).PositiveHomotopyLength},
          cycleWidth B N D c.val := le_add_of_nonneg_right hn
    _ =∑c:D.rotation.BoundaryCycle N,cycleWidth B N D c := by
      exact h
    _ =_:=ht

variable (hcomplete:B.surface.domain=univ) (H:LoopStraighteningClassics B hcomplete)

def essentialGeodesics : Finset B.curves.Primitive :=
  straightenedBoundary B hcomplete H (essentialFrontier B N D C)
    (essentialFrontier_simple B N D C) (essentialFrontier_positive B N D C)

lemma essentialGeodesics_length_le :
    (∑γ∈essentialGeodesics B N D C hcomplete H,B.curves.length γ)≤2*∑e,(N.finish e-N.start e) := by
  apply (straightenedBoundary_length_le_comparison B hcomplete H
    (essentialFrontier B N D C) (essentialFrontier_simple B N D C)
    (essentialFrontier_positive B N D C)
    (fun c=>ClosedLoop.postcompose (cycleClosedLoop N D.rotation C c.val) (boundaryWalk N D.rotation))
    (fun c=>Or.inl (frontierCycle_homotopic_walk B N D C c.val))
    (fun c=>cycleWidth B N D c.val) (fun c=>cycleWidth_nonneg B N D c.val)
    (fun c=>cycle_boundary_walk_variation_le_ofReal N D.rotation C c.val)).trans
  exact essential_cycleWidth_sum_le B N D C

lemma essentialGeodesics_simple {δ:B.curves.Primitive}
    (hδ:δ∈essentialGeodesics B N D C hcomplete H) : SimpleTrace B δ :=
  straightenedBoundary_simple B hcomplete H (essentialFrontier B N D C)
    (essentialFrontier_simple B N D C) (essentialFrontier_positive B N D C) δ hδ

lemma essentialGeodesics_disjoint {γ δ:B.curves.Primitive}
    (hγ:γ∈essentialGeodesics B N D C hcomplete H)
    (hδ:δ∈essentialGeodesics B N D C hcomplete H) (hne:γ≠δ) :
    Disjoint (B.curves.trace γ) (B.curves.trace δ) :=
  straightenedBoundary_disjoint B hcomplete H (essentialFrontier B N D C)
    (essentialFrontier_simple B N D C) (essentialFrontier_positive B N D C)
    (fun _ _ hij=>essentialFrontier_disjoint B N D C hij) hγ hδ hne

lemma essentialGeodesics_card_le :
    (essentialGeodesics B N D C hcomplete H).card≤2*Nat.card N.Edge := by
  calc
    _ ≤Fintype.card (EssentialCycle B N D C) :=
      straightenedBoundary_card_le B hcomplete H (essentialFrontier B N D C)
        (essentialFrontier_simple B N D C) (essentialFrontier_positive B N D C)
    _ ≤Fintype.card (D.rotation.BoundaryCycle N) :=
      Fintype.card_subtype_le _
    _ ≤_:=by simpa only [Nat.card_eq_fintype_card] using D.rotation.boundaryCycle_card_le N

lemma essentialGeodesics_edge_or_disjoint {γ δ:B.curves.Primitive}
    (hγ:SimpleTrace B γ) (htrace:B.curves.trace γ⊆N.support)
    (hδ:δ∈essentialGeodesics B N D C hcomplete H) :
    γ=δ ∨ Disjoint (B.curves.trace γ) (B.curves.trace δ) := by
  obtain ⟨i,hi,he⟩:=Finset.mem_image.mp hδ
  have hδclass:(primitiveLoop B δ).UnorientedFreelyHomotopic (essentialFrontier B N D C i) := by
    simpa [he] using straightenedLoop_class B hcomplete H (essentialFrontier B N D C)
      (essentialFrontier_simple B N D C) (essentialFrontier_positive B N D C) i
  have hd:Disjoint (primitiveLoop B γ).trace (essentialFrontier B N D C i).trace := by
    rw [primitiveLoop_trace]
    exact (frontierCycle_disjoint_support B N D C i.val).symm.mono htrace (subset_refl _)
  exact H.disjoint_representatives γ δ (primitiveLoop B γ) (essentialFrontier B N D C i)
    (primitiveLoop_simple B γ hγ) (essentialFrontier_simple B N D C i)
    (ClosedLoop.unoriented_refl _) hδclass hd

end WP.Critical.ShortConfiguration
