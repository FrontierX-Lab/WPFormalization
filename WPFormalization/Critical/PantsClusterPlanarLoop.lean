import WPFormalization.Critical.PantsClusterBoundary
import WPFormalization.Critical.PantsClusterDiskTransport
import WPFormalization.Critical.ShortConfigurationRecordingLoopLength
import WPFormalization.Critical.ShortConfigurationRecordingDiskAvoidance

/-! The actual canonical primitive loop in the actual twice-punctured-disk
chart, before any planar region classification. -/
noncomputable section
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false
universe u v
namespace WP.Critical.PantsCluster
open WP.External.PantsCluster WP.External.HyperbolicPacking
open WP.External.ShortFillingGeometry WP.External.ShortBorderedLoopGeometry
open WP.External.ShortLoopStraighteningGeometry WP.External.ShortComplementaryRegionGeometry
open WP.External.PlanarJordanGeometry Set

def pantsPlanarChart (F : Family.{u,v}) (s : Waist) : C((F.model s).surface.Point,ℂ) :=
  ⟨fun p => ((F.topology s) p).val,
    continuous_subtype_val.comp (F.topology s).continuous⟩

lemma pantsPlanarChart_injective (F : Family.{u,v}) (s : Waist) :
    Function.Injective (pantsPlanarChart F s) :=
  Subtype.val_injective.comp (F.topology s).injective

def planarPrimitiveLoop (F : Family.{u,v}) (s : Waist) (γ : F.Primitive) : ClosedLoop ℂ :=
  mapClosedLoop (pantsPlanarChart F s) (primitiveLoop (F.model s) (F.marking s γ))

lemma planarPrimitiveLoop_trace (F : Family.{u,v}) (s : Waist) (γ : F.Primitive) :
    (planarPrimitiveLoop F s γ).trace =
      pantsPlanarChart F s '' (F.model s).curves.trace (F.marking s γ) := by
  rw [planarPrimitiveLoop,mapClosedLoop_trace,
    WP.Critical.ShortConfiguration.primitiveLoop_trace]

lemma planarPrimitiveLoop_simple (F : Family.{u,v}) (s : Waist) (γ : F.Primitive)
    (hγ : SimpleTrace (F.model s) (F.marking s γ)) :
    (planarPrimitiveLoop F s γ).Simple :=
  mapClosedLoop_simple (pantsPlanarChart F s) (pantsPlanarChart_injective F s) _
    (WP.Critical.ShortConfiguration.primitiveLoop_simple _ _ hγ)

lemma planarPrimitiveLoop_avoids_punctures (F : Family.{u,v}) (s : Waist)
    (γ : F.Primitive) :
    ∀ z ∈ (planarPrimitiveLoop F s γ).trace, z ≠ (1/2:ℂ) ∧ z ≠ -(1/2:ℂ) := by
  rw [planarPrimitiveLoop_trace]
  rintro _ ⟨p,hp,rfl⟩
  exact ((F.topology s p).property).2

lemma planarPrimitiveLoop_nonwaist_inside_unitDisk (F : Family.{u,v}) (s : Waist)
    (BC : PrimitiveBoundaryClassics (F.model s) (F.boundary s))
    (γ : F.Primitive) (hγ : γ ≠ F.waistClass) :
    ∀ z ∈ (planarPrimitiveLoop F s γ).trace, ‖z‖ < 1 := by
  rw [planarPrimitiveLoop_trace]
  rintro _ ⟨p,hp,rfl⟩
  exact (canonical_pants_interior_iff F s p).mp
    (canonical_nonwaist_trace_interior F s BC γ hγ hp)

lemma planarPrimitiveLoop_has_boundedDisk (F : Family.{u,v}) (s : Waist)
    (J : PlanarJordanClassics) (γ : F.Primitive)
    (hγ : SimpleTrace (F.model s) (F.marking s γ)) :
    Nonempty (DiskBoundedBy (planarPrimitiveLoop F s γ)) :=
  simple_plane_loop_boundedDisk J _ (planarPrimitiveLoop_simple F s γ hγ)

lemma planarPrimitiveLoop_boundedDisk_inside_unitDisk (F : Family.{u,v}) (s : Waist)
    (BC : PrimitiveBoundaryClassics (F.model s) (F.boundary s))
    (γ : F.Primitive) (hγ : γ ≠ F.waistClass)
    (D : DiskBoundedBy (planarPrimitiveLoop F s γ)) :
    ∀ z ∈ Set.range D.map, ‖z‖ < 1 :=
  boundedDisk_subset_open_unitDisk D
    (planarPrimitiveLoop_nonwaist_inside_unitDisk F s BC γ hγ)

end WP.Critical.PantsCluster
