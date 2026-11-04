import WPFormalization.Critical.PantsClusterDomain
import WPFormalization.Critical.PantsClusterCutSpectrum
import WPFormalization.External.ShortBorderedLoopGeometry

/-! Local actual-boundary consequences of generic old geodesic theory.
No classification of simple curves on pants or whole-filling result is
asserted by the classical interface or by this module. -/
noncomputable section
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false
universe u v w z
namespace WP.Critical.PantsCluster
open WP.External WP.External.PantsCluster WP.External.HyperbolicPacking
open WP.External.ShortFillingGeometry WP.External.ShortBorderedLoopGeometry Set
open WP.External.ShortLoopStraighteningGeometry

lemma bordered_primitive_positiveHomotopyLength (B : BorderedGeometry.{u,v})
    (R : BoundaryRealization B) (LS : BorderedLoopStraighteningClassics B R)
    (γ : B.curves.Primitive) : (primitiveLoop B γ).PositiveHomotopyLength :=
  ⟨B.curves.length γ,(B.curves.representative γ).period_pos,LS.length_minimal γ⟩

lemma canonical_boundary_index_eq (F : Family.{u,v}) (s : Waist)
    (j : Fin (F.model s).boundaries) : j = F.waist s := by
  apply Fin.ext
  have hj := j.isLt
  have hw := (F.waist s).isLt
  have hb := F.boundaries s
  omega

lemma canonical_nonwaist_trace_interior (F : Family.{u,v}) (s : Waist)
    (BC : PrimitiveBoundaryClassics (F.model s) (F.boundary s))
    (γ : F.Primitive) (hγ : γ ≠ F.waistClass) :
    (F.model s).curves.trace (F.marking s γ) ⊆ intrinsicInterior (F.model s) := by
  rcases BC.interior_or_boundary (F.marking s γ) with hi|⟨j,hj⟩
  · exact hi
  · rw [canonical_boundary_index_eq F s j,←F.marking_waist] at hj
    exact (hγ ((F.marking s).injective hj.symm)).elim

lemma canonical_waist_trace_boundary (F : Family.{u,v}) (s : Waist) :
    (F.model s).curves.trace (F.marking s F.waistClass) ⊆ intrinsicBoundary (F.model s) := by
  unfold Family.waistClass
  rw [F.marking_waist]
  intro p hp
  rw [←(F.boundary s).cover]
  exact Set.mem_iUnion.mpr ⟨F.waist s,hp⟩

lemma canonical_trace_interior_iff_nonwaist (F : Family.{u,v}) (s : Waist)
    (BC : PrimitiveBoundaryClassics (F.model s) (F.boundary s)) (γ : F.Primitive) :
    (F.model s).curves.trace (F.marking s γ) ⊆ intrinsicInterior (F.model s) ↔
      γ ≠ F.waistClass := by
  constructor
  · intro hi he
    subst γ
    obtain ⟨p,hp⟩ := primitive_trace_nonempty (F.model s) (F.marking s F.waistClass)
    exact Set.disjoint_left.mp (intrinsic_interior_disjoint_boundary (F.model s))
      (hi hp) (canonical_waist_trace_boundary F s hp)
  · exact canonical_nonwaist_trace_interior F s BC γ

variable {P : WP.PsiTheory} {G : WeilPeterssonGeometry.{u,v} P}
  {H : HyperbolicCurveGeometry.{u,v,w} G} (A : AmbientRealization H)
  {T : MulticurveTopology.{u,v,w,z} G H} {g n k : ℕ} {o : T.Orbit g n k}
  {X : G.Moduli g n (fun _ => 0)} {κ : Fin k → H.Primitive g n X}
  {hκ : T.orbitMem o X κ} (C : CutComponentRealization A T o X κ hκ)

lemma actual_cut_pants_cluster_measure
    (F : Family.{u,w}) (U : UniquenessClassics F) (c : Fin (T.cut o).components)
    (hpants : HasPantsTopology (C.piece c).model)
    (hb : (C.piece c).model.boundaries = 1)
    (BC : PrimitiveBoundaryClassics (C.piece c).model (C.piece c).boundary)
    (j : Fin (C.piece c).model.boundaries) :
    projectedPrimitiveMeasure (C.piece c) = measure F
      ⟨(C.piece c).model.curves.length ((C.piece c).boundary.curve j),
        ((C.piece c).model.curves.representative ((C.piece c).boundary.curve j)).period_pos⟩ :=
  actual_cut_pants_projected_measure_eq_cluster A C F U c hpants hb
    BC.trace_injective BC.interior_or_boundary j

end WP.Critical.PantsCluster
