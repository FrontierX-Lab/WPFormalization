import WPFormalization.Critical.PantsClusterSupportBudget
import WPFormalization.Critical.PantsClusterCatalog

/-! Local boundary-sum consumers. The sourced actual single-curve piece
producer and its positive-boundary proof are assembled separately. -/
noncomputable section
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false
universe u v
open scoped NNReal ENNReal
namespace WP.Critical.PantsCluster
open WP.External.PantsCluster WP.External.HyperbolicPacking
open WP.External.ShortFillingGeometry WP.External.ShortBorderedLoopGeometry
open WP.External.ShortLoopStraighteningGeometry WP.External.ShortComplementaryRegionGeometry
open WP.External.PlanarJordanGeometry WP.External.PlanarRegionGeometry
open WP.External.ShortBorderedPeripheralGeometry
open Set MeasureTheory

lemma actual_pants_waist_budget_of_boundary_sum (B : BorderedGeometry.{u,v})
    (hp : HasPantsTopology B) (R : BoundaryRealization B) (hb : B.boundaries = 1)
    (BC : PrimitiveBoundaryClassics B R) (LS : BorderedLoopStraighteningClassics B R)
    (J : PlanarJordanClassics) (PC : PlanarRegionClassics)
    (PP : BorderedPeripheralClassics B R) (γ : B.curves.Primitive)
    (E : IntrinsicPiece B) (hd : 0 < E.model.boundaries)
    (hbudget : boundaryLength E.boundary ≤ 2 * B.curves.length γ)
    (j : Fin B.boundaries) : B.curves.length (R.curve j) ≤ 2 * B.curves.length γ := by
  let i : Fin E.model.boundaries := ⟨0,hd⟩
  have heq := actual_pants_piece_boundary_projection B hp R hb BC LS J PC PP E i j
  calc
    B.curves.length (R.curve j) = E.model.curves.length (E.boundary.curve i) := by
      rw [←E.length_preserved,heq]
    _ ≤ boundaryLength E.boundary := by
      unfold boundaryLength
      exact Finset.single_le_sum (s := Finset.univ)
        (f := fun b => E.model.curves.length (E.boundary.curve b))
        (fun b _ => (E.model.curves.representative (E.boundary.curve b)).period_pos.le)
        (Finset.mem_univ i)
    _ ≤ 2 * B.curves.length γ := hbudget

lemma canonical_waist_budget_of_boundary_sum (F : Family.{u,v}) (s : Waist)
    (BC : PrimitiveBoundaryClassics (F.model s) (F.boundary s))
    (LS : BorderedLoopStraighteningClassics (F.model s) (F.boundary s))
    (J : PlanarJordanClassics) (PC : PlanarRegionClassics)
    (PP : BorderedPeripheralClassics (F.model s) (F.boundary s))
    (γ : F.Primitive) (E : IntrinsicPiece (F.model s))
    (hd : 0 < E.model.boundaries)
    (hbudget : boundaryLength E.boundary ≤ 2 * F.length s γ) :
    s.val ≤ 2 * F.length s γ := by
  have h := actual_pants_waist_budget_of_boundary_sum (F.model s)
    ⟨F.topology s,F.topological_boundary s⟩ (F.boundary s) (F.boundaries s)
    BC LS J PC PP (F.marking s γ) E hd hbudget (F.waist s)
  rwa [F.waist_length] at h

/-- This elementary last step is independent of how the actual geometric
waist budget is produced; the final geometry wrapper supplies that theorem. -/
lemma measure_prefix_eq_zero_of_length_budget (F : Family.{u,v})
    (hbudget : ∀ (s : Waist) (γ : F.Primitive), s.val ≤ 2 * F.length s γ)
    (L : ℝ≥0) (s : Waist) (hs : 2 * (L : ℝ) < s.val) :
    measure F s (Iic L) = 0 := by
  rw [measure_prefix_eq_zero_iff]
  intro γ
  have h := hbudget s γ
  linarith

end WP.Critical.PantsCluster
