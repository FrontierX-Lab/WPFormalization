import WPFormalization.Critical.PantsClusterCutEmbedding

/-! The actual ambient primitive subcatalog arising from an intrinsic cut
component. Full primitive transport is obtained after local projection
injectivity, rather than assumed for every intrinsic piece. -/
noncomputable section
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false
universe u v w z
namespace WP.Critical.PantsCluster
open WP.External WP.External.PantsCluster WP.External.HyperbolicPacking
open WP.External.ShortFillingGeometry MeasureTheory Set
open scoped NNReal ENNReal

def projectedPrimitiveMeasure {B : BorderedGeometry.{u,v}} (E : IntrinsicPiece B) :
    Measure ℝ≥0 :=
  Measure.sum (fun γ : Set.range E.primitiveProjection =>
    Measure.dirac (Real.toNNReal (B.curves.length γ.val)))

lemma projectedPrimitiveMeasure_eq_intrinsic {B : BorderedGeometry.{u,v}}
    (E : IntrinsicPiece B) (hinj : Function.Injective E.primitiveProjection) :
    projectedPrimitiveMeasure E = intrinsicMeasure E.model := by
  let e := Equiv.ofInjective E.primitiveProjection hinj
  let μ : Set.range E.primitiveProjection → Measure ℝ≥0 := fun γ =>
    Measure.dirac (Real.toNNReal (B.curves.length γ.val))
  have he : (fun γ : E.model.curves.Primitive =>
      Measure.dirac (Real.toNNReal (E.model.curves.length γ))) = μ ∘ e := by
    funext γ
    change Measure.dirac (Real.toNNReal (E.model.curves.length γ)) =
      Measure.dirac (Real.toNNReal (B.curves.length (E.primitiveProjection γ)))
    rw [E.length_preserved]
  change Measure.sum μ = Measure.sum (fun γ : E.model.curves.Primitive =>
    Measure.dirac (Real.toNNReal (E.model.curves.length γ)))
  rw [he]
  exact (Measure.sum_comp_equiv e μ).symm

variable {P : WP.PsiTheory} {G : WeilPeterssonGeometry.{u,v} P}
  {H : HyperbolicCurveGeometry.{u,v,w} G} (A : AmbientRealization H)
  {T : MulticurveTopology.{u,v,w,z} G H} {g n k : ℕ} {o : T.Orbit g n k}
  {X : G.Moduli g n (fun _ => 0)} {κ : Fin k → H.Primitive g n X}
  {hκ : T.orbitMem o X κ} (C : CutComponentRealization A T o X κ hκ)

lemma actual_cut_pants_projected_measure_eq_cluster
    (F : Family.{u,w}) (U : UniquenessClassics F) (c : Fin (T.cut o).components)
    (hpants : HasPantsTopology (C.piece c).model)
    (hb : (C.piece c).model.boundaries = 1)
    (htrace : Function.Injective (C.piece c).model.curves.trace)
    (hside : ∀ γ : (C.piece c).model.curves.Primitive,
      (C.piece c).model.curves.trace γ ⊆ intrinsicInterior (C.piece c).model ∨
        ∃ j, (C.piece c).boundary.curve j = γ)
    (j : Fin (C.piece c).model.boundaries) :
    projectedPrimitiveMeasure (C.piece c) = measure F
      ⟨(C.piece c).model.curves.length ((C.piece c).boundary.curve j),
        ((C.piece c).model.curves.representative ((C.piece c).boundary.curve j)).period_pos⟩ := by
  rw [projectedPrimitiveMeasure_eq_intrinsic _
    (cutComponent_single_boundary_projection_injective A C c hb htrace hside)]
  exact actual_pants_measure_eq_cluster F U (C.piece c).model hpants
    (C.piece c).boundary hb j

end WP.Critical.PantsCluster
