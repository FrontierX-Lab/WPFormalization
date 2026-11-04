import WPFormalization.Critical.PhysicalPrimitivePointMeasure
import WPFormalization.Critical.PantsClusterBoundary

/- Transport the same actual H primitive catalog to a cut component's ambient
projection range. No spectral equality is supplied as a new geometric field. -/
noncomputable section
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false
universe u v w z
namespace WP.Critical.PantsCluster
open WP.External WP.RandomGeometry WP.External.PantsCluster
open WP.External.HyperbolicPacking WP.External.ShortFillingGeometry
open WP.External.ShortBorderedLoopGeometry
open MeasureTheory Set
open scoped ENNReal NNReal
variable {P : PsiTheory} {G : WeilPeterssonGeometry.{u,v} P}
  {H : HyperbolicCurveGeometry.{u,v,w} G} (A : AmbientRealization H)
  {g n : ℕ} (X : G.Moduli g n (fun _ => 0))

def actualPiecePrimitivePredicate (E : IntrinsicPiece (A.model g n X))
    (γ : H.Primitive g n X) : Prop :=
  A.primitiveEquiv g n X γ ∈ Set.range E.primitiveProjection

def actualPiecePrimitiveEquiv (E : IntrinsicPiece (A.model g n X)) :
    {γ : H.Primitive g n X // actualPiecePrimitivePredicate A X E γ} ≃
      Set.range E.primitiveProjection :=
  (A.primitiveEquiv g n X).subtypeEquiv (fun _ => Iff.rfl)

lemma actualPiecePrimitiveMeasure_eq_projected
    (E : IntrinsicPiece (A.model g n X)) :
    curveNNLengthMeasure H X 1 (actualPiecePrimitivePredicate A X E) =
      projectedPrimitiveMeasure E := by
  let μ : Set.range E.primitiveProjection → Measure ℝ≥0 := fun γ =>
    Measure.dirac (Real.toNNReal ((A.model g n X).curves.length γ.val))
  have he : (fun γ : {γ : H.Primitive g n X // actualPiecePrimitivePredicate A X E γ} =>
      Measure.dirac (Real.toNNReal (1*H.length γ.val))) =
      μ ∘ actualPiecePrimitiveEquiv A X E := by
    funext γ
    change Measure.dirac (Real.toNNReal (1*H.length γ.val)) =
      Measure.dirac (Real.toNNReal ((A.model g n X).curves.length
        (A.primitiveEquiv g n X γ.val)))
    rw [A.length_eq, one_mul]
  change Measure.sum _ = Measure.sum μ
  rw [he]
  exact Measure.sum_comp_equiv (actualPiecePrimitiveEquiv A X E) μ

variable {T : MulticurveTopology.{u,v,w,z} G H} {k : ℕ} {o : T.Orbit g n k}
  {κ : Fin k → H.Primitive g n X} {hκ : T.orbitMem o X κ}
  (C : CutComponentRealization A T o X κ hκ)

lemma actual_cut_pants_H_measure_eq_cluster
    (F : Family.{u,w}) (U : UniquenessClassics F) (c : Fin (T.cut o).components)
    (hpants : HasPantsTopology (C.piece c).model)
    (hb : (C.piece c).model.boundaries=1)
    (BC : PrimitiveBoundaryClassics (C.piece c).model (C.piece c).boundary)
    (j : Fin (C.piece c).model.boundaries) :
    curveNNLengthMeasure H X 1 (actualPiecePrimitivePredicate A X (C.piece c)) =
      measure F ⟨(C.piece c).model.curves.length ((C.piece c).boundary.curve j),
        ((C.piece c).model.curves.representative ((C.piece c).boundary.curve j)).period_pos⟩ := by
  rw [actualPiecePrimitiveMeasure_eq_projected]
  exact actual_cut_pants_cluster_measure A C F U c hpants hb BC j

end WP.Critical.PantsCluster
