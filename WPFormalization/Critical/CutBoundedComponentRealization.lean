import WPFormalization.Critical.CutBoundedComponentClassification
import WPFormalization.External.ShortFillingGeometry
/-! Intrinsic cut-component topology agrees with the actual cut graph.
Bounded negative Euler characteristic therefore excludes the unique large
stable vertex by the local classification theorem. -/
noncomputable section
universe u v w z
namespace WP.Critical.ShortConfiguration
open WP.External WP.External.ShortFillingGeometry WP.External.HyperbolicPacking
open scoped Classical
variable {P : PsiTheory} {G : WeilPeterssonGeometry.{u,v} P}
  {H : HyperbolicCurveGeometry.{u,v,w} G} {A : AmbientRealization H}
  {T : MulticurveTopology.{u,v,w,z} G H} {g n k : ℕ}
  {o : T.Orbit g n k} {X : G.Moduli g n (fun _ => 0)}
  {κ : Fin k → H.Primitive g n X} {hκ : T.orbitMem o X κ}
  (R : CutComponentRealization A T o X κ hκ)

lemma cutComponent_cusps_eq_cuspCount (c : Fin (T.cut o).components) :
    (R.piece c).model.cusps = CutGraphData.cuspCount (T.cut o) c := by
  have he := Fintype.card_congr (R.cuspEquiv c)
  simpa only [Fintype.card_fin, CutGraphData.cuspCount] using he

lemma cutComponent_boundaries_eq_degree (c : Fin (T.cut o).components) :
    (R.piece c).model.boundaries = CutGraphData.degree (T.cut o) c := by
  have he := Fintype.card_congr (R.halfSideEquiv c)
  simpa only [Fintype.card_fin, CutGraphData.degree] using he

lemma cutComponent_negativeEuler_eq_complexity (c : Fin (T.cut o).components) :
    (R.piece c).model.negativeEuler =
      complexity ((T.cut o).genus c) ((T.cut o).boundaryCount c) := by
  have he := (R.piece c).model.euler_eq
  rw [R.genus_eq c, cutComponent_cusps_eq_cuspCount R c,
    cutComponent_boundaries_eq_degree R c] at he
  rw [CutGraphData.boundaryCount_eq]
  unfold complexity
  omega

lemma bounded_realization_component_canonical_bad_or_marked
    (K : ℝ) (hg : k + Nat.ceil K + 3 ≤ g) (c : Fin (T.cut o).components)
    (hK : ((R.piece c).model.negativeEuler : ℝ) ≤ K)
    (hnotPants : ¬((R.piece c).model.genus = 0 ∧ (R.piece c).model.cusps = 2 ∧
      (R.piece c).model.boundaries = 1)) :
    (CutGraphData.baseStableCount (T.cut o) ≠ 1 ∨ CutGraphData.twoCount (T.cut o) ≠ 0) ∨
      CutDataHasMarkedPartition (T.cut o) (CutGraphData.oneCount (T.cut o))
        (CutGraphData.twoCount (T.cut o)) (CutGraphData.baseStableCount (T.cut o)) := by
  apply actual_bounded_component_canonical_bad_or_marked T o K hg c
  · simpa only [cutComponent_negativeEuler_eq_complexity R c] using hK
  · intro h
    apply hnotPants
    rwa [R.genus_eq c, cutComponent_cusps_eq_cuspCount R c,
      cutComponent_boundaries_eq_degree R c]
end WP.Critical.ShortConfiguration
