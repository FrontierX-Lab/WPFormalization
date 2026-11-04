import WPFormalization.Critical.CutSkeletonDegree

/-! Vertex transports of the actual cut degrees and original cusp labels.
These identities preserve both incidences of a loop and allow every edge
orientation flip of a cut isomorphism. -/

noncomputable section
namespace WP.External.MulticurveCutData.Isomorphism
open WP.Critical
variable {n k : ℕ} {D E : MulticurveCutData n k}

theorem cuspCount_eq (f : D.Isomorphism E) (c : Fin D.components) :
    CutGraphData.cuspCount D c = CutGraphData.cuspCount E (f.vertexEquiv c) := by
  apply Fintype.card_congr
  exact (Equiv.refl (Fin n)).subtypeEquiv (by
    intro i
    change D.cuspVertex i = c ↔ E.cuspVertex i = f.vertexEquiv c
    rw [← f.cusp_eq i]
    exact f.vertexEquiv.injective.eq_iff.symm)

theorem degree_eq (f : D.Isomorphism E) (c : Fin D.components) :
    CutGraphData.degree D c = CutGraphData.degree E (f.vertexEquiv c) := by
  apply Fintype.card_congr
  exact f.halfEdgeEquiv.subtypeEquiv (by
    intro e
    rw [f.halfEdgeEquiv_incidence]
    exact f.vertexEquiv.injective.eq_iff.symm)

end WP.External.MulticurveCutData.Isomorphism

namespace WP.Critical.CutSkeleton
open WP.External
variable {k Q n : ℕ} {S : CutSkeleton k Q} {D : MulticurveCutData n k}

theorem Realization.degree_eq (R : S.Realization D) (c : Fin D.components) :
    CutGraphData.degree D c = S.degree (R.vertices c) := by
  exact R.isomorphism.degree_eq c

theorem Realization.cuspCount_eq (R : S.Realization D) (c : Fin D.components) :
    CutGraphData.cuspCount D c = cutCuspHistogram R.cusps (R.vertices c) := by
  rw [R.isomorphism.cuspCount_eq c, cutCuspHistogram_eq_card]
  rfl

theorem Realization.boundaryCount_cuspHistogram
    (R : S.Realization D) (c : Fin D.components) :
    D.boundaryCount c = cutCuspHistogram R.cusps (R.vertices c) + S.degree (R.vertices c) := by
  rw [CutGraphData.boundaryCount_eq, R.cuspCount_eq, R.degree_eq]

end WP.Critical.CutSkeleton
