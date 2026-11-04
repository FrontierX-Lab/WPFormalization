import WPFormalization.External.MulticurveCutIsomorphism
import WPFormalization.External.MirzakhaniIntegration
import WPFormalization.Geometry.Bridge
import WPFormalization.Marked.ExternalBoundaryPermutation

/-! Actual geometric volume transport under labelled cut isomorphisms.
The stable, nonnegative domain is precisely the domain of the classical
Weil--Petersson volume polynomial; no symmetry is postulated for an arbitrary
measure outside that domain. -/
noncomputable section
universe u v
namespace WP.External.MulticurveCutData
variable {n r : ℕ} {D E : MulticurveCutData n r}

lemma boundaryLengths_nonneg (D : MulticurveCutData n r) (x : Fin r → ℝ)
    (hx : ∀ e, 0 ≤ x e) (c : Fin D.components) :
    ∀ i, 0 ≤ D.boundaryLengths x c i := by
  intro i
  unfold boundaryLengths
  split
  · exact le_refl 0
  · exact hx _

namespace Isomorphism

lemma stable (f : D.Isomorphism E)
    (hD : ∀ c, Stable (D.genus c) (D.boundaryCount c)) :
    ∀ c, Stable (E.genus c) (E.boundaryCount c) := by
  intro c
  have h := hD (f.vertexEquiv.symm c)
  rw [← f.genus_eq, f.boundaryCount_eq, f.vertexEquiv.apply_symm_apply] at h
  exact h

/-- Each actual factor is transported using the proved finite boundary
polynomial reindexing, not a new geometric symmetry field. -/
theorem wpVolume_eq {P : PsiTheory} (G : WeilPeterssonGeometry.{u,v} P)
    (f : D.Isomorphism E) (x : Fin r → ℝ) (hx : ∀ e, 0 ≤ x e)
    (hD : ∀ c, Stable (D.genus c) (D.boundaryCount c))
    (c : Fin D.components) :
    wpVolume G (D.genus c) (D.boundaryCount c) (D.boundaryLengths x c) =
      wpVolume G (E.genus (f.vertexEquiv c)) (E.boundaryCount (f.vertexEquiv c))
        (E.boundaryLengths x (f.vertexEquiv c)) := by
  rw [WP.Geometry.wpVolume_eq_boundaryVolumeModel P G _ _ _ (hD c)
      (D.boundaryLengths_nonneg x hx c),
    WP.Geometry.wpVolume_eq_boundaryVolumeModel P G _ _ _ (f.stable hD _)
      (E.boundaryLengths_nonneg x hx _), f.genus_eq]
  rw [← f.boundaryLengths_reindex x c]
  exact boundaryVolumeModel_reindex P (D.genus c) _ _ _ (f.boundaryIndexEquiv c)

/-- The product of actual cut-component volumes is invariant on the
nonnegative integration orthant. -/
theorem volumeProduct_eq {P : PsiTheory} (G : WeilPeterssonGeometry.{u,v} P)
    (f : D.Isomorphism E) (x : Fin r → ℝ) (hx : ∀ e, 0 ≤ x e)
    (hD : ∀ c, Stable (D.genus c) (D.boundaryCount c)) :
    D.volumeProduct G x = E.volumeProduct G x := by
  unfold volumeProduct
  exact Fintype.prod_equiv f.vertexEquiv _ _ (f.wpVolume_eq G x hx hD)

end Isomorphism
end WP.External.MulticurveCutData
