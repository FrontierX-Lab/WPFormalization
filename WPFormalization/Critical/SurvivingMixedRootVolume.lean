import WPFormalization.Critical.SurvivingMixedRootBoundary
import WPFormalization.Critical.SurvivingMixedVolumeBoundary
import WPFormalization.RandomGeometry.CutVolumeTransport
noncomputable section
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false
universe aa bb
namespace WP.Critical
open WP.External WP.RandomGeometry

lemma survivingMixed_root_volume (P : PsiTheory) (G : WeilPeterssonGeometry.{aa,bb} P)
    (g n r k : ℕ) (f : PantsLabels n r) (hg : k+2 ≤ g) (hn : 2*r ≤ n)
    (x : Fin (r+k) → ℝ) (hx : ∀ i, 0 ≤ x i) :
    wpVolume G ((survivingMixedCutGraph g n r k f).genus (0 : Fin (r+1)))
      ((survivingMixedCutGraph g n r k f).boundaryCount (0 : Fin (r+1)))
      ((survivingMixedCutGraph g n r k f).boundaryLengths x (0 : Fin (r+1))) =
        boundaryVolumeModel P (g-k) (n-r+2*k) (survivingBoundaryLengths r k n x) := by
  have hs : Stable (g-k) ((survivingMixedCutGraph g n r k f).boundaryCount (0 : Fin (r+1))) := by
    unfold Stable
    omega
  change wpVolume G (g-k) _ _ = _
  rw [WP.Geometry.wpVolume_eq_boundaryVolumeModel P G _ _ _ hs
    ((survivingMixedCutGraph g n r k f).boundaryLengths_nonneg x hx _)]
  have he := boundaryVolumeModel_reindex P (g-k) (n-r+2*k) _
    ((survivingMixedCutGraph g n r k f).boundaryLengths x (0 : Fin (r+1)))
    (survivingMixedRootLengthIndexEquiv g n r k f hn)
  rw [survivingMixed_root_lengths] at he
  exact he.symm

lemma survivingMixed_leaf_volume (P : PsiTheory) (G : WeilPeterssonGeometry.{aa,bb} P)
    (g n r k : ℕ) (f : PantsLabels n r) (x : Fin (r+k) → ℝ) (hx : ∀ i, 0 ≤ x i) (e : Fin r) :
    wpVolume G ((survivingMixedCutGraph g n r k f).genus e.succ)
      ((survivingMixedCutGraph g n r k f).boundaryCount e.succ)
      ((survivingMixedCutGraph g n r k f).boundaryLengths x e.succ)=1 := by
  have hcount := survivingMixed_leaf_boundaryCount g n r k f e
  have hs : Stable 0 ((survivingMixedCutGraph g n r k f).boundaryCount e.succ) := by
    rw [hcount]
    norm_num [Stable]
  have hgenus : (survivingMixedCutGraph g n r k f).genus e.succ=0 := by
    simp [survivingMixedCutGraph,Fin.succ_ne_zero]
  rw [hgenus,WP.Geometry.wpVolume_eq_boundaryVolumeModel P G 0 _ _ hs
    ((survivingMixedCutGraph g n r k f).boundaryLengths_nonneg x hx _)]
  have hthree : ∀ m : ℕ, m=3 → ∀ L : Fin m → ℝ, boundaryVolumeModel P 0 m L=1 := by
    intro m hm L
    subst m
    exact pants_boundary_volume_genus_zero_three P L
  exact hthree _ hcount _

lemma survivingMixed_volumeProduct (P : PsiTheory) (G : WeilPeterssonGeometry.{aa,bb} P)
    (g n r k : ℕ) (f : PantsLabels n r) (hg : k+2 ≤ g) (hn : 2*r ≤ n)
    (x : Fin (r+k) → ℝ) (hx : ∀ i, 0 ≤ x i) :
    (survivingMixedCutGraph g n r k f).volumeProduct G x=
      boundaryVolumeModel P (g-k) (n-r+2*k) (survivingBoundaryLengths r k n x) := by
  change (∏ c : Fin (r+1), wpVolume G _ _ _) = _
  rw [Fin.prod_univ_succ,survivingMixed_root_volume P G g n r k f hg hn x hx]
  have hl : (∏ i : Fin r, wpVolume G ((survivingMixedCutGraph g n r k f).genus i.succ)
      ((survivingMixedCutGraph g n r k f).boundaryCount i.succ)
      ((survivingMixedCutGraph g n r k f).boundaryLengths x i.succ))=1 := by
    apply Finset.prod_eq_one
    intro i hi
    exact survivingMixed_leaf_volume P G g n r k f x hx i
  rw [hl,mul_one]
end WP.Critical
