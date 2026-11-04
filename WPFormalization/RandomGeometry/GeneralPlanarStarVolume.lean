import WPFormalization.RandomGeometry.GeneralPlanarStarCutSides
import WPFormalization.RandomGeometry.PantsMomentAsymptoticsStarVolume

/-! Exact physical cut volumes of actual general planar stars. -/
noncomputable section
universe u v
namespace WP.RandomGeometry
open WP.External

/-- All unused cusp boundaries are zero; the root retains each physical edge. -/
def generalPlanarStarRootLengths (n r : ℕ) (k : Fin r → ℕ) (x : Fin r → ℝ) :
    Fin (n-(∑i,k i)+r) → ℝ := Fin.append (fun _ => 0) x

def generalPlanarStarLeafLengths (k : ℕ) (x : ℝ) : Fin (k+1) → ℝ :=
  Fin.append (fun _ => 0) (fun _ : Fin 1 => x)

def generalPlanarStarRootLengthIndexEquiv (g n r : ℕ) (k : Fin r → ℕ)
    (f : PlanarLabelBlocks n r k) :
    Fin (n-(∑i,k i)+r) ≃ Fin ((generalPlanarStarCut g n r k f).boundaryCount (0 : Fin (r+1))) := by
  letI : Fintype ((generalPlanarStarCut g n r k f).Boundary (0 : Fin (r+1))) :=
    MulticurveCutData.instFintypeBoundary (generalPlanarStarCut g n r k f) (0 : Fin (r+1))
  exact finSumFinEquiv.symm |>.trans (generalPlanarStarRootBoundaryEquiv g n r k f)
    |>.trans (Fintype.equivFin _)

def generalPlanarStarLeafLengthIndexEquiv (g n r : ℕ) (k : Fin r → ℕ)
    (f : PlanarLabelBlocks n r k) (e : Fin r) :
    Fin (k e+1) ≃ Fin ((generalPlanarStarCut g n r k f).boundaryCount e.succ) := by
  letI : Fintype ((generalPlanarStarCut g n r k f).Boundary e.succ) :=
    MulticurveCutData.instFintypeBoundary (generalPlanarStarCut g n r k f) e.succ
  exact finSumFinEquiv.symm |>.trans (Equiv.sumCongr (Equiv.refl _) finOneEquiv)
    |>.trans (generalPlanarStarLeafBoundaryEquiv g n r k f e)
    |>.trans (Fintype.equivFin _)

set_option backward.isDefEq.respectTransparency false in
lemma generalPlanarStar_root_lengths (g n r : ℕ) (k : Fin r → ℕ)
    (f : PlanarLabelBlocks n r k) (x : Fin r → ℝ) :
    (generalPlanarStarCut g n r k f).boundaryLengths x (0 : Fin (r+1)) ∘
      generalPlanarStarRootLengthIndexEquiv g n r k f =
      generalPlanarStarRootLengths n r k x := by
  classical
  let D := generalPlanarStarCut g n r k f
  let c : Fin D.components := ⟨0,by change 0<r+1; omega⟩
  letI : Fintype (D.Boundary c) := MulticurveCutData.instFintypeBoundary D c
  funext i
  let eB : D.Boundary c ≃ Fin (D.boundaryCount c) := Fintype.equivFin _
  let e := finSumFinEquiv.symm |>.trans (generalPlanarStarRootBoundaryEquiv g n r k f)
  have he := eB.symm_apply_apply (e i)
  have hm := congrArg (Sum.elim (fun _ => (0:ℝ)) (fun e => x e.val.1) : D.Boundary c → ℝ) he
  have ht := pants_boundaryLengths_eq_sumElim D x c
    ((generalPlanarStarRootLengthIndexEquiv g n r k f).toFun i)
  refine ht.trans (hm.trans ?_)
  refine Fin.addCases ?_ ?_ i
  · intro j
    simp [e,Equiv.sumCongr_apply,generalPlanarStarRootBoundaryEquiv,generalPlanarStarRootLengths] <;> rfl
  · intro j
    simp [e,Equiv.sumCongr_apply,generalPlanarStarRootBoundaryEquiv,generalPlanarStarRootLengths,
      generalPlanarStarRootEdgeEquiv] <;> rfl

set_option backward.isDefEq.respectTransparency false in
lemma generalPlanarStar_leaf_lengths (g n r : ℕ) (k : Fin r → ℕ)
    (f : PlanarLabelBlocks n r k) (x : Fin r → ℝ) (e : Fin r) :
    (generalPlanarStarCut g n r k f).boundaryLengths x e.succ ∘
      generalPlanarStarLeafLengthIndexEquiv g n r k f e =
      generalPlanarStarLeafLengths (k e) (x e) := by
  classical
  let D := generalPlanarStarCut g n r k f
  let c : Fin D.components := e.succ
  letI : Fintype (D.Boundary c) := MulticurveCutData.instFintypeBoundary D c
  funext i
  let eB : D.Boundary c ≃ Fin (D.boundaryCount c) := Fintype.equivFin _
  let ee := finSumFinEquiv.symm |>.trans (Equiv.sumCongr (Equiv.refl _) finOneEquiv)
    |>.trans (generalPlanarStarLeafBoundaryEquiv g n r k f e)
  have he := eB.symm_apply_apply (ee i)
  have hm := congrArg (Sum.elim (fun _ => (0:ℝ)) (fun e => x e.val.1) : D.Boundary c → ℝ) he
  have ht := pants_boundaryLengths_eq_sumElim D x c
    ((generalPlanarStarLeafLengthIndexEquiv g n r k f e).toFun i)
  refine ht.trans (hm.trans ?_)
  refine Fin.addCases ?_ ?_ i
  · intro j
    simp [ee,Equiv.sumCongr_apply,generalPlanarStarLeafBoundaryEquiv,generalPlanarStarLeafLengths] <;> rfl
  · intro j
    simp [ee,Equiv.sumCongr_apply,generalPlanarStarLeafBoundaryEquiv,generalPlanarStarLeafLengths,
      generalPlanarStarLeafEdgeEquiv] <;> rfl

lemma generalPlanarStar_boundary_lengths_nonneg (g n r : ℕ) (k : Fin r → ℕ)
    (f : PlanarLabelBlocks n r k) (x : Fin r → ℝ) (hx : ∀i,0≤x i) (c : Fin (r+1)) :
    ∀j,0≤(generalPlanarStarCut g n r k f).boundaryLengths x c j := by
  intro j
  unfold MulticurveCutData.boundaryLengths
  split
  · exact le_rfl
  · exact hx _

lemma generalPlanarStar_root_volume (P : PsiTheory) (G : WeilPeterssonGeometry.{u,v} P)
    (g n r : ℕ) (k : Fin r → ℕ) (f : PlanarLabelBlocks n r k) (hg : 2≤g)
    (x : Fin r → ℝ) (hx : ∀i,0≤x i) :
    wpVolume G ((generalPlanarStarCut g n r k f).genus (0 : Fin (r+1)))
      ((generalPlanarStarCut g n r k f).boundaryCount (0 : Fin (r+1)))
      ((generalPlanarStarCut g n r k f).boundaryLengths x (0 : Fin (r+1))) =
      boundaryVolumeModel P g (n-(∑i,k i)+r) (generalPlanarStarRootLengths n r k x) := by
  have hs : Stable g ((generalPlanarStarCut g n r k f).boundaryCount (0 : Fin (r+1))) := by
    unfold Stable
    omega
  change wpVolume G g _ _ = _
  rw [WP.Geometry.wpVolume_eq_boundaryVolumeModel P G g _ _ hs
    (generalPlanarStar_boundary_lengths_nonneg g n r k f x hx (0 : Fin (r+1)))]
  have he := boundaryVolumeModel_reindex P g (n-(∑i,k i)+r) _
    ((generalPlanarStarCut g n r k f).boundaryLengths x (0 : Fin (r+1)))
    (generalPlanarStarRootLengthIndexEquiv g n r k f)
  rw [generalPlanarStar_root_lengths g n r k f x] at he
  exact he.symm

lemma generalPlanarStar_leaf_volume (P : PsiTheory) (G : WeilPeterssonGeometry.{u,v} P)
    (g n r : ℕ) (k : Fin r → ℕ) (f : PlanarLabelBlocks n r k) (hk : ∀i,2≤k i)
    (x : Fin r → ℝ) (hx : ∀i,0≤x i) (e : Fin r) :
    wpVolume G ((generalPlanarStarCut g n r k f).genus e.succ)
      ((generalPlanarStarCut g n r k f).boundaryCount e.succ)
      ((generalPlanarStarCut g n r k f).boundaryLengths x e.succ) =
      boundaryVolumeModel P 0 (k e+1) (generalPlanarStarLeafLengths (k e) (x e)) := by
  have hcount := generalPlanarStarCut_leaf_boundaryCount g n r k f e
  have hs : Stable 0 ((generalPlanarStarCut g n r k f).boundaryCount e.succ) := by
    rw [hcount]
    unfold Stable
    have := hk e
    omega
  have hg : (generalPlanarStarCut g n r k f).genus e.succ=0 := by
    simp only [generalPlanarStarCut,Fin.succ_ne_zero,ite_false]
  rw [hg,WP.Geometry.wpVolume_eq_boundaryVolumeModel P G 0 _ _ hs
    (generalPlanarStar_boundary_lengths_nonneg g n r k f x hx e.succ)]
  have he := boundaryVolumeModel_reindex P 0 (k e+1) _
    ((generalPlanarStarCut g n r k f).boundaryLengths x e.succ)
    (generalPlanarStarLeafLengthIndexEquiv g n r k f e)
  rw [generalPlanarStar_leaf_lengths g n r k f x e] at he
  exact he.symm

lemma generalPlanarStar_volumeProduct (P : PsiTheory) (G : WeilPeterssonGeometry.{u,v} P)
    (g n r : ℕ) (k : Fin r → ℕ) (f : PlanarLabelBlocks n r k) (hg : 2≤g)
    (hk : ∀i,2≤k i) (x : Fin r → ℝ) (hx : ∀i,0≤x i) :
    (generalPlanarStarCut g n r k f).volumeProduct G x =
      boundaryVolumeModel P g (n-(∑i,k i)+r) (generalPlanarStarRootLengths n r k x) *
        ∏i,boundaryVolumeModel P 0 (k i+1) (generalPlanarStarLeafLengths (k i) (x i)) := by
  change (∏c : Fin (r+1),wpVolume G _ _ _) = _
  rw [Fin.prod_univ_succ,generalPlanarStar_root_volume P G g n r k f hg x hx]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  exact generalPlanarStar_leaf_volume P G g n r k f hk x hx i
end WP.RandomGeometry
