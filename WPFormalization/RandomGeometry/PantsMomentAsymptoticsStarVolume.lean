import WPFormalization.RandomGeometry.PantsMomentAsymptoticsStarBoundary
import WPFormalization.RandomGeometry.PantsMomentAsymptoticsIntegrals
import WPFormalization.Geometry.Bridge
import WPFormalization.Marked.ExternalBoundaryPermutation
import WPFormalization.External.MirzakhaniIntegration
noncomputable section
universe u v
namespace WP.RandomGeometry
open WP.External

/-- The canonical root's r edge slots first, followed by all remaining cusp slots. -/
def pantsStarRootBoundaryEquiv (g n r : ℕ) (f : PantsLabels n r) (hn : 2*r ≤ n) :
    Fin (n-r) ≃ (pantsCutGraph g n r f).Boundary (0 : Fin (r+1)) :=
  (finCongr (show n-r=r+(n-2*r) by omega)).trans
    finSumFinEquiv.symm |>.trans
      (Equiv.sumCongr (pantsStarRootEdgeEquiv g n r f) (pantsStarRootCuspEquiv g n r f))
      |>.trans (Equiv.sumComm _ _)

lemma activeBoundaryLengths_eq_zero {r m : ℕ} (hr : r ≤ m) (x : Fin r → ℝ)
    (i : Fin m) (hi : r ≤ i.val) : activeBoundaryLengths hr x i=0 := by
  classical
  unfold activeBoundaryLengths
  apply Finset.sum_eq_zero
  intro j _
  rw [if_neg]
  intro he
  have hv := congrArg Fin.val he
  simp only [Fin.coe_castLE] at hv
  omega

set_option backward.isDefEq.respectTransparency false in
lemma pantsStarRootBoundaryEquiv_lengths (g n r : ℕ) (f : PantsLabels n r)
    (hn : 2*r ≤ n) (x : Fin r → ℝ) (i : Fin (n-r)) :
    Sum.elim (fun _ => (0:ℝ)) (fun e => x e.val.1)
      ((pantsStarRootBoundaryEquiv g n r f hn).toFun i) =
      activeBoundaryLengths (show r ≤ n-r by omega) x i := by
  classical
  let e := finCongr (show n-r=r+(n-2*r) by omega)
  obtain ⟨j,rfl⟩ := e.symm.surjective i
  refine Fin.addCases ?_ ?_ j
  · intro j
    have hindex : (pantsStarRootBoundaryEquiv g n r f hn).toFun (e.symm (Fin.castAdd (n-2*r) j)) =
        Sum.inr (pantsStarRootEdgeEquiv g n r f j) := by
      simp [pantsStarRootBoundaryEquiv,e,Equiv.trans_apply,Equiv.sumCongr_apply,Equiv.sumComm_apply]
      rfl
    rw [hindex]
    change x j = activeBoundaryLengths _ x (e.symm (Fin.castAdd (n-2*r) j))
    have he : e.symm (Fin.castAdd (n-2*r) j) = Fin.castLE (show r ≤ n-r by omega) j := by
      apply Fin.ext
      rfl
    rw [he,activeBoundaryLengths_apply]
  · intro j
    have hindex : (pantsStarRootBoundaryEquiv g n r f hn).toFun (e.symm (Fin.natAdd r j)) =
        Sum.inl (pantsStarRootCuspEquiv g n r f j) := by
      simp [pantsStarRootBoundaryEquiv,e,Equiv.trans_apply,Equiv.sumCongr_apply,Equiv.sumComm_apply]
      rfl
    rw [hindex]
    change 0 = activeBoundaryLengths _ x (e.symm (Fin.natAdd r j))
    symm
    apply activeBoundaryLengths_eq_zero
    change r ≤ r+j.val
    omega

lemma pants_boundary_volume_genus_zero_three (P : PsiTheory) (L : Fin 3 → ℝ) :
    boundaryVolumeModel P 0 3 L=1 := by
  classical
  have ht : degreeTuples 0 3 = {fun _ : Fin 3 => 0} := by
    ext d
    rw [mem_degreeTuples_iff,Finset.mem_singleton]
    constructor
    · intro hd
      funext i
      have hi := Finset.single_le_sum (fun i _ => Nat.zero_le (d i)) (Finset.mem_univ i)
      have hdim : dimension 0 3=0 := by norm_num [dimension]
      rw [hdim] at hd
      omega
    · rintro rfl
      simp [dimension]
  rw [boundaryVolumeModel,ht]
  simp only [Finset.sum_singleton,List.ofFn_const]
  have hb : mixedBracket P 0 [0,0,0]=1 := by
    dsimp [mixedBracket,shifted,Stable,dimension,deficit,complexity]
    norm_num [backgrounds_zero,backgroundDegrees,pure,oddFactorial,P.base₀,a_zero]
  simp [hb]


/-- The explicit root boundary-slot index equivalence. -/
def pantsStarRootLengthIndexEquiv (g n r : ℕ) (f : PantsLabels n r) (hn : 2*r ≤ n) :
    Fin (n-r) ≃ Fin ((pantsCutGraph g n r f).boundaryCount (0 : Fin (r+1))) := by
  letI : Fintype ((pantsCutGraph g n r f).Boundary (0 : Fin (r+1))) :=
    MulticurveCutData.instFintypeBoundary (pantsCutGraph g n r f) (0 : Fin (r+1))
  exact (pantsStarRootBoundaryEquiv g n r f hn).trans (Fintype.equivFin _)

lemma pants_boundaryLengths_eq_sumElim {n r : ℕ} (D : MulticurveCutData n r)
    (x : Fin r → ℝ) (c : Fin D.components) (i : Fin (D.boundaryCount c)) :
    D.boundaryLengths x c i =
      Sum.elim (fun _ => (0:ℝ)) (fun e => x e.val.1) ((Fintype.equivFin (D.Boundary c)).symm i) := by
  unfold MulticurveCutData.boundaryLengths
  generalize (Fintype.equivFin (D.Boundary c)).symm i=b
  cases b <;> rfl

set_option backward.isDefEq.respectTransparency false in
lemma pantsStar_root_lengths (g n r : ℕ) (f : PantsLabels n r) (hn : 2*r ≤ n)
    (x : Fin r → ℝ) :
    (pantsCutGraph g n r f).boundaryLengths x (0 : Fin (r+1)) ∘
      pantsStarRootLengthIndexEquiv g n r f hn =
        activeBoundaryLengths (show r ≤ n-r by omega) x := by
  let D := pantsCutGraph g n r f
  let c : Fin D.components := ⟨0,by change 0<r+1; omega⟩
  letI : Fintype (D.Boundary c) := MulticurveCutData.instFintypeBoundary D c
  funext i
  let eB : D.Boundary c ≃ Fin (D.boundaryCount c) := Fintype.equivFin _
  have he := eB.symm_apply_apply ((pantsStarRootBoundaryEquiv g n r f hn).toFun i)
  have hm := congrArg (Sum.elim (fun _ => (0:ℝ)) (fun e => x e.val.1) : D.Boundary c → ℝ) he
  have ht := pants_boundaryLengths_eq_sumElim D x c
    ((pantsStarRootLengthIndexEquiv g n r f hn).toFun i)
  exact ht.trans (hm.trans (pantsStarRootBoundaryEquiv_lengths g n r f hn x i))

lemma pantsStar_boundary_lengths_nonneg (g n r : ℕ) (f : PantsLabels n r)
    (x : Fin r → ℝ) (hx : ∀ i, 0 ≤ x i) (c : Fin (r+1)) :
    ∀ j, 0 ≤ (pantsCutGraph g n r f).boundaryLengths x c j := by
  intro j
  unfold MulticurveCutData.boundaryLengths
  split
  · exact le_rfl
  · exact hx _

lemma pantsStar_root_volume (P : PsiTheory) (G : WeilPeterssonGeometry.{u,v} P)
    (g n r : ℕ) (f : PantsLabels n r) (hg : 2 ≤ g) (hn : 2*r ≤ n)
    (x : Fin r → ℝ) (hx : ∀ i, 0 ≤ x i) :
    wpVolume G ((pantsCutGraph g n r f).genus (0 : Fin (r+1)))
      ((pantsCutGraph g n r f).boundaryCount (0 : Fin (r+1)))
      ((pantsCutGraph g n r f).boundaryLengths x (0 : Fin (r+1))) =
        boundaryVolumeModel P g (n-r) (activeBoundaryLengths (show r ≤ n-r by omega) x) := by
  have hs : Stable g ((pantsCutGraph g n r f).boundaryCount (0 : Fin (r+1))) := by
    unfold Stable
    omega
  change wpVolume G g _ _ = _
  rw [WP.Geometry.wpVolume_eq_boundaryVolumeModel P G g _ _ hs
    (pantsStar_boundary_lengths_nonneg g n r f x hx (0 : Fin (r+1)))]
  have he := boundaryVolumeModel_reindex P g (n-r) _
    ((pantsCutGraph g n r f).boundaryLengths x (0 : Fin (r+1)))
    (pantsStarRootLengthIndexEquiv g n r f hn)
  rw [pantsStar_root_lengths g n r f hn x] at he
  exact he.symm

lemma pantsStar_leaf_volume (P : PsiTheory) (G : WeilPeterssonGeometry.{u,v} P)
    (g n r : ℕ) (f : PantsLabels n r) (x : Fin r → ℝ) (hx : ∀ i, 0 ≤ x i)
    (e : Fin r) :
    wpVolume G ((pantsCutGraph g n r f).genus e.succ)
      ((pantsCutGraph g n r f).boundaryCount e.succ)
      ((pantsCutGraph g n r f).boundaryLengths x e.succ) = 1 := by
  have hcount := pantsStar_leaf_boundaryCount g n r f e
  have hs : Stable 0 ((pantsCutGraph g n r f).boundaryCount e.succ) := by
    rw [hcount]
    norm_num [Stable]
  have hg : (pantsCutGraph g n r f).genus e.succ = 0 := by
    simp only [pantsCutGraph,Fin.succ_ne_zero,ite_false]
  rw [hg,WP.Geometry.wpVolume_eq_boundaryVolumeModel P G 0 _ _ hs
    (pantsStar_boundary_lengths_nonneg g n r f x hx e.succ)]
  have hthree : ∀ (m : ℕ), m=3 → ∀ L : Fin m → ℝ,
      boundaryVolumeModel P 0 m L=1 := by
    intro m hm L
    subst m
    exact pants_boundary_volume_genus_zero_three P L
  exact hthree _ hcount _

/-- The actual genus-g canonical pants star contributes exactly the root
volume, with physical lengths x and all uncut original cusp lengths zero. -/
lemma pantsStar_volumeProduct (P : PsiTheory) (G : WeilPeterssonGeometry.{u,v} P)
    (g n r : ℕ) (f : PantsLabels n r) (hg : 2 ≤ g) (hn : 2*r ≤ n)
    (x : Fin r → ℝ) (hx : ∀ i, 0 ≤ x i) :
    (pantsCutGraph g n r f).volumeProduct G x =
      boundaryVolumeModel P g (n-r) (activeBoundaryLengths (show r ≤ n-r by omega) x) := by
  change (∏ c : Fin (r+1), wpVolume G _ _ _) = _
  rw [Fin.prod_univ_succ,pantsStar_root_volume P G g n r f hg hn x hx]
  have hl : (∏ i : Fin r,
      wpVolume G ((pantsCutGraph g n r f).genus i.succ)
        ((pantsCutGraph g n r f).boundaryCount i.succ)
        ((pantsCutGraph g n r f).boundaryLengths x i.succ)) = 1 := by
    apply Finset.prod_eq_one
    intro i _
    exact pantsStar_leaf_volume P G g n r f x hx i
  rw [hl,mul_one]

end WP.RandomGeometry
