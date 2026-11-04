import WPFormalization.Statements.Basic
import WPFormalization.RandomGeometry.GeneralPlanarStarCutBoundary

/-! Realization hypotheses and classification of actual labeled planar stars. -/
noncomputable section
namespace WP.RandomGeometry
open WP.External

lemma generalPlanarStarCut_stable (g n r : ℕ) (k : Fin r → ℕ)
    (f : PlanarLabelBlocks n r k) (hg : 2 ≤ g) (hk : ∀ i, 2 ≤ k i) :
    ∀ c, Stable ((generalPlanarStarCut g n r k f).genus c)
      ((generalPlanarStarCut g n r k f).boundaryCount c) := by
  intro c
  refine Fin.cases ?_ (fun i => ?_) c
  · change 2 < 2*g + (generalPlanarStarCut g n r k f).boundaryCount (0 : Fin (r+1))
    omega
  · have hc := generalPlanarStarCut_leaf_boundaryCount g n r k f i
    change 2 < 2*(if i.succ=0 then g else 0) + _
    rw [if_neg (Fin.succ_ne_zero i),hc]
    have hi := hk i
    omega

lemma generalPlanarStarCut_no_oneHandle (g n r : ℕ) (k : Fin r → ℕ)
    (f : PlanarLabelBlocks n r k) (hg : 2 ≤ g) (hk : ∀ i, 2 ≤ k i) (e : Fin r) :
    ¬ (generalPlanarStarCut g n r k f).HasOneHandleSide e := by
  classical
  let D := generalPlanarStarCut g n r k f
  rintro ⟨U,hs,hgU,hc⟩
  have hnotleaf : ∀ i : Fin r, i.succ ∉ U := by
    intro i hi
    let a : Fin (k i) := ⟨0, by have := hk i; omega⟩
    have hm : f.val ⟨i,a⟩ ∈ D.cuspSet U := by
      simp only [MulticurveCutData.cuspSet,Finset.mem_filter,Finset.mem_univ,true_and]
      change (generalPlanarStarCut g n r k f).cuspVertex (f.val ⟨i,a⟩) ∈ U
      rw [generalPlanarStarCut_cusp_apply]
      exact hi
    rw [hc] at hm
    simp at hm
  let z : Fin D.components := ⟨0,by change 0 < r+1; omega⟩
  have hsub : U ⊆ {z} := by
    intro c hc
    apply Finset.mem_singleton.mpr
    have hcases : c=z ∨ ∃ i : Fin r, c=i.succ := by
      change (c : Fin (r+1))=(0 : Fin (r+1)) ∨ ∃ i : Fin r,c=i.succ
      exact Fin.cases (Or.inl rfl) (fun i => Or.inr ⟨i,rfl⟩) c
    rcases hcases with h | ⟨i,h⟩
    · exact h
    · exact (hnotleaf i (h ▸ hc)).elim
  have hU : U={z} := by
    apply Finset.eq_singleton_iff_unique_mem.mpr
    rcases hs.1 with ⟨c,hc⟩
    have he : c=z := Finset.mem_singleton.mp (hsub hc)
    exact ⟨he ▸ hc,fun j hj => Finset.mem_singleton.mp (hsub hj)⟩
  rw [hU] at hgU
  change (∑ c ∈ ({z} : Finset (Fin D.components)),D.genus c)+_+1=_+1 at hgU
  simp only [Finset.sum_singleton,Finset.card_singleton] at hgU
  have hroot : D.genus z=g := by simp [D,generalPlanarStarCut,z]
  omega

lemma generalPlanarStarCut_oneHandleCount (g n r : ℕ) (k : Fin r → ℕ)
    (f : PlanarLabelBlocks n r k) (hg : 2 ≤ g) (hk : ∀ i, 2 ≤ k i) :
    (generalPlanarStarCut g n r k f).oneHandleCount=0 := by
  classical
  simp [MulticurveCutData.oneHandleCount,generalPlanarStarCut_no_oneHandle g n r k f hg hk]

set_option backward.isDefEq.respectTransparency false in
lemma generalPlanarStarCut_isomorphism_labels (g n r : ℕ) (k : Fin r → ℕ)
    (f q : PlanarLabelBlocks n r k) (hg : 0 < g)
    (I : MulticurveCutData.Isomorphism (generalPlanarStarCut g n r k f)
      (generalPlanarStarCut g n r k q)) : f=q := by
  classical
  let v : Fin (r+1) ≃ Fin (r+1) := I.vertexEquiv
  have hv0 : v (0 : Fin (r+1))=0 := by
    have hh := I.genus_eq (0 : Fin (r+1))
    by_contra hn
    have he : v (0 : Fin (r+1)) ≠ 0 := hn
    change (if v 0=0 then g else 0)=g at hh
    rw [if_neg he] at hh
    omega
  have hflip : ∀ i,I.flip i=false := by
    intro i
    cases hi : I.flip i
    · rfl
    · have hh : v (0 : Fin (r+1))=i.succ := by
        simpa [generalPlanarStarCut,v,hi] using I.edge_eq i 0
      exact (Fin.succ_ne_zero i (hv0.symm.trans hh).symm).elim
  have hvleaf (i : Fin r) : v i.succ=i.succ := by
    simpa [generalPlanarStarCut,v,hflip i] using I.edge_eq i 1
  apply f.eq_of_row_cover q
  intro i j
  apply (generalPlanarStarCut_cusp_leaf_iff g n r k q i (f.val ⟨i,j⟩)).mp
  have hh := I.cusp_eq (f.val ⟨i,j⟩)
  rw [generalPlanarStarCut_cusp_apply] at hh
  exact hh.symm.trans (hvleaf i)

end WP.RandomGeometry
