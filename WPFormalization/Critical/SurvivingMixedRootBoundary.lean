import WPFormalization.Critical.SurvivingMixedStable
import WPFormalization.RandomGeometry.PantsMomentAsymptoticsStarVolume
noncomputable section
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false
namespace WP.Critical
open WP.External WP.RandomGeometry Finset
open scoped Classical

/-- Both sides of each loop are retained separately. -/
def mixedLoopHalfEdgeEquiv (k : ℕ) : (Fin k ⊕ Fin k) ≃ (Fin k × Fin 2) where
  toFun := Sum.elim (fun i => (i,0)) (fun i => (i,1))
  invFun p := if p.2=0 then Sum.inl p.1 else Sum.inr p.1
  left_inv p := by cases p <;> simp
  right_inv p := by rcases p with ⟨i,j⟩; fin_cases j <;> simp

def survivingMixedRootEdgeEquiv (g n r k : ℕ) (f : PantsLabels n r) :
    (Fin r ⊕ (Fin k × Fin 2)) ≃
      {p : Fin (r+k) × Fin 2 // (survivingMixedCutGraph g n r k f).edgeVertex p=(0 : Fin (r+1))} where
  toFun := Sum.elim (fun i => ⟨(i.castAdd k,0),by simp [survivingMixedCutGraph]⟩)
    (fun p => ⟨(Fin.natAdd r p.1,p.2),by simp [survivingMixedCutGraph]⟩)
  invFun p := Fin.addCases (fun i => Sum.inl i) (fun i => Sum.inr (i,p.val.2)) p.val.1
  left_inv p := by cases p <;> simp
  right_inv p := by
    apply Subtype.ext
    rcases p with ⟨⟨e,j⟩,he⟩
    revert he
    refine Fin.addCases (fun i => ?_) (fun i => ?_) e
    · intro he
      have hj : j=0 := by
        by_contra hj
        have hh : i.succ=(0 : Fin (r+1)) := by simpa [survivingMixedCutGraph,hj] using he
        exact Fin.succ_ne_zero i hh
      subst j
      simp
    · intro he
      simp

/-- The r pants slots, then the two blocks of k loop-side slots. -/
def survivingMixedRootCoreEquiv (g n r k : ℕ) (f : PantsLabels n r) :
    Fin (r+(k+k)) ≃
      {p : Fin (r+k) × Fin 2 // (survivingMixedCutGraph g n r k f).edgeVertex p=(0 : Fin (r+1))} :=
  finSumFinEquiv.symm |>.trans
    (Equiv.sumCongr (Equiv.refl _) (finSumFinEquiv.symm.trans (mixedLoopHalfEdgeEquiv k)))
    |>.trans (survivingMixedRootEdgeEquiv g n r k f)

/-- Every root boundary side or original cusp appears once, in physical
order (s,t,t,0), including both incidences of each loop. -/
def survivingMixedRootBoundaryEquiv (g n r k : ℕ) (f : PantsLabels n r) (hn : 2*r ≤ n) :
    Fin (n-r+2*k) ≃ (survivingMixedCutGraph g n r k f).Boundary (0 : Fin (r+1)) :=
  (finCongr (show n-r+2*k=(r+(k+k))+(n-2*r) by omega)).trans finSumFinEquiv.symm
    |>.trans (Equiv.sumCongr (survivingMixedRootCoreEquiv g n r k f)
      (pantsStarRootCuspEquiv (g-k) n r f))
    |>.trans (Equiv.sumComm _ _)

lemma survivingMixed_root_boundaryCount (g n r k : ℕ) (f : PantsLabels n r) (hn : 2*r ≤ n) :
    (survivingMixedCutGraph g n r k f).boundaryCount (0 : Fin (r+1))=n-r+2*k := by
  exact (Fintype.card_congr (survivingMixedRootBoundaryEquiv g n r k f hn)).symm.trans
    (Fintype.card_fin _)

lemma survivingMixedRootCoreEquiv_lengths (g n r k : ℕ) (f : PantsLabels n r)
    (x : Fin (r+k) → ℝ) (i : Fin (r+(k+k))) :
    x ((survivingMixedRootCoreEquiv g n r k f i).val.1)=
      Fin.append (fun j => x (j.castAdd k))
        (Fin.append (fun j => x (Fin.natAdd r j)) (fun j => x (Fin.natAdd r j))) i := by
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp [survivingMixedRootCoreEquiv,survivingMixedRootEdgeEquiv,Equiv.trans_apply,
      Equiv.sumCongr_apply]
  · refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    · simp [survivingMixedRootCoreEquiv,survivingMixedRootEdgeEquiv,mixedLoopHalfEdgeEquiv,
        Equiv.trans_apply,Equiv.sumCongr_apply]
    · simp [survivingMixedRootCoreEquiv,survivingMixedRootEdgeEquiv,mixedLoopHalfEdgeEquiv,
        Equiv.trans_apply,Equiv.sumCongr_apply]
      have he : j.addNat k=Fin.natAdd k j := by
        apply Fin.ext
        simp [Nat.add_comm]
      rw [he,finSumFinEquiv_symm_apply_natAdd,Fin.append_right]
      rfl

lemma survivingMixedRootBoundaryEquiv_lengths (g n r k : ℕ) (f : PantsLabels n r)
    (hn : 2*r ≤ n) (x : Fin (r+k) → ℝ) (i : Fin (n-r+2*k)) :
    Sum.elim (fun _ => (0:ℝ)) (fun e => x e.val.1)
      (survivingMixedRootBoundaryEquiv g n r k f hn i)=
      if h : i.val < r+(k+k) then
        Fin.append (fun j => x (j.castAdd k))
          (Fin.append (fun j => x (Fin.natAdd r j)) (fun j => x (Fin.natAdd r j))) ⟨i.val,h⟩ else 0 := by
  let e := finCongr (show n-r+2*k=(r+(k+k))+(n-2*r) by omega)
  obtain ⟨j,rfl⟩ := e.symm.surjective i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) j
  · have hindex : survivingMixedRootBoundaryEquiv g n r k f hn (e.symm (j.castAdd (n-2*r)))=
        Sum.inr (survivingMixedRootCoreEquiv g n r k f j) := by
      simp [survivingMixedRootBoundaryEquiv,e,Equiv.trans_apply,Equiv.sumCongr_apply,Equiv.sumComm_apply]
      rfl
    rw [hindex]
    refine (survivingMixedRootCoreEquiv_lengths g n r k f x j).trans ?_
    rw [dif_pos (show (e.symm (j.castAdd (n-2*r))).val < r+(k+k) by exact j.isLt)]
    rfl
  · have hindex : survivingMixedRootBoundaryEquiv g n r k f hn (e.symm (Fin.natAdd (r+(k+k)) j))=
        Sum.inl (pantsStarRootCuspEquiv (g-k) n r f j) := by
      simp [survivingMixedRootBoundaryEquiv,e,Equiv.trans_apply,Equiv.sumCongr_apply,Equiv.sumComm_apply]
      rfl
    rw [hindex]
    rw [dif_neg (show ¬ (e.symm (Fin.natAdd (r+(k+k)) j)).val < r+(k+k) by
      change ¬ r+(k+k)+j.val < r+(k+k); omega)]
    rfl

def survivingMixedRootLengthIndexEquiv (g n r k : ℕ) (f : PantsLabels n r) (hn : 2*r ≤ n) :
    Fin (n-r+2*k) ≃ Fin ((survivingMixedCutGraph g n r k f).boundaryCount (0 : Fin (r+1))) :=
  (survivingMixedRootBoundaryEquiv g n r k f hn).trans (Fintype.equivFin _)

lemma survivingMixed_root_lengths (g n r k : ℕ) (f : PantsLabels n r)
    (hn : 2*r ≤ n) (x : Fin (r+k) → ℝ) :
    (survivingMixedCutGraph g n r k f).boundaryLengths x (0 : Fin (r+1)) ∘
      survivingMixedRootLengthIndexEquiv g n r k f hn =
      fun i => if h : i.val < r+(k+k) then
        Fin.append (fun j => x (j.castAdd k))
          (Fin.append (fun j => x (Fin.natAdd r j)) (fun j => x (Fin.natAdd r j))) ⟨i.val,h⟩ else 0 := by
  let D := survivingMixedCutGraph g n r k f
  let c : Fin D.components := ⟨0,by change 0<r+1; omega⟩
  funext i
  let eB : D.Boundary c ≃ Fin (D.boundaryCount c) := Fintype.equivFin _
  have he := eB.symm_apply_apply (survivingMixedRootBoundaryEquiv g n r k f hn i)
  have hm := congrArg (Sum.elim (fun _ => (0:ℝ)) (fun e => x e.val.1) : D.Boundary c → ℝ) he
  have ht := pants_boundaryLengths_eq_sumElim D x c (survivingMixedRootLengthIndexEquiv g n r k f hn i)
  exact ht.trans (hm.trans (survivingMixedRootBoundaryEquiv_lengths g n r k f hn x i))
end WP.Critical
