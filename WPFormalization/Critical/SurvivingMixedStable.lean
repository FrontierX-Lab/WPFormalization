import WPFormalization.Critical.SurvivingMixedCutGraph
noncomputable section
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false
namespace WP.Critical
open WP.External WP.RandomGeometry Finset
open scoped Classical

lemma survivingMixed_edge_leaf_iff (g n r k : ℕ) (f : PantsLabels n r) (i : Fin r)
    (p : Fin (r+k) × Fin 2) :
    (survivingMixedCutGraph g n r k f).edgeVertex p=i.succ ↔ p=(i.castAdd k,1) := by
  rcases p with ⟨e,j⟩
  refine Fin.addCases (fun e => ?_) (fun e => ?_) e
  · fin_cases j <;> simp [survivingMixedCutGraph,(Fin.succ_ne_zero i).symm]
  · have he : Fin.natAdd r e ≠ i.castAdd k := by
      intro he
      have hv := congrArg Fin.val he
      simp only [Fin.coe_natAdd,Fin.coe_castAdd] at hv
      have := i.isLt
      omega
    simp [survivingMixedCutGraph,(Fin.succ_ne_zero i).symm,he]

def survivingMixedLeafEdgeEquiv (g n r k : ℕ) (f : PantsLabels n r) (e : Fin r) :
    Unit ≃ {p : Fin (r+k) × Fin 2 // (survivingMixedCutGraph g n r k f).edgeVertex p=e.succ} where
  toFun _ := ⟨(e.castAdd k,1),by simp [survivingMixedCutGraph]⟩
  invFun _ := ()
  left_inv _ := rfl
  right_inv p := Subtype.ext ((survivingMixed_edge_leaf_iff g n r k f e p.val).mp p.property).symm

lemma survivingMixed_leaf_boundaryCount (g n r k : ℕ) (f : PantsLabels n r) (e : Fin r) :
    (survivingMixedCutGraph g n r k f).boundaryCount e.succ=3 := by
  let E : (Fin 2 ⊕ Unit) ≃ (survivingMixedCutGraph g n r k f).Boundary e.succ :=
    Equiv.sumCongr (pantsStarLeafCuspEquiv (g-k) n r f e)
      (survivingMixedLeafEdgeEquiv g n r k f e)
  change Fintype.card ((survivingMixedCutGraph g n r k f).Boundary e.succ)=3
  exact (Fintype.card_congr E).symm.trans (by simp)

lemma survivingMixed_stable (g n r k : ℕ) (f : PantsLabels n r) (hg : k+2 ≤ g) :
    ∀ c, Stable ((survivingMixedCutGraph g n r k f).genus c)
      ((survivingMixedCutGraph g n r k f).boundaryCount c) := by
  intro c
  refine Fin.cases ?_ (fun i => ?_) c
  · change 2 < 2*(g-k)+(survivingMixedCutGraph g n r k f).boundaryCount (0 : Fin (r+1))
    omega
  · change 2 < 2*(if i.succ=0 then g-k else 0)+_
    rw [if_neg (Fin.succ_ne_zero i),survivingMixed_leaf_boundaryCount]
    norm_num
end WP.Critical
