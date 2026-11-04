import WPFormalization.Statements.Basic
import WPFormalization.RandomGeometry.PantsCutGraph
import WPFormalization.RandomGeometry.PantsMomentAsymptoticsStarBoundary

/-! Topological realization hypotheses for the canonical pants star. -/
noncomputable section
namespace WP.RandomGeometry
open WP.External

lemma pantsStar_connected (g n r : ℕ) (f : PantsLabels n r) :
    (pantsCutGraph g n r f).ConnectedWithin Finset.univ := by
  classical
  let D := pantsCutGraph g n r f
  let root : Fin D.components := ⟨0,by change 0 < r+1; omega⟩
  have hadj (i : Fin r) : D.AdjacentWithin Finset.univ root i.succ := by
    refine ⟨Finset.mem_univ _,Finset.mem_univ _,i,Or.inl ?_⟩
    constructor <;> simp [D,pantsCutGraph,root]
  have hadj' (i : Fin r) : D.AdjacentWithin Finset.univ i.succ root := by
    refine ⟨Finset.mem_univ _,Finset.mem_univ _,i,Or.inr ?_⟩
    constructor <;> simp [D,pantsCutGraph,root]
  have hr (c : Fin D.components) : Relation.ReflTransGen (D.AdjacentWithin Finset.univ) root c := by
    refine Fin.cases ?_ (fun i => Relation.ReflTransGen.single (hadj i)) c
    exact Relation.ReflTransGen.refl
  have hr' (c : Fin D.components) : Relation.ReflTransGen (D.AdjacentWithin Finset.univ) c root := by
    refine Fin.cases ?_ (fun i => Relation.ReflTransGen.single (hadj' i)) c
    exact Relation.ReflTransGen.refl
  refine ⟨⟨root,Finset.mem_univ _⟩,?_⟩
  intro a _ b _
  exact (hr' a).trans (hr b)

lemma pantsStar_euler (g n r : ℕ) (f : PantsLabels n r) :
    (∑c, (pantsCutGraph g n r f).genus c) + r + 1 =
      g + (pantsCutGraph g n r f).components := by
  have hs : (∑c, (pantsCutGraph g n r f).genus c) = g := by
    change (∑c : Fin (r+1), if c=0 then g else 0) = g
    simp [Fin.sum_univ_succ]
  rw [hs]
  rfl

lemma pantsStar_stable (g n r : ℕ) (f : PantsLabels n r) (hg : 2 ≤ g) :
    ∀c, Stable ((pantsCutGraph g n r f).genus c)
      ((pantsCutGraph g n r f).boundaryCount c) := by
  intro c
  refine Fin.cases ?_ (fun i => ?_) c
  · change 2 < 2*g + (pantsCutGraph g n r f).boundaryCount (0 : Fin (r+1))
    omega
  · have hc := pantsStar_leaf_boundaryCount g n r f i
    change 2 < 2*(if i.succ=0 then g else 0) + _
    rw [if_neg (Fin.succ_ne_zero i),hc]
    norm_num

end WP.RandomGeometry
