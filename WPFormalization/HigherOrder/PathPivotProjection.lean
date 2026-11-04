import WPFormalization.HigherOrder.BoundaryCoordinatePullback
import WPFormalization.HigherOrder.Coherence
import WPFormalization.HigherOrder.MergerTuple
/-! The actual beforeCoordinate state, with its distinguished pivot moved first and its erased tail kept in order, is a zero/coordinate projection of the raw path variables. The adjacentCoefficient identity is definitional in its getter and erased tail; no permutation symmetry or path-independence theorem is used. -/
noncomputable section
namespace WP.HigherOrder.JointBoundary

def pathPivotProjection {m : ℕ} (i : Fin (m + 1)) :
    Fin (m + 1) → Option (Fin (m + 2)) :=
  Fin.cases (some 0) (fun k =>
    if (i.succAbove k).val < i.val then some (i.succAbove k).succ else none)

lemma beforeCoordinate_ofFn {m : ℕ} (d : Fin (m + 1) → ℕ) (i : Fin (m + 1)) (t : ℕ) :
    beforeCoordinate (List.ofFn d) i.val t =
      List.ofFn (fun j : Fin (m + 1) =>
        if j.val < i.val then d j else if j.val = i.val then t else 0) := by
  simp only [beforeCoordinate, List.length_ofFn]
  congr 1
  funext j
  simp only [Fin.val_cast, List.getElem!_eq_getElem?_getD, List.getElem?_ofFn,
    dite_eq_left j.isLt, Option.getD_some]

lemma pathPivotProjection_list {m : ℕ} (i : Fin (m + 1)) (d : Fin (m + 1) → ℕ) (t : ℕ) :
    List.ofFn (projectNat (pathPivotProjection i) (Fin.cases t d)) =
      t :: (beforeCoordinate (List.ofFn d) i.val t).eraseIdx i.val := by
  rw [List.ofFn_succ, beforeCoordinate_ofFn,
    ← eraseIdx_ofFn_eq (fun j : Fin (m + 1) => if j.val < i.val then d j else if j.val = i.val then t else 0) i]
  congr 1
  apply congrArg List.ofFn
  funext k
  have hne : (i.succAbove k).val ≠ i.val := fun h => Fin.succAbove_ne i k (Fin.ext h)
  simp only [projectNat, pathPivotProjection, Fin.cases_succ, hne, ite_false]
  split_ifs <;> rfl

lemma pathPivotProjection_list_raw {m : ℕ} (i : Fin (m + 1)) (v : Fin (m + 2) → ℕ) :
    List.ofFn (projectNat (pathPivotProjection i) v) =
      v 0 :: (beforeCoordinate (List.ofFn (fun j => v j.succ)) i.val (v 0)).eraseIdx i.val := by
  have hv : Fin.cases (v 0) (fun j => v j.succ) = v := by
    funext j
    refine Fin.cases ?_ (fun k => ?_) j <;> rfl
  simpa only [hv] using pathPivotProjection_list i (fun j => v j.succ) (v 0)

lemma adjacent_beforeCoordinate_project (P : PsiTheory) (Y : ℝ) (F : HierarchyJet) (K : ℕ)
    {m : ℕ} (i : Fin (m + 1)) (v : Fin (m + 2) → ℕ) :
    adjacentCoefficient P Y F K i.val
        (beforeCoordinate (List.ofFn (fun j => v j.succ)) i.val (v 0)) =
      adjacentCoefficient P Y F K 0 (List.ofFn (projectNat (pathPivotProjection i) v)) := by
  have hi : i.val < (List.ofFn (fun j : Fin (m + 1) => v j.succ)).length := by
    simpa only [List.length_ofFn] using i.isLt
  rw [pathPivotProjection_list_raw]
  unfold adjacentCoefficient
  rw [beforeCoordinate_self _ _ _ hi]
  simp only [List.getElem!_eq_getElem?_getD, List.getElem?_cons_zero, Option.getD_some,
    List.eraseIdx_cons_zero]
end WP.HigherOrder.JointBoundary
