import WPFormalization.Intersection.ProfileMonotone
import WPFormalization.Weighted.NodeBounds
import WPFormalization.Weighted.LinearNormalization
/-! Actual stable admissible comparison states and a certified symmetric pivot.
The chosen pivot is positive whenever one exists; otherwise all entries are
zero. All permutation identifications concern the original normalized and
harmonic quantities. -/
noncomputable section
namespace WP

lemma ratio_perm (P : PsiTheory) (g : ℕ) {d e : List ℕ} (hp : d.Perm e) (Y : ℝ) :
    ratio P g d Y = ratio P g e Y := by
  unfold ratio
  rw [normalized_perm P g hp Y,model_perm g hp Y]

abbrev ComparisonState := {q : ℕ × List ℕ //
  1 ≤ q.2.length ∧ Stable q.1 q.2.length ∧ q.2.sum ≤ dimension q.1 q.2.length}

structure ComparisonPivot (d : List ℕ) where
  pivot : ℕ
  tail : List ℕ
  perm : d.Perm (pivot::tail)
  choice : 0 < pivot ∨ (pivot=0 ∧ ∀ k ∈ tail, k=0)

lemma comparisonPivot_exists (d : List ℕ) (hn : 1 ≤ d.length) :
    Nonempty (ComparisonPivot d) := by
  by_cases hp : ∃ p ∈ d, 0 < p
  · obtain ⟨p,hp,hpos⟩ := hp
    obtain ⟨l,r,rfl⟩ := List.mem_iff_append.mp hp
    exact ⟨⟨p,l++r,List.perm_middle,Or.inl hpos⟩⟩
  · have hz : ∀ p ∈ d, p=0 := by push_neg at hp;intro p hp';have := hp p hp';omega
    cases d with
    | nil => simp at hn
    | cons p d =>
      have hp0 : p=0 := hz p (by simp)
      subst p
      exact ⟨⟨0,d,List.Perm.refl _,Or.inr ⟨rfl,fun k hk => hz k (by simp [hk])⟩⟩⟩

namespace ComparisonState

def genus (x : ComparisonState) : ℕ := x.val.1
def degrees (x : ComparisonState) : List ℕ := x.val.2
def rank (x : ComparisonState) : ℕ := complexity x.genus x.degrees.length
def zeroCount (x : ComparisonState) : ℕ := zeros x.degrees
def terminal (x : ComparisonState) : Prop := Terminal x.genus x.degrees
lemma nonempty (x : ComparisonState) : 1 ≤ x.degrees.length := x.property.1
lemma stable (x : ComparisonState) : Stable x.genus x.degrees.length := x.property.2.1
lemma admissible (x : ComparisonState) : x.degrees.sum ≤ dimension x.genus x.degrees.length := x.property.2.2
lemma rank_pos (x : ComparisonState) : 1 ≤ x.rank := by
  have hs := x.stable
  unfold Stable at hs
  unfold rank complexity
  omega
lemma nonterminal_genus (x : ComparisonState) (hx : ¬x.terminal) : 2 ≤ x.genus := by
  change ¬(deficit x.genus x.degrees=0 ∨ x.genus≤1) at hx
  omega
lemma nonterminal_deficit (x : ComparisonState) (hx : ¬x.terminal) : 1 ≤ deficit x.genus x.degrees := by
  change ¬(deficit x.genus x.degrees=0 ∨ x.genus≤1) at hx
  omega

noncomputable def pivotData (x : ComparisonState) : ComparisonPivot x.degrees :=
  Classical.choice (comparisonPivot_exists x.degrees x.nonempty)
noncomputable def pivot (x : ComparisonState) : ℕ := x.pivotData.pivot
noncomputable def tail (x : ComparisonState) : List ℕ := x.pivotData.tail
lemma pivot_perm (x : ComparisonState) : x.degrees.Perm (x.pivot::x.tail) := x.pivotData.perm
lemma pivot_choice (x : ComparisonState) : 0<x.pivot ∨ (x.pivot=0 ∧ ∀ k ∈ x.tail,k=0) := x.pivotData.choice
lemma pivot_length (x : ComparisonState) : x.tail.length+1=x.degrees.length := by
  simpa using x.pivot_perm.length_eq.symm
lemma pivot_sum (x : ComparisonState) : x.pivot+x.tail.sum=x.degrees.sum := by
  simpa using x.pivot_perm.sum_eq.symm
lemma rank_pivot (x : ComparisonState) : complexity x.genus (x.tail.length+1)=x.rank := by
  rw [x.pivot_length]
  rfl
lemma deficit_pivot (x : ComparisonState) : deficit x.genus (x.pivot::x.tail)=deficit x.genus x.degrees := by
  unfold deficit
  rw [←x.pivot_perm.length_eq,←x.pivot_perm.sum_eq]
lemma pivot_admissible (x : ComparisonState) :
    (x.pivot::x.tail).sum ≤ dimension x.genus (x.tail.length+1) := by
  simpa only [List.sum_cons,x.pivot_sum,x.pivot_length] using x.admissible
lemma pivot_normalized (x : ComparisonState) (P : PsiTheory) (Y : ℝ) :
    normalized P x.genus x.degrees Y = normalized P x.genus (x.pivot::x.tail) Y :=
  normalized_perm P x.genus x.pivot_perm Y
lemma pivot_model (x : ComparisonState) (Y : ℝ) :
    model x.genus x.degrees Y = model x.genus (x.pivot::x.tail) Y := model_perm x.genus x.pivot_perm Y
lemma pivot_ratio (x : ComparisonState) (P : PsiTheory) (Y : ℝ) :
    ratio P x.genus x.degrees Y = ratio P x.genus (x.pivot::x.tail) Y := ratio_perm P x.genus x.pivot_perm Y
lemma pivot_zeros (x : ComparisonState) : zeros (x.pivot::x.tail)=x.zeroCount :=
  (zeros_perm x.pivot_perm).symm
end ComparisonState
end WP
