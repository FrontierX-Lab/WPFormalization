import WPFormalization.Critical.CutCuspLabels

/-! Exact allocation of individually labeled cusps to the two ordered sides.
The cardinality parameter retains both empty fibers. -/
noncomputable section
namespace WP.RandomGeometry
open WP.Critical Finset

def separatingCuspSet {n : ℕ} (σ : Fin n→Fin 2) : Finset (Fin n) :=
  univ.filter (fun i=>σ i=0)

def separatingCuspSetEquiv (n : ℕ) : (Fin n→Fin 2)≃Finset (Fin n) where
  toFun:=separatingCuspSet
  invFun:=fun S i=>if i∈S then 0 else 1
  left_inv:=by
    intro σ
    funext i
    change (if i∈separatingCuspSet σ then (0:Fin 2) else 1)=σ i
    by_cases h : σ i=0
    · simp [separatingCuspSet,h]
    · simp only [separatingCuspSet,mem_filter,mem_univ,true_and,h,if_false]
      apply Fin.ext
      have hi:= (σ i).isLt
      have hn : (σ i).val≠0 := by intro he;apply h;exact Fin.ext he
      simp only [Fin.val_one]
      omega
  right_inv:=by
    intro S
    ext i
    by_cases hi : i∈S <;> simp [separatingCuspSet,hi]

lemma separatingCuspSet_card {n : ℕ} (σ : Fin n→Fin 2) :
    (separatingCuspSet σ).card=cutCuspHistogram σ 0 := by
  rw [cutCuspHistogram_eq_card]
  simp [separatingCuspSet,Fintype.card_subtype]

lemma separating_cusp_assignment_sum {M : Type*} [AddCommMonoid M]
    (n : ℕ) (f : ℕ→M) :
    (∑σ : Fin n→Fin 2,f (cutCuspHistogram σ 0))=
      ∑k∈range (n+1),n.choose k • f k := by
  classical
  calc
    _=∑σ : Fin n→Fin 2,f ((separatingCuspSetEquiv n σ).card) := by
      apply sum_congr rfl
      intro σ _
      rw [←separatingCuspSet_card]
      rfl
    _=∑S : Finset (Fin n),f S.card := Equiv.sum_comp (separatingCuspSetEquiv n) (fun S : Finset (Fin n)=>f S.card)
    _=∑S∈(univ : Finset (Fin n)).powerset,f S.card := by simp
    _=∑k∈range (n+1),n.choose k • f k := by
      rw [Finset.sum_powerset]
      simp_rw [Finset.sum_powersetCard]
      simp

end WP.RandomGeometry
