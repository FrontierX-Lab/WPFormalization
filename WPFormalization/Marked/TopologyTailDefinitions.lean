import WPFormalization.Marked.SmallLossLayers
import WPFormalization.Marked.SeparatingRemainder

/-! The actual smaller-complexity loss tails of Appendix C. For c=1 the two losses are the stable component complexities plus one; for c=2 they are the component complexities. Requiring both losses >= L is precisely the smaller-loss cutoff. The unfiltered masses are the original separating S and T sums. -/
noncomputable section
namespace WP
open Set
def markedSplitLossTailGenus (P : PsiTheory) (g p c L j : ℕ) (Y : ℝ) : ℝ :=
  ∑ s ∈ Finset.range (p-c+1), if L ≤ 2*j+s ∧ L ≤ 2*(g-j)+(p-c-s) then
    markedSplitTerm P g p c j s Y else 0

def markedSplitLossTail (P : PsiTheory) (g p c L : ℕ) (Y : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (g+1), markedSplitLossTailGenus P g p c L j Y

lemma markedSplitLossTailGenus_nonneg (P : PsiTheory) (g p c L j : ℕ) (hg : 2 ≤ g)
    (hp : 2 ≤ p) (hc : c=1 ∨ c=2) (Y : ℝ) (hY : Y ∈ Icc 0 y₀) :
    0 ≤ markedSplitLossTailGenus P g p c L j Y := by
  apply Finset.sum_nonneg
  intro s hs
  have hs0 := Finset.mem_range.mp hs
  split_ifs
  · exact markedSplitTerm_nonneg P g p c j s hg hp hc (by omega) Y hY
  · exact le_rfl

lemma markedSplitLossTailGenus_le (P : PsiTheory) (g p c L j : ℕ) (hg : 2 ≤ g)
    (hp : 2 ≤ p) (hc : c=1 ∨ c=2) (Y : ℝ) (hY : Y ∈ Icc 0 y₀) :
    markedSplitLossTailGenus P g p c L j Y ≤ markedSplitGenus P g p c j Y := by
  apply Finset.sum_le_sum
  intro s hs
  have hs0 := Finset.mem_range.mp hs
  split_ifs
  · exact le_rfl
  · exact markedSplitTerm_nonneg P g p c j s hg hp hc (by omega) Y hY

lemma markedSplitLossTailGenus_symm (P : PsiTheory) (g p c L j : ℕ) (hp : 2 ≤ p)
    (hc : c=1 ∨ c=2) (hj : j ≤ g) (Y : ℝ) :
    markedSplitLossTailGenus P g p c L (g-j) Y = markedSplitLossTailGenus P g p c L j Y := by
  unfold markedSplitLossTailGenus
  rw [←Finset.sum_range_reflect (fun s => if L ≤ 2*(g-j)+s ∧
    L ≤ 2*(g-(g-j))+(p-c-s) then markedSplitTerm P g p c (g-j) s Y else 0) (p-c+1)]
  apply Finset.sum_congr rfl
  intro s hs
  have hs0 := Finset.mem_range.mp hs
  have hsQ : s ≤ p-c := by omega
  have hcP : c ≤ p := by rcases hc with rfl|rfl <;> omega
  have h1 : (p-c)-s+c=p-s := by omega
  have h2 : p-((p-c)-s)=s+c := by omega
  have h3 : g-(g-j)=j := by omega
  have h4 : (p-c)-((p-c)-s)=s := by omega
  simp only [Nat.add_sub_cancel,h3,h4]
  by_cases H : L ≤ 2*j+s ∧ L ≤ 2*(g-j)+(p-c-s)
  · simp only [if_pos H,if_pos (And.symm H)]
    unfold markedSplitTerm
    rw [h1,h2,h3,Nat.choose_symm hsQ]
    ring
  · simp only [if_neg H,if_neg (show ¬(L ≤ 2*(g-j)+(p-c-s) ∧ L ≤ 2*j+s) by tauto)]

lemma markedSplitLossTail_half_bound (P : PsiTheory) (g p c N L : ℕ) (hg : 2 ≤ g)
    (hp : 2 ≤ p) (hc : c=1 ∨ c=2) (hN : 2 ≤ N) (Y : ℝ) (hY : Y ∈ Icc 0 y₀) :
    markedSplitLossTail P g p c L Y ≤ 2*(markedSplitLossTailGenus P g p c L 0 Y+
      (∑ j ∈ Finset.range (g/N+1), if 1 ≤ j then markedSplitLossTailGenus P g p c L j Y else 0)+
      markedSplitMacroscopic P g p c N Y) := by
  have hb := Analysis.finite_symmetric_sum_le_twice_half g
    (fun j => markedSplitLossTailGenus P g p c L j Y)
    (fun j _ => markedSplitLossTailGenus_nonneg P g p c L j hg hp hc Y hY)
    (fun j hj => markedSplitLossTailGenus_symm P g p c L j hp hc hj Y)
  rw [Analysis.finite_half_cut_partition g N hN] at hb
  refine hb.trans (mul_le_mul_of_nonneg_left (add_le_add le_rfl ?_) (by norm_num))
  unfold markedSplitMacroscopic
  apply Finset.sum_le_sum
  intro j hj
  split_ifs
  · exact markedSplitLossTailGenus_le P g p c L j hg hp hc Y hY
  · exact le_rfl

lemma markedSplitLossTail_small_macro (P : PsiTheory) (g p c N L : ℕ) (hg : 2 ≤ g)
    (hp : 2 ≤ p) (hc : c=1 ∨ c=2) (hN : 2 ≤ N) (Y : ℝ) (hY : Y∈Icc (0:ℝ) y₀) :
    markedSplitLossTail P g p c L Y ≤
      2*(markedSplitSmallLossTail P g p c N L Y+markedSplitMacroscopic P g p c N Y) := by
  have he := markedSplitLossTail_half_bound P g p c N L hg hp hc hN Y hY
  have hz : (∑ j ∈ Finset.range (g/N+1), markedSplitLossTailGenus P g p c L j Y)=
      markedSplitLossTailGenus P g p c L 0 Y+
      ∑ j ∈ Finset.range (g/N+1),if 1≤j then markedSplitLossTailGenus P g p c L j Y else 0 := by
    rw [Finset.sum_range_succ',Finset.sum_range_succ']
    simp [add_comm]
  rw [←hz] at he
  apply he.trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply add_le_add _ le_rfl
  unfold markedSplitSmallLossTail
  rw [Finset.product_eq_sprod,Finset.sum_product]
  apply Finset.sum_le_sum
  intro j hj
  apply Finset.sum_le_sum
  intro s hs
  have hs0 := Finset.mem_range.mp hs
  by_cases h1 : L ≤ 2*j+s
  · by_cases h2 : L ≤ 2*(g-j)+(p-c-s)
    · simp only [h1,h2,and_self,ite_true]
      exact le_rfl
    · simp only [h1,h2,and_false,ite_false,ite_true]
      exact markedSplitTerm_nonneg P g p c j s hg hp hc (by omega) Y hY
  · simp only [h1,false_and,ite_false]
    exact le_rfl

end WP

namespace WP
lemma markedSplitLossTail_zero (P : PsiTheory) (g p c : ℕ) (Y : ℝ) :
    markedSplitLossTail P g p c 0 Y=markedSplitConvolution P g p c Y := by
  simp [markedSplitLossTail,markedSplitLossTailGenus,markedSplitConvolution,markedSplitGenus]
end WP
