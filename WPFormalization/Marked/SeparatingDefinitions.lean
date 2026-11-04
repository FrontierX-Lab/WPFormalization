import WPFormalization.Marked.Positivity

/-! Actual finite estimates for the separating terms of Section 6. The
proofs use the original marked W functions and the already proved ratio
and growth bounds; no separating estimate is assumed. -/
noncomputable section
open Set
open scoped BigOperators
namespace WP

def markedSplitTerm (P : PsiTheory) (g p c j s : ℕ) (Y : ℝ) : ℝ :=
  (Nat.choose (p-c) s:ℝ)*W P j (s+c) Y*W P (g-j) (p-s) Y/W P g p Y

def markedSplitSmallPositive (P : PsiTheory) (g p c N : ℕ) (Y : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (g/N+1), if 1 ≤ j then
    ∑ s ∈ Finset.range (p-c+1), markedSplitTerm P g p c j s Y else 0

def markedSplitGenus (P : PsiTheory) (g p c j : ℕ) (Y : ℝ) : ℝ :=
  ∑ s ∈ Finset.range (p-c+1), markedSplitTerm P g p c j s Y

def markedSplitConvolution (P : PsiTheory) (g p c : ℕ) (Y : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (g+1), markedSplitGenus P g p c j Y

def markedSplitPositive (P : PsiTheory) (g p c : ℕ) (Y : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (g+1), if 1 ≤ j ∧ j < g then markedSplitGenus P g p c j Y else 0

def markedSplitMacroscopic (P : PsiTheory) (g p c N : ℕ) (Y : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (g+1), if g/N < j ∧ 2*j ≤ g then
    ∑ s ∈ Finset.range (p-c+1), markedSplitTerm P g p c j s Y else 0

def separatingTPositive (P : PsiTheory) (g p : ℕ) (Y : ℝ) : ℝ :=
  (∑ j ∈ Finset.range (g+1), if 1 ≤ j ∧ j < g then
    ∑ s ∈ Finset.range (p-1), (Nat.choose (p-2) s:ℝ)*W P j (s+2) Y*W P (g-j) (p-s) Y else 0) /
      W P g p Y

lemma markedSplitGenus_symm (P : PsiTheory) (g p c j : ℕ) (hp : 2 ≤ p)
    (hc : c=1 ∨ c=2) (hj : j ≤ g) (Y : ℝ) :
    markedSplitGenus P g p c (g-j) Y=markedSplitGenus P g p c j Y := by
  unfold markedSplitGenus
  rw [←Finset.sum_range_reflect (fun s => markedSplitTerm P g p c (g-j) s Y) (p-c+1)]
  apply Finset.sum_congr rfl
  intro s hs
  have hs0 := Finset.mem_range.mp hs
  have hsQ : s ≤ p-c := by omega
  have hcP : c ≤ p := by rcases hc with rfl|rfl <;> omega
  have h1 : (p-c)-s+c=p-s := by omega
  have h2 : p-((p-c)-s)=s+c := by omega
  have h3 : g-(g-j)=j := by omega
  simp only [Nat.add_sub_cancel]
  unfold markedSplitTerm
  rw [h1,h2,h3,Nat.choose_symm hsQ]
  ring

lemma markedSplitGenus_nonneg (P : PsiTheory) (g p c j : ℕ) (hg : 2 ≤ g) (hp : 2 ≤ p)
    (hc : c=1 ∨ c=2) (Y : ℝ) (hY : Y ∈ Icc 0 y₀) :
    0 ≤ markedSplitGenus P g p c j Y := by
  have hpW := W_pos P g p (by omega) (by unfold Stable;omega) Y hY
  apply Finset.sum_nonneg
  intro s hs
  have hs0 := Finset.mem_range.mp hs
  have hq₁ : 1 ≤ s+c := by rcases hc with rfl|rfl <;> omega
  have hq₂ : 1 ≤ p-s := by rcases hc with rfl|rfl <;> omega
  exact div_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg _)
    (W_nonneg P j (s+c) hq₁ Y hY)) (W_nonneg P (g-j) (p-s) hq₂ Y hY)) hpW.le

lemma markedSplitConvolution_nonneg (P : PsiTheory) (g p c : ℕ) (hg : 2 ≤ g)
    (hp : 2 ≤ p) (hc : c=1 ∨ c=2) (Y : ℝ) (hY : Y ∈ Icc 0 y₀) :
    0 ≤ markedSplitConvolution P g p c Y :=
  Finset.sum_nonneg (fun j _ => markedSplitGenus_nonneg P g p c j hg hp hc Y hY)

lemma markedSplitPositive_nonneg (P : PsiTheory) (g p c : ℕ) (hg : 2 ≤ g)
    (hp : 2 ≤ p) (hc : c=1 ∨ c=2) (Y : ℝ) (hY : Y ∈ Icc 0 y₀) :
    0 ≤ markedSplitPositive P g p c Y := by
  unfold markedSplitPositive
  apply Finset.sum_nonneg
  intro j hj
  split_ifs
  · exact markedSplitGenus_nonneg P g p c j hg hp hc Y hY
  · exact le_rfl

lemma separatingS_eq_markedSplitConvolution (P : PsiTheory) (g p : ℕ) (hp : 1 ≤ p) (Y : ℝ) :
    separatingS P g p Y = markedSplitConvolution P g p 1 Y := by
  unfold separatingS markedSplitConvolution markedSplitGenus markedSplitTerm
  rw [show p-1+1=p by omega]
  simp only [Finset.sum_div]

lemma separatingT_eq_markedSplitConvolution (P : PsiTheory) (g p : ℕ) (hp : 2 ≤ p) (Y : ℝ) :
    separatingT P g p Y = markedSplitConvolution P g p 2 Y := by
  unfold separatingT markedSplitConvolution markedSplitGenus markedSplitTerm
  rw [show p-2+1=p-1 by omega]
  simp only [Finset.sum_div]

lemma separatingTPositive_eq_markedSplitPositive (P : PsiTheory) (g p : ℕ)
    (hp : 2 ≤ p) (Y : ℝ) :
    separatingTPositive P g p Y = markedSplitPositive P g p 2 Y := by
  unfold separatingTPositive markedSplitPositive markedSplitGenus markedSplitTerm
  rw [show p-2+1=p-1 by omega,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hj' : 1 ≤ j ∧ j < g
  · simp only [if_pos hj',Finset.sum_div]
  · simp only [if_neg hj',zero_div]

end WP
