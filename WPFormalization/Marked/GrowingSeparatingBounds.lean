import WPFormalization.Marked.UniformTopologyTails

/-! The true separating masses start at their stability losses. The uniform all-loss estimate gives the growing-marking S and T bounds used for first-order profiles. -/
noncomputable section
namespace WP
open Set
lemma markedSplitLossTail_stability_minimum (P : PsiTheory) (g p c : ℕ)
    (hc : c=1 ∨ c=2) (hcp : c ≤ p) (Y : ℝ) :
    markedSplitLossTail P g p c (3-c) Y = markedSplitConvolution P g p c Y := by
  unfold markedSplitLossTail markedSplitLossTailGenus markedSplitConvolution markedSplitGenus
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro s hs
  have hs0 := Finset.mem_range.mp hs
  by_cases h1 : 3-c ≤ 2*j+s
  · by_cases h2 : 3-c ≤ 2*(g-j)+(p-c-s)
    · rw [if_pos ⟨h1,h2⟩]
    · rw [if_neg (by tauto : ¬(3-c ≤ 2*j+s ∧ 3-c ≤ 2*(g-j)+(p-c-s)))]
      have hst : ¬Stable (g-j) (p-s) := by
        unfold Stable
        rcases hc with rfl|rfl <;>omega
      simp [markedSplitTerm,W_unstable P (g-j) (p-s) hst Y]
  · rw [if_neg (by tauto : ¬(3-c ≤ 2*j+s ∧ 3-c ≤ 2*(g-j)+(p-c-s)))]
    have hst : ¬Stable j (s+c) := by
      unfold Stable
      rcases hc with rfl|rfl <;>omega
    simp [markedSplitTerm,W_unstable P j (s+c) hst Y]

lemma separating_growing_markings_bounds (P : PsiTheory) (M : ℝ) (hM : 0 < M) :
    ∃ C : ℝ, 0 < C ∧ ∃ H : ℕ,
      (∀g p:ℕ,1 ≤ p → H ≤ complexity g p → (p:ℝ) ≤ M*Real.sqrt (complexity g p:ℝ) →
        ∀Y∈Icc (0:ℝ) y₀,separatingS P g p Y ≤ C*((p:ℝ)+2)^2/(complexity g p:ℝ)^2) ∧
      (∀g p:ℕ,2 ≤ p → H ≤ complexity g p → (p:ℝ) ≤ M*Real.sqrt (complexity g p:ℝ) →
        ∀Y∈Icc (0:ℝ) y₀,separatingT P g p Y ≤ C*((p:ℝ)+1)/(complexity g p:ℝ)) := by
  obtain ⟨C,B,hC,hB,H,hS,hT⟩ := uniform_topology_tails_proof P M hM
  let D : ℝ := C*(B^2+B+1)
  have hD : 0 < D := by dsimp [D];positivity
  have hC2 : C*B^2 ≤ D := by dsimp [D];nlinarith only [mul_nonneg hC.le (by linarith : 0 ≤ B+1)]
  have hC1 : C*B ≤ D := by dsimp [D];nlinarith only [mul_nonneg hC.le (show 0 ≤ B^2+1 by positivity)]
  refine ⟨D,hD,max H 4,?_,?_⟩
  · intro g p hp hH hpM Y hY
    have hh4 : (4:ℝ) ≤ complexity g p := by exact_mod_cast (le_max_right H 4).trans hH
    have hh0 : (0:ℝ) ≤ complexity g p := Nat.cast_nonneg _
    have hroot : (2:ℝ) ≤ Real.sqrt (complexity g p:ℝ) := by
      nlinarith only [hh4,Real.sqrt_nonneg (complexity g p:ℝ),Real.sq_sqrt hh0]
    have he := hS g p hp ((le_max_left H 4).trans hH) hpM 2 (by omega) hroot Y hY
    rw [markedSplitLossTail_stability_minimum P g p 1 (Or.inl rfl) (by omega) Y] at he
    rw [←separatingS_eq_markedSplitConvolution P g p hp Y] at he
    calc
      _ ≤ C*(B*((p:ℝ)+2)/(complexity g p:ℝ))^2 := he
      _ = (C*B^2)*(((p:ℝ)+2)^2/(complexity g p:ℝ)^2) := by rw [div_pow,mul_pow];ring
      _ ≤ D*(((p:ℝ)+2)^2/(complexity g p:ℝ)^2) := mul_le_mul_of_nonneg_right hC2 (by positivity)
      _ = _ := by ring
  · intro g p hp hH hpM Y hY
    have hh4 : (4:ℝ) ≤ complexity g p := by exact_mod_cast (le_max_right H 4).trans hH
    have hh0 : (0:ℝ) ≤ complexity g p := Nat.cast_nonneg _
    have hroot : (1:ℝ) ≤ Real.sqrt (complexity g p:ℝ) := Real.one_le_sqrt.mpr (by linarith)
    have he := hT g p hp ((le_max_left H 4).trans hH) hpM 1 (by omega) (by simpa only [Nat.cast_one] using hroot) Y hY
    simp only [Nat.cast_one] at he
    rw [markedSplitLossTail_stability_minimum P g p 2 (Or.inr rfl) (by omega) Y] at he
    rw [←separatingT_eq_markedSplitConvolution P g p hp Y] at he
    calc
      _ ≤ C*(B*((p:ℝ)+1)/(complexity g p:ℝ))^1 := he
      _ = (C*B)*(((p:ℝ)+1)/(complexity g p:ℝ)) := by ring
      _ ≤ D*(((p:ℝ)+1)/(complexity g p:ℝ)) := mul_le_mul_of_nonneg_right hC1 (by positivity)
      _ = _ := by ring
lemma separatingS_growing_markings_genus_bound (P : PsiTheory) (M : ℝ) (hM : 0 < M) :
    ∃ Cs : ℝ,0 < Cs ∧ ∃ G : ℕ,∀g≥G,∀p:ℕ,1 ≤ p →
      (p:ℝ) ≤ M*Real.sqrt (complexity g p:ℝ) → ∀Y∈Icc (0:ℝ) y₀,
      separatingS P g p Y ≤ Cs/(g:ℝ) := by
  obtain ⟨D,hD,H,hS,hT⟩ := separating_growing_markings_bounds P M hM
  let C : ℝ := D*(M+2)^2
  have hC : 0 < C := by dsimp [C];positivity
  refine ⟨C,hC,max H 2,?_⟩
  intro g hg p hp hpM Y hY
  have hg2 : 2 ≤ g := (le_max_right _ _).trans hg
  have hgp : (0:ℝ) < g := by exact_mod_cast (show 0<g by omega)
  have hhg : (g:ℝ) ≤ complexity g p := by exact_mod_cast (show g ≤ complexity g p by unfold complexity;omega)
  have hh : (0:ℝ) < complexity g p := hgp.trans_le hhg
  have hr : 1 ≤ Real.sqrt (complexity g p:ℝ) := Real.one_le_sqrt.mpr (by exact_mod_cast (show 1 ≤ complexity g p by unfold complexity;omega))
  have hp2 : (p:ℝ)+2 ≤ (M+2)*Real.sqrt (complexity g p:ℝ) := by nlinarith only [hpM,hr]
  have hsq : ((p:ℝ)+2)^2 ≤ (M+2)^2*(complexity g p:ℝ) := by
    have he := pow_le_pow_left₀ (show (0:ℝ) ≤ (p:ℝ)+2 by positivity) hp2 2
    rwa [mul_pow,Real.sq_sqrt hh.le] at he
  calc
    _ ≤ D*((p:ℝ)+2)^2/(complexity g p:ℝ)^2 := hS g p hp (by
      have he := (le_max_left H 2).trans hg
      have hgn : g ≤ complexity g p := by unfold complexity;omega
      omega) hpM Y hY
    _ ≤ D*((M+2)^2*(complexity g p:ℝ))/(complexity g p:ℝ)^2 :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hsq hD.le) (sq_nonneg _)
    _ = C/(complexity g p:ℝ) := by dsimp [C];field_simp
    _ ≤ C/(g:ℝ) := div_le_div_of_nonneg_left hC.le hgp hhg

end WP
