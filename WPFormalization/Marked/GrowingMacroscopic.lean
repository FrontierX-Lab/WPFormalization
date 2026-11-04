import WPFormalization.Marked.GrowingMarkingsGrowth
import WPFormalization.Marked.MacroscopicSeparating

/-! Actual macroscopic separating sums have exponentially small total mass uniformly for p <= M sqrt(h). The genus and subset counts are included. -/
noncomputable section
namespace WP
open Set
lemma marked_split_macroscopic_decay_growing (P : PsiTheory) (M : ℝ) (hM : 0 < M)
    (c N : ℕ) (hc : c=1 ∨ c=2) (hN : 2 ≤ N) :
    ∃ C α : ℝ, 0 < C ∧ 0 < α ∧ ∃ G : ℕ,
      ∀ g ≥ G, ∀ p : ℕ, 2 ≤ p → (p:ℝ) ≤ M*Real.sqrt (complexity g p:ℝ) →
      ∀ j : ℕ, g/N < j → 2*j ≤ g →
      ∀ s ∈ Finset.range (p-c+1), ∀ Y ∈ Icc (0:ℝ) y₀,
        W P j (s+c) Y*W P (g-j) (p-s) Y/W P g p Y ≤ C*Real.exp (-α*(g:ℝ)) := by
  have hNpos : 0 < N := by omega
  have hNr : (2:ℝ) ≤ N := by exact_mod_cast hN
  let α : ℝ := Real.log 2/(4*(N:ℝ))
  have hα : 0 < α := by dsimp [α];exact div_pos (Real.log_pos (by norm_num)) (by positivity)
  let M' : ℝ := (M+2)*(4*N)
  have hM' : 0 < M' := by dsimp [M'];positivity
  have hMM' : M ≤ M' := by dsimp [M'];nlinarith only [hM,hNr]
  obtain ⟨B,hB,hA⟩ := A_log_uniform_upper
  obtain ⟨H,hgrowth⟩ := W_growing_markings_log_small P M' hM' α hα
  obtain ⟨J,hJ⟩ := exists_nat_ge (4*M^2+1)
  refine ⟨Real.exp B,α,Real.exp_pos _,hα,N*(H+2)+2*H+4+J,?_⟩
  intro g hg p hp hpM j hj hjhalf s hs Y hY
  have hg4 : 4 ≤ g := by nlinarith
  have hcut : H+2 ≤ g/N := (Nat.le_div_iff_mul_le hNpos).2 (by nlinarith)
  have hjH : H ≤ j := by omega
  have hj2 : 2 ≤ j := by omega
  have hlargeH : H ≤ g-j := by omega
  have hgH : H ≤ g := by omega
  have hs0 := Finset.mem_range.mp hs
  have hsp : s < p := by rcases hc with rfl|rfl <;> omega
  have hq₁ : 1 ≤ s+c := by rcases hc with rfl|rfl <;> omega
  have hq₂ : 1 ≤ p-s := by omega
  have hst : Stable g p := by unfold Stable;omega
  have hhg : g ≤ complexity g p := by unfold complexity;omega
  have hhg₁ : j ≤ complexity j (s+c) := by unfold complexity;omega
  have hhg₂ : g-j ≤ complexity (g-j) (p-s) := by unfold complexity;omega
  have hcomp : (complexity g p:ℝ) ≤ 4*(g:ℝ) :=
    complexity_le_four_genus_growing g p hst M hM hpM
      (hJ.trans (by exact_mod_cast (show J ≤ complexity g p by omega)))
  have hNj : (g:ℝ) ≤ (j:ℝ)*N := by
    exact_mod_cast ((Nat.div_lt_iff_lt_mul hNpos).mp hj).le
  have hscale₁ : (complexity g p:ℝ) ≤ (4*N)*(complexity j (s+c):ℝ) := by
    have hjc : (j:ℝ) ≤ complexity j (s+c) := by exact_mod_cast hhg₁
    have he := mul_le_mul_of_nonneg_left hjc (show 0 ≤ 4*(N:ℝ) by positivity)
    nlinarith only [hcomp,hNj,he]
  have hscale₂ : (complexity g p:ℝ) ≤ (4*N)*(complexity (g-j) (p-s):ℝ) := by
    have hgc : (g:ℝ) ≤ 2*(complexity (g-j) (p-s):ℝ) := by
      exact_mod_cast (show g ≤ 2*complexity (g-j) (p-s) by omega)
    have hc0 : (0:ℝ) ≤ complexity (g-j) (p-s) := Nat.cast_nonneg _
    nlinarith only [hcomp,hgc,hNr,hc0]
  have hr₁ := Analysis.sqrt_scale_bound _ _ (4*(N:ℝ)) (by linarith) hscale₁
  have hr₂ := Analysis.sqrt_scale_bound _ _ (4*(N:ℝ)) (by linarith) hscale₂
  have hroot1 : 1 ≤ Real.sqrt (complexity g p:ℝ) := Real.one_le_sqrt.mpr (by exact_mod_cast (show 1 ≤ complexity g p by omega))
  have hpc₁ : ((s+c:ℕ):ℝ) ≤ M'*Real.sqrt (complexity j (s+c):ℝ) := by
    have hsR : ((s+c:ℕ):ℝ) ≤ (p:ℝ)+2 := by
      have he : s+c ≤ p+2 := by rcases hc with rfl|rfl <;>omega
      exact_mod_cast he
    have hm := mul_le_mul_of_nonneg_left hr₁ (show 0 ≤ M+2 by positivity)
    dsimp [M']
    nlinarith only [hsR,hpM,hroot1,hm]
  have hpc₂ : ((p-s:ℕ):ℝ) ≤ M'*Real.sqrt (complexity (g-j) (p-s):ℝ) := by
    have hsR : ((p-s:ℕ):ℝ) ≤ (p:ℝ) := by exact_mod_cast Nat.sub_le p s
    have hm := mul_le_mul_of_nonneg_left hr₂ (show 0 ≤ M+2 by positivity)
    dsimp [M']
    nlinarith only [hsR,hpM,hroot1,hm]
  have hpc : (p:ℝ) ≤ M'*Real.sqrt (complexity g p:ℝ) := hpM.trans
    (mul_le_mul_of_nonneg_right hMM' (Real.sqrt_nonneg _))
  have he₁ : |markedLogError P j (s+c) Y| ≤ α*(j:ℝ) :=
    hgrowth j (s+c) hq₁ (by unfold Stable;omega) (by omega) hpc₁ Y hY
  have he₂ : |markedLogError P (g-j) (p-s) Y| ≤ α*((g-j:ℕ):ℝ) :=
    hgrowth (g-j) (p-s) hq₂ (by unfold Stable;omega) (by omega) hpc₂ Y hY
  have he : |markedLogError P g p Y| ≤ α*(g:ℝ) := hgrowth g p (by omega) hst (by omega) hpc Y hY
  have hl := marked_split_log_ratio_upper P g p j s c hg4 hp hj2 hjhalf hsp hc Y hY B α hB (hA Y hY) he₁ he₂ he
  have hα4 : α*(4*(N:ℝ))=Real.log 2 := by dsimp [α];field_simp
  have hjDecay : 4*α*(g:ℝ) ≤ (j:ℝ)*Real.log 2 := by
    calc
      _ ≤ 4*α*((j:ℝ)*N) := mul_le_mul_of_nonneg_left hNj (by positivity)
      _ = _ := by rw [←hα4];ring
  have hl' : Real.log (W P j (s+c) Y*W P (g-j) (p-s) Y/W P g p Y) ≤ B-α*(g:ℝ) :=
    hl.trans (by nlinarith [show 0 ≤ α*(g:ℝ) by positivity])
  have hW₁ := W_pos P j (s+c) hq₁ (by unfold Stable;omega) Y hY
  have hW₂ := W_pos P (g-j) (p-s) hq₂ (by unfold Stable;omega) Y hY
  have hW := W_pos P g p (by omega) hst Y hY
  calc
    _ = Real.exp (Real.log (W P j (s+c) Y*W P (g-j) (p-s) Y/W P g p Y)) :=
      (Real.exp_log (div_pos (mul_pos hW₁ hW₂) hW)).symm
    _ ≤ Real.exp (B-α*(g:ℝ)) := Real.exp_le_exp.mpr hl'
    _ = _ := by rw [←Real.exp_add];congr 1;ring
lemma markedSplitMacroscopic_exponential_growing (P : PsiTheory) (M : ℝ) (hM : 0 < M)
    (c N : ℕ) (hc : c=1 ∨ c=2) (hN : 2 ≤ N) :
    ∃ C α : ℝ, 0 < C ∧ 0 < α ∧ ∃ G : ℕ,
      ∀ g ≥ G, ∀ p : ℕ, 2 ≤ p → (p:ℝ) ≤ M*Real.sqrt (complexity g p:ℝ) →
      ∀ Y ∈ Icc (0:ℝ) y₀,
        markedSplitMacroscopic P g p c N Y ≤ C*Real.exp (-α*(complexity g p:ℝ)) := by
  obtain ⟨C,α,hC,hα,G,hpoint⟩ := marked_split_macroscopic_decay_growing P M hM c N hc hN
  obtain ⟨H,hH,hcount⟩ := Analysis.sqrt_marking_count_exponential_absorption (4*M) α (by positivity) hα
  obtain ⟨J,hJ⟩ := exists_nat_ge (max H (4*M^2+1))
  refine ⟨C,α/8,hC,by positivity,G+J+4,?_⟩
  intro g hg p hp hpM Y hY
  have hgG : G ≤ g := by omega
  have hg4 : 4 ≤ g := by omega
  have hgH : H ≤ (g:ℝ) := (le_max_left _ _).trans (hJ.trans (by exact_mod_cast (show J ≤ g by omega)))
  have hst : Stable g p := by unfold Stable;omega
  have hhg : g ≤ complexity g p := by unfold complexity;omega
  have hcomp : (complexity g p:ℝ) ≤ 4*(g:ℝ) :=
    complexity_le_four_genus_growing g p hst M hM hpM
      ((le_max_right _ _).trans (hJ.trans (by exact_mod_cast (show J ≤ complexity g p by omega))))
  have hr := Analysis.sqrt_scale_bound _ _ 4 (by norm_num) hcomp
  have hpc : (p:ℝ) ≤ (4*M)*Real.sqrt (g:ℝ) := by
    have he := mul_le_mul_of_nonneg_left hr hM.le
    nlinarith only [he,hpM]
  have hcnt := hcount g hgH p hpc
  have hchoose : (∑ s ∈ Finset.range (p-c+1), (Nat.choose (p-c) s:ℝ))=(2:ℝ)^(p-c) := by
    exact_mod_cast Nat.sum_range_choose (p-c)
  have hinner (j : ℕ) (hj : g/N < j ∧ 2*j ≤ g) :
      (∑ s ∈ Finset.range (p-c+1), markedSplitTerm P g p c j s Y) ≤
        (2:ℝ)^(p-c)*C*Real.exp (-α*(g:ℝ)) := by
    calc
      _ ≤ ∑ s ∈ Finset.range (p-c+1), (Nat.choose (p-c) s:ℝ)*(C*Real.exp (-α*(g:ℝ))) := by
        apply Finset.sum_le_sum
        intro s hs
        have hp' := hpoint g hgG p hp hpM j hj.1 hj.2 s hs Y hY
        simpa only [markedSplitTerm,mul_assoc,div_eq_mul_inv] using
          mul_le_mul_of_nonneg_left hp' (Nat.cast_nonneg (Nat.choose (p-c) s))
      _ = _ := by rw [←Finset.sum_mul,hchoose];ring
  have hmass : markedSplitMacroscopic P g p c N Y ≤
      (2:ℝ)^(p-c)*C*(((g:ℝ)+1)*Real.exp (-α*(g:ℝ))) := by
    calc
      _ ≤ ∑ j ∈ Finset.range (g+1), (2:ℝ)^(p-c)*C*Real.exp (-α*(g:ℝ)) := by
        unfold markedSplitMacroscopic
        apply Finset.sum_le_sum
        intro j hj
        by_cases hi : g/N < j ∧ 2*j ≤ g
        · simp only [if_pos hi]
          exact hinner j hi
        · simp only [if_neg hi]
          positivity
      _ = _ := by simp;ring
  calc
    _ ≤ (2:ℝ)^(p-c)*C*(((g:ℝ)+1)*Real.exp (-α*(g:ℝ))) := hmass
    _ ≤ (2:ℝ)^p*C*(((g:ℝ)+1)*Real.exp (-α*(g:ℝ))) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) (Nat.sub_le p c)) hC.le
    _ = C*(((g:ℝ)+1)*(2:ℝ)^p*Real.exp (-α*(g:ℝ))) := by ring
    _ ≤ C*Real.exp (-(α/2)*(g:ℝ)) := mul_le_mul_of_nonneg_left hcnt hC.le
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ hC.le
      apply Real.exp_le_exp.mpr
      have he := mul_le_mul_of_nonneg_left hcomp hα.le
      nlinarith only [he]
end WP
