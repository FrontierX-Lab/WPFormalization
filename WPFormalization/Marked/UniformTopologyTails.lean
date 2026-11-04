import WPFormalization.Marked.TopologyTailDefinitions

/-! The complete uniform topological tail estimate of Appendix C, Lemma C.5. Constants precede all genera, marking counts, loss orders, and physical parameters. Both stability minima and the one-marking S tail are retained. No paper-specific tail or comparison estimate is assumed. -/
noncomputable section
namespace WP
open Set
lemma uniform_topology_tail_two_markings (P : PsiTheory) (M : ℝ) (hM : 0 < M)
    (c : ℕ) (hc : c=1 ∨ c=2) :
    ∃ C B : ℝ, 0 < C ∧ 0 < B ∧ ∃ H : ℕ, ∀ g p : ℕ,
      2 ≤ p → H ≤ complexity g p → (p:ℝ) ≤ M*Real.sqrt (complexity g p:ℝ) →
      ∀ L : ℕ, 1 ≤ L → (L:ℝ) ≤ Real.sqrt (complexity g p:ℝ) → ∀Y∈Icc (0:ℝ) y₀,
      markedSplitLossTail P g p c L Y ≤ C*(B*((p:ℝ)+L)/(complexity g p:ℝ))^L := by
  obtain ⟨D,hD,hsmall⟩ := markedSplitSmallLossTail_cut_bound P
  obtain ⟨N,Gs,hN,hcut⟩ := small_loss_sqrt_marking_cutoff D M hD hM
  obtain ⟨Cm,α,hCm,hα,Gm,hmacro⟩ := markedSplitMacroscopic_exponential_growing P M hM c N hc hN
  obtain ⟨Ha,hHa,hexp⟩ := Analysis.macroscopic_exponential_le_uniform_loss_scale α hα
  obtain ⟨J,hJ⟩ := exists_nat_ge Ha
  obtain ⟨H,hH⟩ := exists_nat_ge (max (4*M^2+1) (4*((Gs+Gm+J+2:ℕ):ℝ)))
  let B : ℝ := max 1 (4*D)
  have hB : 0 < B := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  refine ⟨4+2*Cm,B,by positivity,hB,H,?_⟩
  intro g p hp hlarge hpM L hL hLroot Y hY
  have hHh : (H:ℝ) ≤ complexity g p := by exact_mod_cast hlarge
  have hhM : 4*M^2+1 ≤ (complexity g p:ℝ) := (le_max_left _ _).trans (hH.trans hHh)
  have hhG : 4*((Gs+Gm+J+2:ℕ):ℝ) ≤ complexity g p := (le_max_right _ _).trans (hH.trans hHh)
  have hh0 : (0:ℝ) < complexity g p := by nlinarith only [hhM,sq_nonneg M]
  have hs : Stable g p := by
    have he : 0 < complexity g p := by exact_mod_cast hh0
    unfold complexity Stable at *
    omega
  have hcomp := complexity_le_four_genus_growing g p hs M hM hpM hhM
  have hgAll : Gs+Gm+J+2 ≤ g := by
    have he : (Gs+Gm+J+2:ℕ) ≤ g := by exact_mod_cast (show ((Gs+Gm+J+2:ℕ):ℝ) ≤ g by linarith only [hhG,hcomp])
    exact he
  have hg2 : 2 ≤ g := by omega
  have hgR : 0 < (g:ℝ) := by exact_mod_cast (show 0 < g by omega)
  have hhg : g ≤ complexity g p := by unfold complexity;omega
  have hhHa : Ha ≤ (complexity g p:ℝ) := hJ.trans (by exact_mod_cast (show J ≤ complexity g p by omega))
  have hsbound := hsmall g p c N L hg2 hp hc hN hL (hcut g (by omega) p hp hpM c) Y hY
  have hmbound := hmacro g (by omega) p hp hpM Y hY
  have hexpbound := hexp (complexity g p) hhHa p (by exact_mod_cast (show 1 ≤ p by omega)) L hLroot
  have hbase : D*((p:ℝ)+L)/(g:ℝ) ≤ B*((p:ℝ)+L)/(complexity g p:ℝ) := by
    apply (div_le_div_iff₀ hgR hh0).mpr
    have he := mul_le_mul_of_nonneg_left hcomp (show 0 ≤ D*((p:ℝ)+L) by positivity)
    have hf := mul_le_mul_of_nonneg_right (le_max_right 1 (4*D))
      (show 0 ≤ ((p:ℝ)+L)*(g:ℝ) by positivity)
    nlinarith only [he,hf]
  have hbase' : ((p:ℝ)+L)/(complexity g p:ℝ) ≤ B*((p:ℝ)+L)/(complexity g p:ℝ) := by
    apply div_le_div_of_nonneg_right _ hh0.le
    have he := mul_le_mul_of_nonneg_right (le_max_left 1 (4*D)) (show (0:ℝ) ≤ (p:ℝ)+L by positivity)
    simpa only [one_mul] using he
  have ha := pow_le_pow_left₀ (show 0 ≤ D*((p:ℝ)+L)/(g:ℝ) by positivity) hbase L
  have hb := pow_le_pow_left₀ (show 0 ≤ ((p:ℝ)+L)/(complexity g p:ℝ) by positivity) hbase' L
  have he := markedSplitLossTail_small_macro P g p c N L hg2 hp hc hN Y hY
  have hm := mul_le_mul_of_nonneg_left (hexpbound.trans hb) hCm.le
  nlinarith only [he,hsbound,hmbound,ha,hm]
lemma markedSplitLossTail_one_transfer (P : PsiTheory) :
    ∃ K : ℝ, 0 < K ∧ ∃ G : ℕ, ∀g≥G,∀L:ℕ,∀Y∈Icc (0:ℝ) y₀,
      markedSplitLossTail P g 1 1 L Y ≤ K*markedSplitLossTail P g 2 2 L Y := by
  obtain ⟨Cr,hCr,hcusp⟩ := W_cusp_uniform_bound
  obtain ⟨Ci,hCi,Gi,hInv⟩ := W_one_cusp_inverse_uniform P
  refine ⟨2*Cr^2*Ci,by positivity,Gi+2,?_⟩
  intro g hg L Y hY
  have hg2 : 2 ≤ g := by omega
  have hgp : (0:ℝ)<g := by exact_mod_cast (show 0<g by omega)
  have hW1 : 0<W P g 1 Y := W_pos P g 1 (by omega) (by unfold Stable;omega) Y hY
  have hW2 : 0<W P g 2 Y := W_pos P g 2 (by omega) (by unfold Stable;omega) Y hY
  let mask (j : ℕ) : Prop := L ≤ 2*j ∧ L ≤ 2*(g-j)
  let A₁ : ℝ := ∑ j ∈ Finset.range (g+1), if mask j then W P j 1 Y*W P (g-j) 1 Y else 0
  let A₂ : ℝ := ∑ j ∈ Finset.range (g+1), if mask j then W P j 2 Y*W P (g-j) 2 Y else 0
  have hs : markedSplitLossTail P g 1 1 L Y=A₁/W P g 1 Y := by
    simp only [markedSplitLossTail,markedSplitLossTailGenus,markedSplitTerm,
      Nat.reduceSub,Nat.zero_add,Nat.sub_zero,Nat.add_zero,Finset.sum_range_one,
      Nat.choose_zero_right,Nat.cast_one,one_mul]
    dsimp [A₁,mask]
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j hj
    split_ifs <;> simp
  have ht : markedSplitLossTail P g 2 2 L Y=A₂/W P g 2 Y := by
    simp only [markedSplitLossTail,markedSplitLossTailGenus,markedSplitTerm,
      Nat.reduceSub,Nat.zero_add,Nat.sub_zero,Nat.add_zero,Finset.sum_range_one,
      Nat.choose_zero_right,Nat.cast_one,one_mul]
    dsimp [A₂,mask]
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j hj
    split_ifs <;> simp
  have hT0 : 0 ≤ markedSplitLossTail P g 2 2 L Y := Finset.sum_nonneg
    (fun j _=>markedSplitLossTailGenus_nonneg P g 2 2 L j hg2 (by omega) (Or.inr rfl) Y hY)
  have hb : A₂ ≤ markedSplitLossTail P g 2 2 L Y*(Ci*(g:ℝ)*W P g 1 Y) := by
    calc
      _ = markedSplitLossTail P g 2 2 L Y*W P g 2 Y := by rw [ht];field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left (hInv g (by omega) Y hY) hT0
  have hsum : (g:ℝ)*A₁ ≤ (2*Cr^2)*A₂ := by
    dsimp [A₁,A₂]
    rw [Finset.mul_sum,Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j hj
    by_cases hm : mask j
    · simp only [if_pos hm]
      exact separatingS_one_term_bound Cr hCr.le hcusp P g j hg2
        (by have he:=Finset.mem_range.mp hj;omega) Y hY
    · simp only [if_neg hm,mul_zero]
      exact le_rfl
  rw [hs]
  apply (div_le_iff₀ hW1).mpr
  apply (mul_le_mul_iff_right₀ hgp).mp
  calc
    (g:ℝ)*A₁ ≤ (2*Cr^2)*A₂ := hsum
    _ ≤ (2*Cr^2)*(markedSplitLossTail P g 2 2 L Y*(Ci*(g:ℝ)*W P g 1 Y)) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ = _ := by ring

lemma uniform_topology_tail_one_marking (P : PsiTheory) :
    ∃ C B : ℝ, 0 < C ∧ 0 < B ∧ ∃ H : ℕ,∀g:ℕ,
      H ≤ complexity g 1 → ∀L:ℕ,1 ≤ L → (L:ℝ) ≤ Real.sqrt (complexity g 1:ℝ) →
      ∀Y∈Icc (0:ℝ) y₀,
      markedSplitLossTail P g 1 1 L Y ≤ C*(B*(1+(L:ℝ))/(complexity g 1:ℝ))^L := by
  obtain ⟨K,hK,G,htransfer⟩ := markedSplitLossTail_one_transfer P
  obtain ⟨C,B,hC,hB,H,htail⟩ := uniform_topology_tail_two_markings P 2 (by norm_num) 2 (Or.inr rfl)
  refine ⟨K*C,2*B,by positivity,by positivity,max H (2*(G+2)+1),?_⟩
  intro g hg L hL hLroot Y hY
  have hgG : G ≤ g := by
    have he := (le_max_right H (2*(G+2)+1)).trans hg
    unfold complexity at he
    omega
  have hg2 : 2 ≤ g := by
    have he := (le_max_right H (2*(G+2)+1)).trans hg
    unfold complexity at he
    omega
  have hcomp : complexity g 1 ≤ complexity g 2 := by unfold complexity;omega
  have hh1 : 0 < (complexity g 1:ℝ) := by exact_mod_cast (show 0<complexity g 1 by unfold complexity;omega)
  have hh2 : 0 < (complexity g 2:ℝ) := by exact_mod_cast (show 0<complexity g 2 by omega)
  have hroot : 1 ≤ Real.sqrt (complexity g 2:ℝ) := Real.one_le_sqrt.mpr (by exact_mod_cast (show 1 ≤ complexity g 2 by omega))
  have hp : (2:ℝ) ≤ 2*Real.sqrt (complexity g 2:ℝ) := by linarith
  have hLs : (L:ℝ) ≤ Real.sqrt (complexity g 2:ℝ) := hLroot.trans (Real.sqrt_le_sqrt (by exact_mod_cast hcomp))
  have ht := htail g 2 (by omega) (((le_max_left H (2*(G+2)+1)).trans hg).trans hcomp) hp L hL hLs Y hY
  have hbase : B*((2:ℝ)+L)/(complexity g 2:ℝ) ≤ (2*B)*(1+(L:ℝ))/(complexity g 1:ℝ) := by
    calc
      _ ≤ B*((2:ℝ)+L)/(complexity g 1:ℝ) := div_le_div_of_nonneg_left (by positivity) hh1 (by exact_mod_cast hcomp)
      _ ≤ _ := div_le_div_of_nonneg_right (by nlinarith [show (0:ℝ) ≤ L from Nat.cast_nonneg L]) hh1.le
  have he := pow_le_pow_left₀ (show 0 ≤ B*((2:ℝ)+L)/(complexity g 2:ℝ) by positivity) hbase L
  calc
    _ ≤ K*markedSplitLossTail P g 2 2 L Y := htransfer g hgG L Y hY
    _ ≤ K*(C*(B*((2:ℝ)+L)/(complexity g 2:ℝ))^L) := mul_le_mul_of_nonneg_left ht hK.le
    _ ≤ K*(C*((2*B)*(1+(L:ℝ))/(complexity g 1:ℝ))^L) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left he hC.le) hK.le
    _ = _ := by ring
lemma uniform_topology_tails_proof (P : PsiTheory) (M : ℝ) (hM : 0 < M) :
    ∃ C B : ℝ, 0 < C ∧ 0 < B ∧ ∃ H : ℕ,
      (∀g p:ℕ,1 ≤ p → H ≤ complexity g p → (p:ℝ) ≤ M*Real.sqrt (complexity g p:ℝ) →
        ∀L:ℕ,2 ≤ L → (L:ℝ) ≤ Real.sqrt (complexity g p:ℝ) → ∀Y∈Icc (0:ℝ) y₀,
        markedSplitLossTail P g p 1 L Y ≤ C*(B*((p:ℝ)+L)/(complexity g p:ℝ))^L) ∧
      (∀g p:ℕ,2 ≤ p → H ≤ complexity g p → (p:ℝ) ≤ M*Real.sqrt (complexity g p:ℝ) →
        ∀L:ℕ,1 ≤ L → (L:ℝ) ≤ Real.sqrt (complexity g p:ℝ) → ∀Y∈Icc (0:ℝ) y₀,
        markedSplitLossTail P g p 2 L Y ≤ C*(B*((p:ℝ)+L)/(complexity g p:ℝ))^L) := by
  obtain ⟨Cs,Bs,hCs,hBs,Hs,hS⟩ := uniform_topology_tail_two_markings P M hM 1 (Or.inl rfl)
  obtain ⟨Ct,Bt,hCt,hBt,Ht,hT⟩ := uniform_topology_tail_two_markings P M hM 2 (Or.inr rfl)
  obtain ⟨Co,Bo,hCo,hBo,Ho,hO⟩ := uniform_topology_tail_one_marking P
  let C : ℝ := Cs+Ct+Co
  let B : ℝ := Bs+Bt+Bo
  have hC : 0 < C := by dsimp [C];positivity
  have hB : 0 < B := by dsimp [B];positivity
  refine ⟨C,B,hC,hB,Hs+Ht+Ho+1,?_,?_⟩
  · intro g p hp hH hpM L hL hLroot Y hY
    by_cases hp1 : p=1
    · subst p
      have he := hO g (by omega) L (by omega) hLroot Y hY
      apply he.trans
      norm_num only [Nat.cast_one]
      change Co*(Bo*(1+(L:ℝ))/(complexity g 1:ℝ))^L ≤ C*(B*(1+(L:ℝ))/(complexity g 1:ℝ))^L
      apply Analysis.loss_scale_bound_mono Co C Bo B _ _ L hCo.le _ hBo.le _ (by positivity) (by positivity)
      · dsimp [C];linarith
      · dsimp [B];linarith
    · have he := hS g p (by omega) (by omega) hpM L (by omega) hLroot Y hY
      apply he.trans
      apply Analysis.loss_scale_bound_mono Cs C Bs B _ _ L hCs.le _ hBs.le _ (by positivity) (by positivity)
      · dsimp [C];linarith
      · dsimp [B];linarith
  · intro g p hp hH hpM L hL hLroot Y hY
    have he := hT g p hp (by omega) hpM L hL hLroot Y hY
    apply he.trans
    apply Analysis.loss_scale_bound_mono Ct C Bt B _ _ L hCt.le _ hBt.le _ (by positivity) (by positivity)
    · dsimp [C];linarith
    · dsimp [B];linarith
end WP
