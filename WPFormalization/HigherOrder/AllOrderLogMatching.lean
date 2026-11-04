import WPFormalization.HigherOrder.AllOrderMatchingAnchor
import WPFormalization.Analysis.AllOrderIntegrationScale
noncomputable section
namespace WP.HigherOrder
open Set PowerSeries
lemma actual_marked_log_matching_gevrey_two (P : PsiTheory) (p : ℕ) (hp : 1 ≤ p) :
    ∃ (C B c : ℝ) (G : ℕ), 0 < C ∧ 0 < B ∧ 0 < c ∧
      ∀ g ≥ G, ∀ L : ℕ, 1 ≤ L →
      ((L+2:ℕ):ℝ) ≤ c*Real.sqrt (complexity g p:ℝ) →
      ∀ Y ∈ Ico (0:ℝ) y₀,
      |prefactorLogError P g p Y-logarithmicMarkedTruncation P p (L-1) (complexity g p:ℝ) Y| ≤
        C*B^L*(L.factorial:ℝ)^2/(complexity g p:ℝ)^L := by
  obtain ⟨Ca,Ba,ca,δa,Ga,hCa,hBa,hca,hδa,hanchor⟩ := allOrderCorrectedPrefactorLog_critical_anchor P p hp
  obtain ⟨Cv,Bv,cv,hCv,hBv,hcv,hvar⟩ := allOrderCorrectedPrefactorLog_variation P p hp
  obtain ⟨Cc,Bc,hCc,hBc,hcont,hderiv,hcoef,hlip⟩ := logarithmicMarkedCoefficient_real_gevrey_regularity P p hp
  obtain ⟨Mz,δz,hMz,hδz,hgap⟩ := Analysis.all_order_logZ_gap
  obtain ⟨H,hH1,hmatch⟩ := Analysis.all_order_log_scale_matching (min δa δz) (lt_min hδa hδz)
  obtain ⟨N,hN⟩ := exists_nat_gt H
  let c : ℝ := min cv (min ca (1/(2*Ba+1)))
  let B : ℝ := max Ba (max (32*Bv) Bc)
  let Vc : ℝ := 32*Cv*Bv^2*(Mz+3)
  let C : ℝ := Ca+Vc+Cc
  have hc : 0 < c := lt_min hcv (lt_min hca (by positivity))
  have hB : 0 < B := hBa.trans_le (le_max_left _ _)
  have hVc : 0 < Vc := by dsimp [Vc];positivity
  have hC : 0 < C := by dsimp [C];positivity
  have hcCv : c ≤ cv := min_le_left _ _
  have hcCa : c ≤ ca := (min_le_right _ _).trans (min_le_left _ _)
  have hcBa : c ≤ 1/(2*Ba+1) := (min_le_right _ _).trans (min_le_right _ _)
  have hc1 : c ≤ 1 := hcBa.trans (by apply (div_le_one (by positivity : 0 < 2*Ba+1)).2;linarith)
  have hcPow : 2*Ba*c^2 ≤ 1 := by
    have ht := (le_div_iff₀ (by positivity : 0 < 2*Ba+1)).mp hcBa
    have hsq : c^2 ≤ c := by nlinarith
    nlinarith
  have hBaB : Ba ≤ B := le_max_left _ _
  have hBvB : 32*Bv ≤ B := (le_max_left _ _).trans (le_max_right _ _)
  have hBcB : Bc ≤ B := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨C,B,c,max Ga (N+2),hC,hB,hc,?_⟩
  intro g hg L hL horder Y hY
  have hg2 : 2 ≤ g := by omega
  have hgN : N ≤ g := by omega
  have hs : Stable g p := by unfold Stable;omega
  have hgh : g ≤ complexity g p := by unfold complexity;omega
  let h : ℝ := complexity g p
  have hhN : 1 ≤ complexity g p := by omega
  have hh1 : 1 ≤ h := by dsimp [h];exact_mod_cast hhN
  have hh : 0 < h := by linarith
  have hHh : H ≤ h := hN.le.trans (by dsimp [h];exact_mod_cast (hgN.trans hgh))
  have hLc : (L:ℝ)+2 ≤ c*Real.sqrt h := by simpa only [Nat.cast_add,Nat.cast_ofNat] using horder
  have hLs : 0 ≤ (L:ℝ)+1 := by positivity
  have hwindow : 2*Ba*((L:ℝ)+1)^2 ≤ h := by
    have ht : (L:ℝ)+1 ≤ c*Real.sqrt h := by linarith
    have ht2 := pow_le_pow_left₀ hLs ht 2
    rw [mul_pow,Real.sq_sqrt hh.le] at ht2
    calc _ ≤ 2*Ba*(c^2*h) := mul_le_mul_of_nonneg_left ht2 (by positivity)
         _ ≤ 1*h := by nlinarith [mul_le_mul_of_nonneg_right hcPow hh.le]
         _ = h := one_mul h
  have hendorder : ((L-1:ℕ):ℝ) ≤ ca*h := by
    have hlt : ((L-1:ℕ):ℝ) ≤ (L:ℝ)+2 := by exact_mod_cast (show L-1 ≤ L+2 by omega)
    have hsqrt : Real.sqrt h ≤ h := Real.sqrt_le_self_iff.mpr (Or.inr hh1)
    calc _ ≤ (L:ℝ)+2 := hlt
         _ ≤ c*Real.sqrt h := hLc
         _ ≤ ca*h := mul_le_mul hcCa hsqrt (Real.sqrt_nonneg _) hca.le
  let V : ℝ := y₀-1/h^(L+1)
  have hmatchV := hmatch h hHh L hL
  have hV : V ∈ Ico (0:ℝ) y₀ := hmatchV.1
  have hVsmall : y₀-V ≤ min δa δz := hmatchV.2
  have hVdel : y₀-V=1/h^(L+1) := by dsimp [V];ring
  have hVa := hanchor g ((le_max_left _ _).trans hg) L hL hendorder hwindow V hV
    (hVsmall.trans (min_le_left _ _)) (by rw [hVdel])
  have hEL : |allOrderCorrectedPrefactorLog P g p L Y| ≤ (Ca+Vc)*B^L*(L.factorial:ℝ)^2/h^L := by
    have hmajor (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hbB : b ≤ B) :
        a*b^L*(L.factorial:ℝ)^2/h^L ≤ a*B^L*(L.factorial:ℝ)^2/h^L := by gcongr
    by_cases hYV : Y ≤ V
    · have hvarY := hvar g hs hhN L (by exact horder.trans (mul_le_mul_of_nonneg_right hcCv (Real.sqrt_nonneg _))) Y hY V hV hYV
      have hgapY := hgap h hh L V hV (hVsmall.trans (min_le_right _ _)) rfl Y hY
      have hvarBound : |allOrderCorrectedPrefactorLog P g p L Y-allOrderCorrectedPrefactorLog P g p L V| ≤
          Vc*(32*Bv)^L*(L.factorial:ℝ)^2/h^L := by
        apply hvarY.trans
        apply (mul_le_mul_of_nonneg_left hgapY (by positivity : 0 ≤ Cv*Bv^(L+2)*((L+2).factorial:ℝ)^2/h^(L+1))).trans
        exact Analysis.all_order_transport_log_scale_absorption Cv Bv Mz h hCv.le hBv.le hMz.le hh1 L
      have hsplit : |allOrderCorrectedPrefactorLog P g p L Y| ≤
          |allOrderCorrectedPrefactorLog P g p L Y-allOrderCorrectedPrefactorLog P g p L V|+
            |allOrderCorrectedPrefactorLog P g p L V| := by
        simpa only [sub_add_cancel] using abs_add_le (allOrderCorrectedPrefactorLog P g p L Y-allOrderCorrectedPrefactorLog P g p L V) (allOrderCorrectedPrefactorLog P g p L V)
      apply (hsplit.trans (add_le_add (hvarBound.trans (hmajor Vc (32*Bv) hVc.le (by positivity) hBvB))
        (hVa.trans (hmajor Ca Ba hCa.le hBa.le hBaB)))).trans_eq
      ring
    · have hδY : y₀-Y ≤ y₀-V := by linarith
      have hYa := hanchor g ((le_max_left _ _).trans hg) L hL hendorder hwindow Y hY
        (hδY.trans (hVsmall.trans (min_le_left _ _))) (hδY.trans_eq hVdel)
      apply (hYa.trans (hmajor Ca Ba hCa.le hBa.le hBaB)).trans
      gcongr
      linarith
  have hlcoef : |logarithmicMarkedCoefficient P p L Y/h^L| ≤ Cc*B^L*(L.factorial:ℝ)^2/h^L := by
    rw [abs_div,abs_of_pos (pow_pos hh L)]
    apply (div_le_div_of_nonneg_right (hcoef L Y ⟨hY.1,hY.2.le⟩) (pow_nonneg hh.le L)).trans
    gcongr
  have hprev : L-1+1=L := by omega
  have hid : prefactorLogError P g p Y-logarithmicMarkedTruncation P p (L-1) h Y=
      allOrderCorrectedPrefactorLog P g p L Y+logarithmicMarkedCoefficient P p L Y/h^L := by
    dsimp [allOrderCorrectedPrefactorLog,logarithmicMarkedTruncation]
    rw [hprev,Finset.sum_range_succ]
    dsimp [h]
    ring
  rw [hid]
  apply ((abs_add_le _ _).trans (add_le_add hEL hlcoef)).trans_eq
  dsimp [C]
  ring
end WP.HigherOrder
namespace WP.HigherOrder
open Set
lemma actual_marked_log_uniform_gevrey_two (P : PsiTheory) (p : ℕ) (hp : 1 ≤ p) :
    ∃ C B c h₀ : ℝ, 0 < C ∧ 0 < B ∧ 0 < c ∧ 0 < h₀ ∧
      ∀ (g K : ℕ), h₀ ≤ (complexity g p:ℝ) →
      (K:ℝ) ≤ c*Real.sqrt (complexity g p:ℝ) → ∀ Y ∈ Ico (0:ℝ) y₀,
      |prefactorLogError P g p Y-
        ∑ j ∈ Finset.range (K+1), logarithmicMarkedCoefficient P p j Y/(complexity g p:ℝ)^j| ≤
        C*B^(K+1)*((K+1).factorial:ℝ)^2/(complexity g p:ℝ)^(K+1) := by
  obtain ⟨C,B,c,G,hC,hB,hc,hmain⟩ := actual_marked_log_matching_gevrey_two P p hp
  let H : ℝ := max ((2*G+p+2:ℕ):ℝ) (36/c^2+1)
  have hH : 0 < H := by dsimp [H];apply lt_of_lt_of_le _ (le_max_right _ _);positivity
  refine ⟨C,B,c/2,H,hC,hB,by positivity,hH,?_⟩
  intro g K hg hK Y hY
  have hnat : 2*G+p+2 ≤ complexity g p := by exact_mod_cast ((le_max_left _ _).trans hg : ((2*G+p+2:ℕ):ℝ) ≤ (complexity g p:ℝ))
  have hgG : G ≤ g := by unfold complexity at hnat;omega
  have hh : (0:ℝ) < complexity g p := hH.trans_le hg
  have hlarge : 36/c^2 ≤ (complexity g p:ℝ) := by
    have ht : 36/c^2+1 ≤ (complexity g p:ℝ) := (le_max_right _ _).trans hg
    linarith
  have hsq : 36 ≤ c^2*(complexity g p:ℝ) := by
    have ht := (div_le_iff₀ (sq_pos_of_pos hc)).mp hlarge
    nlinarith
  have hs : 3 ≤ c/2*Real.sqrt (complexity g p:ℝ) := by
    have hroot := Real.sq_sqrt hh.le
    have hn := Real.sqrt_nonneg (complexity g p:ℝ)
    nlinarith [mul_nonneg hc.le hn]
  have horder : ((K+1+2:ℕ):ℝ) ≤ c*Real.sqrt (complexity g p:ℝ) := by
    push_cast
    nlinarith
  have he := hmain g hgG (K+1) (by omega) horder Y hY
  simpa only [Nat.add_sub_cancel,logarithmicMarkedTruncation] using he
end WP.HigherOrder
