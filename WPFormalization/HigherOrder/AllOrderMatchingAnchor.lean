import WPFormalization.HigherOrder.LogTruncationControl
import WPFormalization.HigherOrder.AllOrderCriticalAnchor
import WPFormalization.HigherOrder.AllOrderLogVariation
noncomputable section
namespace WP.HigherOrder
open Set PowerSeries
lemma allOrderCorrectedPrefactorLog_critical_anchor (P : PsiTheory) (p : ℕ) (hp : 1 ≤ p) :
    ∃ (C B c δ : ℝ) (G : ℕ), 0 < C ∧ 0 < B ∧ 0 < c ∧ 0 < δ ∧
      ∀ g ≥ G, ∀ L : ℕ, 1 ≤ L → ((L-1:ℕ):ℝ) ≤ c*(complexity g p:ℝ) →
      2*B*((L:ℝ)+1)^2 ≤ (complexity g p:ℝ) →
      ∀ Y ∈ Ico (0:ℝ) y₀, y₀-Y ≤ δ → y₀-Y ≤ 1/(complexity g p:ℝ)^(L+1) →
      |allOrderCorrectedPrefactorLog P g p L Y| ≤ C*B^L*(L.factorial:ℝ)^2/(complexity g p:ℝ)^L := by
  obtain ⟨Cu,δ,hCu,hδ,hanchor⟩ := prefactor_log_critical_uniform_anchor
  obtain ⟨Ca,Ba,hCa,hBa,hpoly⟩ := logarithmicMarkedTruncation_endpoint_variation P p hp
  obtain ⟨Ce,Be,ce,Ge,hCe,hBe,hce,hend⟩ := exactEndpoint_log_uniform_gevrey_error P p
  obtain ⟨Co,Bo,hCo,hBo,hcoef⟩ := endpointLogCoefficient_factorial_bound p
  let B : ℝ := max 1 (max Ba (max Be Bo))
  let C : ℝ := Cu+Ca+Ce+Co
  have hB1 : 1 ≤ B := le_max_left _ _
  have hB : 0 < B := lt_of_lt_of_le zero_lt_one hB1
  have hBaB : Ba ≤ B := (le_max_left _ _).trans (le_max_right _ _)
  have hBeB : Be ≤ B := (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hBoB : Bo ≤ B := (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  refine ⟨C,B,ce,δ,max Ge 2,by dsimp [C];positivity,hB,hce,hδ,?_⟩
  intro g hg L hL horder hwindow Y hY hsmall hstrip
  have hs : Stable g p := by unfold Stable;omega
  have hhN : 1 ≤ complexity g p := by unfold complexity;omega
  have hh1 : (1:ℝ) ≤ complexity g p := by exact_mod_cast hhN
  have hh : (0:ℝ) < complexity g p := by linarith
  let h : ℝ := complexity g p
  have hδ0 : 0 ≤ y₀-Y := sub_nonneg.mpr hY.2.le
  have hfac : (1:ℝ) ≤ L.factorial := by exact_mod_cast (Nat.factorial_pos L)
  have hunit : 1 ≤ B^L*(L.factorial:ℝ)^2 := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hB1) (by nlinarith)
  have hhn : h ≠ 0 := hh.ne'
  have hpow : h^L ≤ h^(L+1) := by
    simpa only [pow_succ] using (le_mul_of_one_le_right (pow_nonneg hh.le L) hh1)
  have hδhL : y₀-Y ≤ 1/h^L := hstrip.trans (one_div_le_one_div_of_le (pow_pos hh L) hpow)
  have hhδ : h*(y₀-Y) ≤ 1/h^L := by
    have ht := mul_le_mul_of_nonneg_left hstrip hh.le
    apply ht.trans_eq
    change h*(1/h^(L+1))=1/h^L
    rw [pow_succ]
    field_simp [hhn]
  have ha := hanchor P g p hp hs hhN Y hY hsmall
  have hwBa : 2*Ba*((L:ℝ)+1)^2 ≤ h := by
    apply le_trans _ hwindow
    gcongr
  have hpv := hpoly L h hh hwBa Y ⟨hY.1,hY.2.le⟩
  have he := hend g ((le_max_left _ _).trans hg) (L-1) horder
  have hprev : L-1+1=L := by omega
  rw [hprev] at he
  have hlcoef : |endpointLogCoefficient p L| ≤ Co*B^L*(L.factorial:ℝ)^2 := by
    apply (hcoef L).trans
    have ht := pow_le_pow_left₀ hBo.le hBoB L
    have hf : (L.factorial:ℝ) ≤ (L.factorial:ℝ)^2 := by nlinarith
    exact mul_le_mul (mul_le_mul_of_nonneg_left ht hCo.le) hf (by positivity) (by positivity)
  have hendpoint : |Real.log (exactEndpoint P g p)-∑ j ∈ Finset.range (L+1),endpointLogCoefficient p j/h^j| ≤
      (Ce+Co)*B^L*(L.factorial:ℝ)^2/h^L := by
    have he' : |Real.log (exactEndpoint P g p)-∑ j ∈ Finset.range L,endpointLogCoefficient p j/h^j| ≤
        Ce*B^L*(L.factorial:ℝ)^2/h^L := by
      apply he.trans
      apply div_le_div_of_nonneg_right _ (pow_nonneg hh.le L)
      have ht := pow_le_pow_left₀ hBe.le hBeB L
      exact mul_le_mul (mul_le_mul_of_nonneg_left ht hCe.le) (by nlinarith : (L.factorial:ℝ) ≤ (L.factorial:ℝ)^2) (by positivity) (by positivity)
    rw [Finset.sum_range_succ]
    calc _ ≤ |Real.log (exactEndpoint P g p)-∑ j ∈ Finset.range L,endpointLogCoefficient p j/h^j|+
        |endpointLogCoefficient p L/h^L| := by simpa only [sub_add_eq_sub_sub] using abs_sub _ _
         _ ≤ Ce*B^L*(L.factorial:ℝ)^2/h^L+Co*B^L*(L.factorial:ℝ)^2/h^L := by
           apply add_le_add he'
           rw [abs_div,abs_of_pos (pow_pos hh L)]
           exact div_le_div_of_nonneg_right hlcoef (pow_nonneg hh.le L)
         _ = _ := by ring
  have hu : |prefactorLogError P g p Y-Real.log (exactEndpoint P g p)| ≤ Cu/h^L := by
    apply ha.trans
    calc Cu*h*(y₀-Y)=Cu*(h*(y₀-Y)) := by ring
         _ ≤ Cu*(1/h^L) := mul_le_mul_of_nonneg_left hhδ hCu.le
         _ = _ := by ring
  have hv : |(∑ j ∈ Finset.range (L+1),logarithmicMarkedCoefficient P p j Y/h^j)-
      ∑ j ∈ Finset.range (L+1),endpointLogCoefficient p j/h^j| ≤ Ca/h^L :=
    hpv.trans (by simpa only [mul_one_div] using mul_le_mul_of_nonneg_left hδhL hCa.le)
  have hsplit : |allOrderCorrectedPrefactorLog P g p L Y| ≤
      |prefactorLogError P g p Y-Real.log (exactEndpoint P g p)|+
        |Real.log (exactEndpoint P g p)-∑ j ∈ Finset.range (L+1),endpointLogCoefficient p j/h^j|+
        |(∑ j ∈ Finset.range (L+1),logarithmicMarkedCoefficient P p j Y/h^j)-
          ∑ j ∈ Finset.range (L+1),endpointLogCoefficient p j/h^j| := by
    dsimp [allOrderCorrectedPrefactorLog,logarithmicMarkedTruncation]
    have heq : prefactorLogError P g p Y-∑ j ∈ Finset.range (L+1),logarithmicMarkedCoefficient P p j Y/h^j=
      (prefactorLogError P g p Y-Real.log (exactEndpoint P g p))+
      (Real.log (exactEndpoint P g p)-∑ j ∈ Finset.range (L+1),endpointLogCoefficient p j/h^j)-
      ((∑ j ∈ Finset.range (L+1),logarithmicMarkedCoefficient P p j Y/h^j)-
        ∑ j ∈ Finset.range (L+1),endpointLogCoefficient p j/h^j) := by ring
    rw [heq]
    exact (abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
  apply hsplit.trans ((add_le_add (add_le_add hu hendpoint) hv).trans _)
  have hu' := mul_le_mul_of_nonneg_left hunit hCu.le
  have hv' := mul_le_mul_of_nonneg_left hunit hCa.le
  have ht := div_le_div_of_nonneg_right (add_le_add (add_le_add hu' (le_refl ((Ce+Co)*B^L*(L.factorial:ℝ)^2))) hv') (pow_nonneg hh.le L)
  convert ht using 1 <;> dsimp [C,h] <;> ring
end WP.HigherOrder
