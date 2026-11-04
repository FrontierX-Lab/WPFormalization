import WPFormalization.HigherOrder.AllOrderTransportGevrey
import WPFormalization.HigherOrder.LogMarkedRegularity
noncomputable section
namespace WP.HigherOrder
open Set PowerSeries

def logarithmicMarkedTruncation (P : PsiTheory) (p K : ℕ) (h Y : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (K+1), logarithmicMarkedCoefficient P p j Y/h^j

def allOrderCorrectedPrefactorLog (P : PsiTheory) (g p K : ℕ) (Y : ℝ) : ℝ :=
  prefactorLogError P g p Y-logarithmicMarkedTruncation P p K (complexity g p:ℝ) Y

lemma logarithmicMarkedTruncation_continuousOn (P : PsiTheory) (p K : ℕ)
    (hp : 1 ≤ p) (h : ℝ) :
    ContinuousOn (logarithmicMarkedTruncation P p K h) (Icc (0:ℝ) y₀) := by
  obtain ⟨C,B,hC,hB,hcont,hrest⟩ := logarithmicMarkedCoefficient_real_gevrey_regularity P p hp
  exact continuousOn_finsetSum _ (fun j hj => (hcont j).div_const _)

lemma logarithmicMarkedTruncation_hasDerivAt (P : PsiTheory) (p K : ℕ)
    (hp : 1 ≤ p) (h Y : ℝ) (hY : Y ∈ Ioo (0:ℝ) y₀) :
    HasDerivAt (logarithmicMarkedTruncation P p K h)
      (transportTruncation P p K Y h/(A Y*r Y)) Y := by
  obtain ⟨C,B,hC,hB,hcont,hderiv,hrest⟩ := logarithmicMarkedCoefficient_real_gevrey_regularity P p hp
  have hsum : HasDerivAt (fun x => ∑ j ∈ Finset.range (K+1), logarithmicMarkedCoefficient P p j x/h^j)
      (∑ j ∈ Finset.range (K+1), (if j=0 then 0 else transportCoefficient P p j Y/(A Y*r Y))/h^j) Y := by
    apply HasDerivAt.fun_sum
    intro j hj
    by_cases hj0 : j=0
    · subst j
      simpa [logarithmicMarkedCoefficient] using (hasDerivAt_const Y (0:ℝ))
    · simpa only [ite_eq_right hj0] using (hderiv j (by omega) Y hY).div_const (h^j)
  convert hsum using 1
  · rfl
  unfold transportTruncation
  rw [Finset.sum_range_succ', Finset.sum_div]
  simp only [Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ite_false, ite_true, zero_div, add_zero]
  apply Finset.sum_congr rfl
  intro j hj
  ring

lemma allOrderCorrectedPrefactorLog_hasDerivAt (P : PsiTheory) (g p K : ℕ)
    (hp : 1 ≤ p) (hs : Stable g p) (Y : ℝ) (hY : Y ∈ Ioo (0:ℝ) y₀) :
    HasDerivAt (allOrderCorrectedPrefactorLog P g p K)
      (((A Y*r Y)*deriv (prefactorLogError P g p) Y-transportTruncation P p K Y (complexity g p:ℝ))/(A Y*r Y)) Y := by
  have he := (prefactorLogError_hasDerivAt_inverse_cusp P g p hp hs Y hY).sub
    (logarithmicMarkedTruncation_hasDerivAt P p K hp (complexity g p:ℝ) Y hY)
  have hAr : A Y*r Y ≠ 0 := (mul_pos (Analysis.marked_A_pos Y ⟨hY.1.le,hY.2.le⟩) (r_pos Y ⟨hY.1.le,hY.2⟩)).ne'
  convert he using 1
  · rfl
  · rw [(prefactorLogError_hasDerivAt_inverse_cusp P g p hp hs Y hY).deriv]
    have hA := (Analysis.marked_A_pos Y ⟨hY.1.le,hY.2.le⟩).ne'
    have hr := (r_pos Y ⟨hY.1.le,hY.2⟩).ne'
    field_simp [hA,hr]
    <;> ring

lemma allOrderCorrectedPrefactorLog_variation (P : PsiTheory) (p : ℕ) (hp : 1 ≤ p) :
    ∃ C B c : ℝ, 0 < C ∧ 0 < B ∧ 0 < c ∧
      ∀ g : ℕ, Stable g p → 1 ≤ complexity g p → ∀ L : ℕ,
      ((L+2:ℕ):ℝ) ≤ c*Real.sqrt (complexity g p:ℝ) →
      ∀ Y ∈ Ico (0:ℝ) y₀, ∀ V ∈ Ico (0:ℝ) y₀, Y ≤ V →
      |allOrderCorrectedPrefactorLog P g p L Y-allOrderCorrectedPrefactorLog P g p L V| ≤
        (C*B^(L+2)*((L+2).factorial:ℝ)^2/(complexity g p:ℝ)^(L+1))*(Real.log (Z Y)-Real.log (Z V)) := by
  obtain ⟨C,B,c,hC,hB,hc,htr⟩ := actual_log_transport_gevrey_two P p hp
  refine ⟨C,B,c,hC,hB,hc,?_⟩
  intro g hs hh L horder Y hY V hV hYV
  have hsub : Icc Y V ⊆ Ico (0:ℝ) y₀ := fun x hx => ⟨hY.1.trans hx.1,hx.2.trans_lt hV.2⟩
  have hmem (x : ℝ) (hx : x ∈ Ioo Y V) : x ∈ Ioo (0:ℝ) y₀ := ⟨hY.1.trans_lt hx.1,hx.2.trans hV.2⟩
  have hf : ContinuousOn (allOrderCorrectedPrefactorLog P g p L) (Icc Y V) :=
    ((prefactorLogError_continuousOn_parameter P g p hp hs).sub
      ((logarithmicMarkedTruncation_continuousOn P p L hp _).mono Ico_subset_Icc_self)).mono hsub
  rw [abs_sub_comm]
  apply Analysis.log_scale_variation_bound (allOrderCorrectedPrefactorLog P g p L) (fun x => Real.log (Z x))
    Y V _ hYV hf (Analysis.logZ_continuousOn_parameter.mono hsub)
  · intro x hx
    exact (allOrderCorrectedPrefactorLog_hasDerivAt P g p L hp hs x (hmem x hx)).differentiableAt
  · intro x hx
    exact (Analysis.logZ_hasDerivAt_open_parameter x (hmem x hx)).differentiableAt
  · intro x hx
    have hxo := hmem x hx
    have hAr : 0 < A x*r x := mul_pos (Analysis.marked_A_pos x ⟨hxo.1.le,hxo.2.le⟩) (r_pos x ⟨hxo.1.le,hxo.2⟩)
    rw [(allOrderCorrectedPrefactorLog_hasDerivAt P g p L hp hs x hxo).deriv,
      (Analysis.logZ_hasDerivAt_open_parameter x hxo).deriv,abs_div,abs_of_pos hAr]
    have he := htr g hs hh L horder x hxo
    calc _ ≤ (C*B^(L+2)*((L+2).factorial:ℝ)^2/(complexity g p:ℝ)^(L+1))/(A x*r x) := div_le_div_of_nonneg_right he hAr.le
         _ = _ := by ring
end WP.HigherOrder
