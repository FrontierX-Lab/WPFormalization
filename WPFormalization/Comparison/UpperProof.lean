import WPFormalization.Comparison.MaximaRecursion
import WPFormalization.Comparison.TerminalWeighted
import WPFormalization.Statements.Weighted
import WPFormalization.Comparison.RecordGrowth
import WPFormalization.Comparison.MaximaRates
noncomputable section
namespace WP
open Set
theorem comparison_upper_proof (P : PsiTheory) : ∃ c₀ : ℝ, 0 < c₀ ∧
    ∀ c ∈ Set.Ioc 0 c₀, ∃ C : ℝ, 0 < C ∧
      ∀ g : ℕ, ∀ d : List ℕ, 1 ≤ d.length → Stable g d.length →
      d.sum ≤ dimension g d.length → ∀ Y ∈ Set.Icc 0 y₀,
        ratio P g d Y ≤ C*clippedWeight c d*Real.exp (C*Real.sqrt (complexity g d.length)) := by
  obtain ⟨cL,hcL,hlinearFamily⟩:=weighted_linear_bound
  obtain ⟨cS,hcS,hseparatingFamily⟩:=weighted_separating_bound
  refine ⟨min cL cS,lt_min hcL hcS,?_⟩
  intro c hc
  have hcLin:c∈Ioc 0 cL:=⟨hc.1,hc.2.trans (min_le_left _ _)⟩
  have hcSep:c∈Ioc 0 cS:=⟨hc.1,hc.2.trans (min_le_right _ _)⟩
  obtain ⟨L₁,L,hL₁,hL,hlinear⟩:=hlinearFamily c hcLin
  obtain ⟨B₁,B,hB₁,hB,hseparating⟩:=hseparatingFamily c hcSep
  obtain ⟨K,hK,hterminal⟩:=terminal_weighted_ratio_bounded P c hc.1
  have hl:∀g pivot:ℕ,∀d:List ℕ,PivotChoice pivot d→¬Terminal g (pivot::d)→
      (pivot::d).sum ≤ dimension g (d.length+1)→∀Y∈Icc (0:ℝ) y₀,
      weightedLinear c Y g pivot d ≤ 1+L/Real.sqrt (complexity g (d.length+1)):=by
    intro g pivot d hp ht hd Y hY
    exact (hlinear g pivot d hp ht hd Y hY).1.trans (hlinear g pivot d hp ht hd Y hY).2
  have hs:∀g pivot:ℕ,∀d:List ℕ,PivotChoice pivot d→¬Terminal g (pivot::d)→
      (pivot::d).sum ≤ dimension g (d.length+1)→∀Y∈Icc (0:ℝ) y₀,
      weightedSeparating c Y g pivot d ≤ B/Real.sqrt (complexity g (d.length+1)):=by
    intro g pivot d hp ht hd Y hY
    exact (hseparating g pivot d hp ht hd Y hY).1.trans (hseparating g pivot d hp ht hd Y hY).2
  let f:=clippedComplexityMaximum P c
  have hreduce:∀a b:ℝ,0<b→b<a→a-b<(1/12:ℝ)→
      a∈Analysis.exponentialRates f→b∈Analysis.exponentialRates f:=by
    intro a b hb hba hab ha
    obtain ⟨Ca,hCa,hglobal⟩:=ha.2
    obtain ⟨Cb,hCb,hbound⟩:=Analysis.exponential_bound_of_record_recursion f b L (Ca*B) K hb (by
      intro n hn hrec
      exact Comparison.exponential_record_recurrence P c L B K a b Ca hb hab.le hCa.le hK.le
        hglobal hterminal hl hs n hn hrec)
    exact ⟨hb.le,Cb,hCb,hbound⟩
  have hsub:=Analysis.subexponential_of_rate_reduction f (1/12) (by norm_num)
    (clippedComplexityMaximum_rates_nonempty P c) hreduce
  obtain ⟨D,hD,hglobal⟩:=hsub (1/24) (by norm_num)
  obtain ⟨C,hC,hbound⟩:=Analysis.sqrt_bound_of_record_recursion f L (D*B) K hL.le (mul_pos hD hB).le (by
    intro A hA n hn hrec
    exact Comparison.sqrt_record_recurrence P c L B K (1/24) D (by norm_num) hD.le hK.le
      hglobal hterminal hl hs A hA n hn hrec)
  refine ⟨C,hC,?_⟩
  intro g d hn hst hd Y hY
  have hactual:=clippedComplexityMaximum_bound P c g d hn hst hd Y hY
  have hupper:=mul_le_mul_of_nonneg_right (hbound (complexity g d.length)) (clippedWeight_pos c d).le
  apply hactual.trans
  convert hupper using 1 <;> ring
end WP
