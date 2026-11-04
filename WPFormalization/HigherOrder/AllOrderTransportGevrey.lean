import WPFormalization.HigherOrder.AllOrderCuspInverse
import WPFormalization.HigherOrder.AllOrderTransportExact
import WPFormalization.HigherOrder.RecursiveRemainderProof
/-! The actual all-order logarithmic derivative has a uniform Gevrey-two error. The public producer supplies the proved recursive remainder itself; no remainder or whole transport assumption remains. -/
noncomputable section
namespace WP.HigherOrder
open Set PowerSeries
lemma actual_log_transport_gevrey_two_of_recursiveRemainder (P:PsiTheory)
    (hr:UniformRecursiveRemainderTarget P)(p:ℕ)(hp:1 ≤ p) :
    ∃C B c:ℝ,0<C ∧ 0<B ∧ 0<c ∧∀g:ℕ,Stable g p→1 ≤ complexity g p→
    ∀L:ℕ,((L+2:ℕ):ℝ) ≤ c*Real.sqrt (complexity g p:ℝ)→∀Y∈Ioo (0:ℝ) y₀,
      |(A Y*r Y)*deriv (prefactorLogError P g p) Y-transportTruncation P p L Y (complexity g p:ℝ)| ≤
        C*B^(L+2)*((L+2).factorial:ℝ)^2/(complexity g p:ℝ)^(L+1) := by
  obtain ⟨C,B,c,hC,hB,hc,hbound⟩:=actual_cusp_inverse_gevrey_two_of_recursiveRemainder P hr p hp
  refine ⟨C,B,c,hC,hB,hc,?_⟩
  intro g hs hhN L horder Y hY
  have hh:0<(complexity g p:ℝ):=by exact_mod_cast (show 0<complexity g p by omega)
  rw[prefactorLogError_transport_defect_identity P g p L hp hs Y hY,abs_mul,abs_of_pos hh]
  have hb:=hbound g hs hhN (L+2) (by omega) horder Y ⟨hY.1.le,hY.2.le⟩
  have hm:=mul_le_mul_of_nonneg_left hb hh.le
  apply hm.trans_eq
  rw[show L+2=(L+1)+1 by omega,pow_succ]
  field_simp[hh.ne']
  <;>simp only[pow_succ]<;>ring

lemma actual_log_transport_gevrey_two (P:PsiTheory)
    (p:ℕ)(hp:1 ≤ p) :
    ∃C B c:ℝ,0<C ∧ 0<B ∧ 0<c ∧∀g:ℕ,Stable g p→1 ≤ complexity g p→
    ∀L:ℕ,((L+2:ℕ):ℝ) ≤ c*Real.sqrt (complexity g p:ℝ)→∀Y∈Ioo (0:ℝ) y₀,
      |(A Y*r Y)*deriv (prefactorLogError P g p) Y-transportTruncation P p L Y (complexity g p:ℝ)| ≤
        C*B^(L+2)*((L+2).factorial:ℝ)^2/(complexity g p:ℝ)^(L+1) := by
  exact actual_log_transport_gevrey_two_of_recursiveRemainder P (canonical_uniform_recursive_remainders P) p hp
end WP.HigherOrder
