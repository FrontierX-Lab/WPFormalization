import WPFormalization.HigherOrder.AllOrderLogMatching
import WPFormalization.HigherOrder.LogMarkedRegularity
import WPFormalization.Analysis.FiniteExpGevreyTwo
import WPFormalization.Analysis.GevreyTwoWindow
/-! The actual marked relative Gevrey-two remainder from the proved actual logarithm.
The original canonical finiteExp jets are used, and all constants precede genus,
truncation and the full physical parameter range. -/

noncomputable section
namespace WP.HigherOrder
open Set
lemma exp_prefactorLogError (P:PsiTheory) (g p:ℕ) (hp:1 ≤ p) (hs:Stable g p)
    (Y:ℝ) (hY:Y∈Ico (0:ℝ) y₀):
    Real.exp (prefactorLogError P g p Y)=Real.pi*markedF P g p (XR Y)/markedModel g p Y:=by
  have hh:(0:ℝ)<complexity g p:=by exact_mod_cast (show 0<complexity g p by unfold complexity Stable at *;omega)
  have hA:=Analysis.marked_A_pos Y ⟨hY.1,hY.2.le⟩
  have hΘ:=Analysis.marked_Theta_pos Y ⟨hY.1,hY.2.le⟩
  have hZ:=Analysis.marked_Z_pos Y hY
  have hG:=Real.Gamma_pos_of_pos hh
  have hr:=r_pos Y hY
  have hP:=Real.rpow_pos_of_pos hr ((p:ℝ)/2)
  have hS:=Real.sqrt_pos.mpr (mul_pos hA hΘ)
  have hD:=Real.sqrt_pos.mpr (mul_pos Real.pi_pos hh)
  have hM:0 < markedModel g p Y:=by unfold markedModel;positivity
  exact Real.exp_log (div_pos (mul_pos Real.pi_pos (markedF_pos_parameter P g p hp hs Y hY)) hM)

lemma actual_marked_relative_uniform_gevrey_two (P:PsiTheory) (p:ℕ) (hp:1 ≤ p):
    ∃C B c h₀:ℝ,0<C ∧ 0<B ∧ 0<c ∧ 0<h₀ ∧
      ∀g K:ℕ,h₀ ≤ (complexity g p:ℝ)→(K:ℝ) ≤ c*Real.sqrt (complexity g p:ℝ)→
      ∀Y∈Ico (0:ℝ) y₀,
      |Real.pi*markedF P g p (XR Y)/markedModel g p Y-
        ∑j∈Finset.range (K+1),markedCoefficient P p j Y/(complexity g p:ℝ)^j| ≤
        C*B^(K+1)*((K+1).factorial:ℝ)^2/(complexity g p:ℝ)^(K+1):=by
  obtain ⟨Ce,Be,ce,He,hCe,hBe,hce,hHe,herr⟩:=actual_marked_log_uniform_gevrey_two P p hp
  obtain ⟨Ca,Ba,hCa,hBa,hcont,hderiv,hcoef,hlip⟩:=logarithmicMarkedCoefficient_real_gevrey_regularity P p hp
  obtain ⟨c,H,hc,hcce,hH,hwindow⟩:=Analysis.gevreyTwo_cauchy_window Ba ce hBa hce
  let h₀:=max He (max H 1)
  have hh₀:0<h₀:=hHe.trans_le (le_max_left _ _)
  let M:=2*Ca+Ce*Be+1
  have hM:2*Ca ≤ M:=by dsimp[M];nlinarith[mul_pos hCe hBe]
  let C:=Real.exp M*Ce+2*Real.exp (2*Ca)
  let B:=Be+2*Ba*(Real.exp 1)^2
  refine ⟨C,B,c,h₀,by dsimp[C];positivity,by dsimp[B];positivity,hc,hh₀,?_⟩
  intro g K hg hK Y hY
  let h:ℝ:=complexity g p
  have hh:0<h:=hh₀.trans_le hg
  have hgHe:He ≤ h:=(le_max_left _ _).trans hg
  have hgH:H ≤ h:=((le_max_left _ _).trans (le_max_right _ _)).trans hg
  have hh1:1 ≤ h:=((le_max_right _ _).trans (le_max_right _ _)).trans hg
  have hst:Stable g p:=by
    have hn:1 ≤ complexity g p:=by exact_mod_cast (show (1:ℝ) ≤ (complexity g p:ℝ) from hh1)
    unfold complexity Stable at *
    omega
  have hKlog:(K:ℝ) ≤ ce*Real.sqrt h:=hK.trans (mul_le_mul_of_nonneg_right hcce (Real.sqrt_nonneg _))
  have herrK:=herr g K hgHe hKlog Y hY
  have herr0:|prefactorLogError P g p Y| ≤ Ce*Be/h:=by
    have hz:(0:ℝ) ≤ ce*Real.sqrt (complexity g p:ℝ):=mul_nonneg hce.le (Real.sqrt_nonneg _)
    have ht:=herr g 0 hgHe (by simpa only[Nat.cast_zero] using hz) Y hY
    simpa only[Nat.zero_add,Finset.sum_range_one,logarithmicMarkedCoefficient,ite_true,zero_div,
      sub_zero,pow_one,Nat.factorial_one,Nat.cast_one,one_pow,mul_one] using ht
  have hbound:Ce*Be/h ≤ Ce*Be:=by
    apply (div_le_iff₀ hh).mpr
    have ht:=mul_le_mul_of_nonneg_left hh1 (mul_pos hCe hBe).le
    nlinarith
  have hx:prefactorLogError P g p Y ≤ M:=by
    have he:prefactorLogError P g p Y ≤ Ce*Be:=(le_abs_self _).trans (herr0.trans hbound)
    dsimp[M]
    linarith
  have hf:∀n:ℕ,|PowerSeries.coeff n (markedLogSeries P p Y)| ≤ Ca*Ba^n*(n.factorial:ℝ)^2:=by
    intro n
    simpa only[markedLogSeries,PowerSeries.coeff_mk] using hcoef n Y ⟨hY.1,hY.2.le⟩
  have hlog:|prefactorLogError P g p Y-
      ∑i∈Finset.range (K+1),PowerSeries.coeff i (markedLogSeries P p Y)/h^i| ≤
        Ce*Be^(K+1)*((K+1).factorial:ℝ)^2/h^(K+1):=by
    simpa only[markedLogSeries,PowerSeries.coeff_mk] using herrK
  have hexp:=Analysis.finiteExp_gevreyTwo_error_of_log_error (markedLogSeries P p Y) Ca Ba Ce Be M
    hCa.le hBa hCe.le hBe.le hM (markedLogSeries_constant P p Y) hf K h
    (prefactorLogError P g p Y) hh (hwindow h hgH K hK) hx hlog
  rw[exp_prefactorLogError P g p hp hst Y hY] at hexp
  simpa only[markedCoefficient] using hexp
end WP.HigherOrder
