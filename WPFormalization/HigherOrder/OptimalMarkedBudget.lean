import WPFormalization.HigherOrder.OptimalMarkedModel
/-! The same actual optimal model with its proved individual-term budget.
The square-root window is retained explicitly; the budget is not inferred
from the norm of a sum. The legacy comparison statement is unchanged. -/
noncomputable section
namespace WP.HigherOrder
open Set
lemma optimal_marked_model_real_comparison_with_budget (P:PsiTheory) (p:ℕ) (hp:1≤p):
    ∃(Ω:Set ℂ)(L:ℕ→ℂ→ℂ)(C B κ a H:ℝ),
      IsOpen Ω ∧ (∀Y∈Icc (0:ℝ) y₀,(Y:ℂ)∈Ω) ∧
      0<C ∧ 0<B ∧ 0<κ ∧ 0<a ∧ 0<H ∧
      (∀j,AnalyticOnNhd ℂ (L j) Ω) ∧
      (∀z,L 0 z=1) ∧
      (∀j Y,Y∈Icc (0:ℝ) y₀→L j Y=(markedCoefficient P p j Y:ℂ)) ∧
      (∀j z,z∈Ω→‖L j z‖≤C*B^j*(j.factorial:ℝ)^2) ∧
      ∀g:ℕ,H≤(complexity g p:ℝ)→
        let h:ℝ:=complexity g p
        let J:=⌊κ*Real.sqrt h⌋₊
        2*B*((J:ℝ)+1)^2≤h ∧
        (∀z∈Ω,‖finiteMarkedFactor L h J z-1‖≤2*C*B/h ∧
          1/2≤‖finiteMarkedFactor L h J z‖ ∧
          ‖finiteMarkedFactor L h J z‖≤2 ∧ finiteMarkedFactor L h J z≠0) ∧
        (∀Y∈Icc (0:ℝ) y₀,
          finiteMarkedFactor L h J (Y:ℂ)=(realFiniteMarkedFactor P p h J Y:ℂ)) ∧
        (∀Y∈Ico (0:ℝ) y₀,
          |(Real.pi*markedF P g p (XR Y)/markedModel g p Y)/
            realFiniteMarkedFactor P p h J Y-1|≤2*C*Real.exp (-a*Real.sqrt h)):=by
  obtain ⟨C₀,B,c,H₀,hC₀,hB,hc,hH₀,hpair,herr,hlog,hoptOld⟩:=full_expansion_proof P p hp
  obtain ⟨Ω,aC,L₀,hΩ,hcover,hana,hrest,hbound⟩:=hpair
  let C:=C₀+1
  let L:ℕ→ℂ→ℂ:=fun j z=>if j=0 then 1 else L₀ j z
  have hC:0<C:=by dsimp[C];linarith
  have hC₀C:C₀≤C:=by dsimp[C];linarith
  have hLa:∀j,AnalyticOnNhd ℂ (L j) Ω:=by
    intro j
    by_cases hj:j=0
    · simp only[L,hj,ite_true];exact analyticOnNhd_const
    · simpa only[L,ite_eq_right hj] using (hana j).2
  have hL0:∀z,L 0 z=1:=by intro z;simp[L]
  have hLr:∀j Y,Y∈Icc (0:ℝ) y₀→L j Y=(markedCoefficient P p j Y:ℂ):=by
    intro j Y hY
    by_cases hj:j=0
    · subst j;simp[L]
    · simpa only[L,ite_eq_right hj] using (hrest j Y hY).2
  have hLb:∀j z,z∈Ω→‖L j z‖≤C*B^j*(j.factorial:ℝ)^2:=by
    intro j z hz
    by_cases hj:j=0
    · subst j;simp only[L,ite_true,norm_one,pow_zero,Nat.factorial_zero,Nat.cast_one,mul_one]
      dsimp[C];linarith
    · have hb:‖L₀ j z‖≤C₀*B^j*(j.factorial:ℝ)^2:=by
        have ht:=hbound j z hz
        linarith[norm_nonneg (aC j z)]
      simp only[L,ite_eq_right hj]
      exact hb.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC₀C (by positivity)) (sq_nonneg _))
  obtain ⟨cw,Hw,hcw,hcwc,hHw,hwindow⟩:=Analysis.gevreyTwo_cauchy_window B c hB hc
  obtain ⟨κ,a,Ho,hκ,hκcw,ha,hHo,hopt⟩:=Analysis.gevreyTwo_optimal_scalar B cw hB hcw
  let H:=max H₀ (max Hw (max Ho (4*C*B)))
  have hH:0<H:=hH₀.trans_le (le_max_left _ _)
  refine ⟨Ω,L,C,B,κ,a,H,hΩ,hcover,hC,hB,hκ,ha,hH,hLa,hL0,hLr,hLb,?_⟩
  intro g hg
  dsimp only
  let h:ℝ:=complexity g p
  let J:=⌊κ*Real.sqrt h⌋₊
  have hh:0<h:=hH.trans_le hg
  have hg₀:H₀≤h:=(le_max_left _ _).trans hg
  have hgw:Hw≤h:=((le_max_left _ _).trans (le_max_right _ _)).trans hg
  have hgo:Ho≤h:=((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans hg
  have hgsize:4*C*B≤h:=((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans hg
  have hJw:(J:ℝ)≤cw*Real.sqrt h:=
    (Nat.floor_le (mul_nonneg hκ.le (Real.sqrt_nonneg h))).trans
      (mul_le_mul_of_nonneg_right hκcw (Real.sqrt_nonneg _))
  have hJc:(J:ℝ)≤c*Real.sqrt h:=hJw.trans
    (mul_le_mul_of_nonneg_right hcwc (Real.sqrt_nonneg _))
  have hw:2*B*((J:ℝ)+1)^2≤h:=by
    have hw':=hwindow h hgw J hJw
    nlinarith[sq_nonneg ((J:ℝ)+1)]
  have hnear:∀z∈Ω,‖finiteMarkedFactor L h J z-1‖≤2*C*B/h:=by
    intro z hz
    exact Analysis.gevreyTwo_finite_correction_norm (fun j=>L j z) C B h J hC.le hB hh
      (hL0 z) (fun j=>hLb j z hz) hw
  have hhalf:2*C*B/h≤1/2:=(div_le_iff₀ hh).mpr (by linarith)
  have hreal:∀Y∈Icc (0:ℝ) y₀,
      finiteMarkedFactor L h J (Y:ℂ)=(realFiniteMarkedFactor P p h J Y:ℂ):=by
    intro Y hY
    simp only[finiteMarkedFactor,realFiniteMarkedFactor,Complex.ofReal_sum,Complex.ofReal_div,Complex.ofReal_pow]
    exact Finset.sum_congr rfl (fun j hj=>by rw[hLr j Y hY])
  refine ⟨hw,?_,hreal,?_⟩
  · intro z hz
    exact ⟨hnear z hz,Analysis.near_one_norm_bounds _ ((hnear z hz).trans hhalf)⟩
  · intro Y hY
    have hYc:Y∈Icc (0:ℝ) y₀:=⟨hY.1,hY.2.le⟩
    have hPr:|realFiniteMarkedFactor P p h J Y-1|≤1/2:=by
      have hn:=(hnear (Y:ℂ) (hcover Y hYc)).trans hhalf
      rw[hreal Y hYc,←Complex.ofReal_one,←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs] at hn
      exact hn
    have he:=herr g J hg₀ hJc Y hY
    have ht:=hopt h hgo
    change B^(J+1)*((J+1).factorial:ℝ)^2/h^(J+1)≤Real.exp (-a*Real.sqrt h) at ht
    have he':|Real.pi*markedF P g p (XR Y)/markedModel g p Y-realFiniteMarkedFactor P p h J Y|≤
        C*Real.exp (-a*Real.sqrt h):=by
      apply he.trans
      have hb:=mul_le_mul_of_nonneg_left ht hC₀.le
      have hc0:=mul_le_mul_of_nonneg_right hC₀C (Real.exp_pos (-a*Real.sqrt h)).le
      have hb' : C₀*B^(J+1)*((J+1).factorial:ℝ)^2/h^(J+1) ≤ C₀*Real.exp (-a*Real.sqrt h) := by
        convert hb using 1 <;>ring
      exact hb'.trans hc0
    simpa only [mul_assoc] using Analysis.real_relative_error_of_near_one _ _ _ hPr he'
end WP.HigherOrder
