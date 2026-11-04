import WPFormalization.HigherOrder.OptimalMarkedModel
/-! The original finite-order marked model, before any growing-order selection.
One actual canonical family serves every fixed retained order; the real error
is the original inverse-complexity remainder, divided by a proved nonzero
finite factor. -/
noncomputable section
namespace WP.HigherOrder
open Set
lemma local_comparison_marked_source (P:PsiTheory) (p:ℕ) (hp:1≤p):
    ∃(Ω:Set ℂ)(L:ℕ→ℂ→ℂ)(C B c H:ℝ),
      IsOpen Ω ∧ (∀Y∈Icc (0:ℝ) y₀,(Y:ℂ)∈Ω) ∧
      0<C ∧ 0<B ∧ 0<c ∧ 0<H ∧
      (∀j,AnalyticOnNhd ℂ (L j) Ω) ∧
      (∀z,L 0 z=1) ∧
      (∀j Y,Y∈Icc (0:ℝ) y₀→L j Y=(markedCoefficient P p j Y:ℂ)) ∧
      (∀j z,z∈Ω→‖L j z‖≤C*B^j*(j.factorial:ℝ)^2) ∧
      ∀g K:ℕ,H≤(complexity g p:ℝ)→
        (K:ℝ)≤c*Real.sqrt (complexity g p:ℝ)→
        2*B*((K:ℝ)+1)^2≤(complexity g p:ℝ)→
        let h:ℝ:=complexity g p
        (∀z∈Ω,‖finiteMarkedFactor L h K z-1‖≤2*C*B/h ∧
          1/2≤‖finiteMarkedFactor L h K z‖ ∧
          ‖finiteMarkedFactor L h K z‖≤2 ∧ finiteMarkedFactor L h K z≠0) ∧
        (∀Y∈Icc (0:ℝ) y₀,
          finiteMarkedFactor L h K (Y:ℂ)=(realFiniteMarkedFactor P p h K Y:ℂ)) ∧
        (∀Y∈Ico (0:ℝ) y₀,
          |(Real.pi*markedF P g p (XR Y)/markedModel g p Y)/
            realFiniteMarkedFactor P p h K Y-1|≤
              2*C*B^(K+1)*((K+1).factorial:ℝ)^2/h^(K+1)) := by
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
  let H:ℝ:=max H₀ (4*C*B)
  have hH:0<H:=hH₀.trans_le (le_max_left _ _)
  refine ⟨Ω,L,C,B,c,H,hΩ,hcover,hC,hB,hc,hH,hLa,hL0,hLr,hLb,?_⟩
  intro g K hg hK hw
  dsimp only
  let h:ℝ:=complexity g p
  have hh:0<h:=hH.trans_le hg
  have hg₀:H₀≤h:=(le_max_left _ _).trans hg
  have hgsize:4*C*B≤h:=(le_max_right _ _).trans hg
  have hnear:∀z∈Ω,‖finiteMarkedFactor L h K z-1‖≤2*C*B/h:=by
    intro z hz
    exact Analysis.gevreyTwo_finite_correction_norm (fun j=>L j z) C B h K hC.le hB hh
      (hL0 z) (fun j=>hLb j z hz) hw
  have hhalf:2*C*B/h≤1/2:=(div_le_iff₀ hh).mpr (by linarith)
  have hreal:∀Y∈Icc (0:ℝ) y₀,
      finiteMarkedFactor L h K (Y:ℂ)=(realFiniteMarkedFactor P p h K Y:ℂ):=by
    intro Y hY
    simp only[finiteMarkedFactor,realFiniteMarkedFactor,Complex.ofReal_sum,Complex.ofReal_div,Complex.ofReal_pow]
    exact Finset.sum_congr rfl (fun j hj=>by rw[hLr j Y hY])
  refine ⟨?_,hreal,?_⟩
  · intro z hz
    exact ⟨hnear z hz,Analysis.near_one_norm_bounds _ ((hnear z hz).trans hhalf)⟩
  · intro Y hY
    have hYc:Y∈Icc (0:ℝ) y₀:=⟨hY.1,hY.2.le⟩
    have hPr:|realFiniteMarkedFactor P p h K Y-1|≤1/2:=by
      have hn:=(hnear (Y:ℂ) (hcover Y hYc)).trans hhalf
      rw[hreal Y hYc,←Complex.ofReal_one,←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs] at hn
      exact hn
    have he:=herr g K hg₀ hK Y hY
    have he':|Real.pi*markedF P g p (XR Y)/markedModel g p Y-realFiniteMarkedFactor P p h K Y|≤
        C*B^(K+1)*((K+1).factorial:ℝ)^2/h^(K+1):=by
      apply he.trans
      gcongr
    have Hrel := Analysis.real_relative_error_of_near_one _ _ _ hPr he'
    convert Hrel using 1 <;> ring
end WP.HigherOrder
