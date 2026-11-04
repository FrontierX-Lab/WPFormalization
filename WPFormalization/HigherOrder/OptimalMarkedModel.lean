import WPFormalization.HigherOrder.MarkedExpansionProof
import WPFormalization.Analysis.GevreyTwoWindow

/-! The same square-root truncation of the actual marked coefficient hierarchy
is uniformly close to one on its common complex neighborhood. The original
real generating function divided by this finite model has a genuine
exponentially small relative error on the complete physical interval.
This module does not yet assert the complex comparison or coefficient extraction. -/

noncomputable section
namespace WP.Analysis
lemma factorial_succ_le_order_pow (n K:ℕ) (hn:n<K) :
    ((n+1).factorial:ℝ) ≤ ((K:ℝ)+1)^n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ]
    have hnK:n<K:=by omega
    have ht:(n:ℝ)+2≤(K:ℝ)+1:=by exact_mod_cast (show n+2≤K+1 by omega)
    simpa only [Nat.cast_add, Nat.cast_one, add_assoc, show (1:ℝ)+1=2 by norm_num, mul_comm] using
      mul_le_mul ht (ih hnK) (by positivity) (by positivity)

lemma gevreyTwo_finite_correction_norm (a:ℕ→ℂ) (C B h:ℝ) (K:ℕ)
    (hC:0≤C) (hB:0<B) (hh:0<h) (hzero:a 0=1)
    (ha:∀j:ℕ,‖a j‖≤C*B^j*(j.factorial:ℝ)^2)
    (hwindow:2*B*((K:ℝ)+1)^2≤h) :
    ‖(∑j∈Finset.range (K+1),a j/(h:ℂ)^j)-1‖≤2*C*B/h:=by
  have hpow(n:ℕ)(hn:n<K):
      ‖a (n+1)/(h:ℂ)^(n+1)‖ ≤ C*B/h*(1/(2:ℝ))^n:=by
    rw[norm_div,norm_pow,Complex.norm_of_nonneg hh.le]
    have hf:=factorial_succ_le_order_pow n K hn
    have hw:‖a (n+1)‖≤C*B^(n+1)*(((K:ℝ)+1)^2)^n:=by
      apply (ha (n+1)).trans
      have hs:=pow_le_pow_left₀ (by positivity:0≤((n+1).factorial:ℝ)) hf 2
      rw[←pow_mul,show n*2=2*n by omega,pow_mul] at hs
      exact mul_le_mul_of_nonneg_left hs (by positivity)
    have ht:B*((K:ℝ)+1)^2/h≤1/2:=by
      apply (div_le_iff₀ hh).mpr
      linarith
    calc
      _ ≤ (C*B^(n+1)*(((K:ℝ)+1)^2)^n)/h^(n+1):=
        div_le_div_of_nonneg_right hw (by positivity)
      _ = C*B/h*(B*((K:ℝ)+1)^2/h)^n:=by rw[pow_succ,div_pow,mul_pow];ring
      _ ≤ _:=mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) ht n) (by positivity)
  have he:(∑j∈Finset.range (K+1),a j/(h:ℂ)^j)-1=
      ∑n∈Finset.range K,a (n+1)/(h:ℂ)^(n+1):=by
    rw[Finset.sum_range_succ']
    simp only[hzero,pow_zero,div_one,add_sub_cancel_right]
  rw[he]
  calc
    _ ≤ ∑n∈Finset.range K,‖a (n+1)/(h:ℂ)^(n+1)‖:=norm_sum_le _ _
    _ ≤ ∑n∈Finset.range K,C*B/h*(1/(2:ℝ))^n:=
      Finset.sum_le_sum (fun n hn=>hpow n (Finset.mem_range.mp hn))
    _ = C*B/h*(∑n∈Finset.range K,(1/(2:ℝ))^n):=(Finset.mul_sum _ _ _).symm
    _ ≤ C*B/h*2:=mul_le_mul_of_nonneg_left (sum_geometric_two_le K) (by positivity)
    _ = _:=by ring
end WP.Analysis

namespace WP.Analysis
lemma near_one_norm_bounds (z:ℂ) (hz:‖z-1‖≤1/2):
    1/2≤‖z‖ ∧ ‖z‖≤2 ∧ z≠0:=by
  have hl:=norm_sub_norm_le (1:ℂ) z
  rw[norm_one,norm_sub_rev] at hl
  have hu:=norm_sub_norm_le z (1:ℂ)
  rw[norm_one] at hu
  have hn:1/2≤‖z‖:=by linarith
  refine ⟨hn,by linarith,?_⟩
  exact norm_pos_iff.mp (lt_of_lt_of_le (by norm_num:(0:ℝ)<1/2) hn)
lemma real_relative_error_of_near_one (x P ε:ℝ) (hP:|P-1|≤1/2)
    (herr:|x-P|≤ε): |x/P-1|≤2*ε:=by
  have hPl:1/2≤|P|:=by
    have hl:=norm_sub_norm_le (1:ℝ) P
    simp only[Real.norm_eq_abs,abs_one,abs_sub_comm] at hl
    linarith
  have hPn:P≠0:=abs_pos.mp (lt_of_lt_of_le (by norm_num:(0:ℝ)<1/2) hPl)
  rw[div_sub_one hPn,abs_div]
  apply (div_le_iff₀ (abs_pos.mpr hPn)).mpr
  have hε:0≤ε:=(abs_nonneg _).trans herr
  have ht:=mul_le_mul_of_nonneg_left hPl (by linarith : 0≤2*ε)
  nlinarith
end WP.Analysis

namespace WP.HigherOrder
open Set
/-- The actual finite marked correction, retaining the one chosen order. -/
def finiteMarkedFactor (L:ℕ→ℂ→ℂ) (h:ℝ) (K:ℕ) (z:ℂ):ℂ:=
  ∑j∈Finset.range (K+1),L j z/(h:ℂ)^j

def realFiniteMarkedFactor (P:PsiTheory) (p:ℕ) (h:ℝ) (K:ℕ) (Y:ℝ):ℝ:=
  ∑j∈Finset.range (K+1),markedCoefficient P p j Y/h^j

lemma optimal_marked_model_real_comparison (P:PsiTheory) (p:ℕ) (hp:1≤p):
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
  refine ⟨?_,hreal,?_⟩
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
