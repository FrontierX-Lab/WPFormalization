import WPFormalization.Analysis.GevreyOnePointwise
/-! Actual Gevrey-one matching under exponentiation. The input is an explicit
proved error for F; finiteExp is the existing finite formal exponential. -/
noncomputable section
namespace WP.Analysis
open PowerSeries
lemma GevreyOneAsymptotic.exp_zero (F:ℝ→ℝ) (f:WP.HigherOrder.Series)
    (hF:GevreyOneAsymptotic F f) (hf0:constantCoeff f=0) :
    GevreyOneAsymptotic (fun h=>Real.exp (F h)) (WP.HigherOrder.finiteExp f) := by
  obtain ⟨C₀,B₀,hC₀,hB₀,hcoeff⟩:=GevreyOneAsymptotic.coeff_bound F f hF
  obtain ⟨C₁,B₁,q,H₀,hC₁,hB₁,hq,hH₀,hlog⟩:=hF
  let c:ℝ:=min q (1/(8*B₀))
  let H:ℝ:=max H₀ (max 1 (8*B₀))
  let B:ℝ:=B₁+2*B₀*Real.exp 1
  let M:ℝ:=C₁*B₁
  let C:ℝ:=Real.exp (M+2*C₀)*C₁+2*Real.exp (2*C₀)
  refine ⟨C,B,c,H,by dsimp[C];positivity,by dsimp[B];positivity,
    lt_min hq (by positivity),hH₀.trans_le (le_max_left _ _),?_⟩
  intro K h hhH hK
  have hh₀:H₀≤h:=(le_max_left _ _).trans hhH
  have hh1:1≤h:=((le_max_left _ _).trans (le_max_right _ _)).trans hhH
  have hhB:8*B₀≤h:=((le_max_right _ _).trans (le_max_right _ _)).trans hhH
  have hh:0<h:=zero_lt_one.trans_le hh1
  have hKq:(K:ℝ)≤q*h:=hK.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) hh.le)
  have hKr:(K:ℝ)≤(1/(8*B₀))*h:=hK.trans (mul_le_mul_of_nonneg_right (min_le_right _ _) hh.le)
  have hwindow:4*B₀*((K:ℝ)+1)≤h:=by
    have hk:(K:ℝ)*(8*B₀)≤h:=(le_div_iff₀ (by positivity:0<8*B₀)).mp
      (by simpa only[one_div,mul_comm,div_eq_mul_inv,one_mul] using hKr)
    nlinarith
  let P:ℝ:=inversePowerTruncation f K h
  have hL:|F h|≤M:=by
    have he:=hlog 0 h hh₀ (by simpa only[Nat.cast_zero] using (mul_pos hq hh).le)
    simp only[inversePowerTruncation,Finset.sum_range_one,PowerSeries.coeff_zero_eq_constantCoeff,
      hf0,zero_div,sub_zero,pow_zero,Nat.zero_add,Nat.factorial_one,Nat.cast_one,mul_one,pow_one] at he
    exact he.trans (div_le_self (by positivity) hh1)
  have hP:|P|≤2*C₀:=inversePowerTruncation_abs_bound f C₀ B₀ hC₀.le hB₀ hcoeff K h hh
    (by nlinarith)
  have hLP:=exp_abs_sub_le (M+2*C₀) (F h) P
    ((le_abs_self _).trans (hL.trans (by linarith)))
    ((le_abs_self _).trans (hP.trans (by dsimp[M];linarith [mul_pos hC₁ hB₁])))
  have hLerr:=hlog K h hh₀ hKq
  have hE:=finiteExp_real_polynomial_remainder f C₀ B₀ hC₀.le hB₀ hf0 hcoeff K h hh hwindow
  change |Real.exp P-inversePowerTruncation (WP.HigherOrder.finiteExp f) K h|≤_ at hE
  calc
    _ ≤ |Real.exp (F h)-Real.exp P|+|Real.exp P-inversePowerTruncation (WP.HigherOrder.finiteExp f) K h|:=abs_sub_le _ _ _
    _ ≤ Real.exp (M+2*C₀)*(C₁*B₁^(K+1)*((K+1).factorial:ℝ)/h^(K+1))+
      2*Real.exp (2*C₀)*(2*B₀*Real.exp 1)^(K+1)*((K+1).factorial:ℝ)/h^(K+1):=
      add_le_add (hLP.trans (mul_le_mul_of_nonneg_left hLerr (Real.exp_pos _).le)) hE
    _ ≤ Real.exp (M+2*C₀)*(C₁*B^(K+1)*((K+1).factorial:ℝ)/h^(K+1))+
      2*Real.exp (2*C₀)*B^(K+1)*((K+1).factorial:ℝ)/h^(K+1):=by
        have hb₁:B₁≤B:=le_add_of_nonneg_right (by positivity)
        have hb₂:2*B₀*Real.exp 1≤B:=le_add_of_nonneg_left hB₁.le
        gcongr
    _ = _:=by dsimp[C];ring
end WP.Analysis
