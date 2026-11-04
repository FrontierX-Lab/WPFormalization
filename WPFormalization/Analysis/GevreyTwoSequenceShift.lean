import WPFormalization.Analysis.GevreyTwoShift
import WPFormalization.Analysis.GevreyTwoSequenceOperations
noncomputable section
namespace WP.Analysis
open Filter PowerSeries
open scoped Topology
lemma GevreyTwoSequence.shift (scale F:ℕ→ℝ)(hs:Tendsto scale atTop atTop)
    (f:WP.HigherOrder.Series)(hF:GevreyTwoSequence scale F f)(c:ℝ):
    GevreyTwoSequence (fun n=>scale n+c) F (WP.HigherOrder.complexityShift c f):=by
  obtain ⟨C₀,B₀,hC₀,hB₀,hcoeff⟩:=GevreyTwoSequence.coeff_bound scale F hs f hF
  obtain ⟨C₁,B₁,q,N₀,hC₁,hB₁,hq,herr⟩:=hF
  let T:ℝ:=B₀+|c|+1
  have hT:0<T:=by dsimp[T];positivity
  obtain ⟨q',H,hq',hq'q,hH,hwindowAll⟩:=gevreyTwo_cauchy_window (2*T) (q/2) (by positivity) (by positivity)
  obtain ⟨N₁,hN₁⟩:=eventually_atTop.1 (hs.eventually
    (eventually_ge_atTop (max (|c|+1) (H+|c|))))
  let N:ℕ:=max N₀ N₁
  let B:ℝ:=2*B₁+4*T*(Real.exp 1)^2
  let C:ℝ:=C₁+4*C₀
  refine ⟨C,B,q',N,by dsimp[C];positivity,by dsimp[B];positivity,
    hq',?_⟩
  intro n hn
  have hn₀:N₀≤n:=(le_max_left _ _).trans hn
  have hn₁:N₁≤n:=(le_max_right _ _).trans hn
  have hd:=herr n hn₀
  have hl:max (|c|+1) (H+|c|)≤ scale n:=hN₁ n hn₁
  have hs₁:|c|+1≤ scale n:=(le_max_left _ _).trans hl
  have hsT:H+|c|≤ scale n:=(le_max_right _ _).trans hl
  let h:ℝ:=scale n+c
  have hh:0<h:=by dsimp[h];have hc:=neg_abs_le c;linarith
  have hhT:H≤h:=by dsimp[h];have hc:=neg_abs_le c;linarith
  have hhalf:0<h/2:=by positivity
  have hhalfU:h/2≤ scale n:=by dsimp[h];have hc:=le_abs_self c;linarith
  have hu:h-c=scale n:=by dsimp[h];ring
  refine ⟨hh,?_⟩
  intro K hK
  have hroots:Real.sqrt h/2≤Real.sqrt (scale n):=by
    have h₁:=Real.sqrt_nonneg h
    have h₂:=Real.sqrt_nonneg (scale n)
    have he₁:=Real.sq_sqrt hh.le
    have he₂:=Real.sq_sqrt hd.1.le
    nlinarith
  have hKq:(K:ℝ)≤q*Real.sqrt (scale n):=by
    have hk:(K:ℝ)≤(q/2)*Real.sqrt h:=hK.trans
      (mul_le_mul_of_nonneg_right hq'q (Real.sqrt_nonneg h))
    have hm:=mul_le_mul_of_nonneg_left hroots hq.le
    nlinarith
  have hwindow:8*T*((K:ℝ)+1)^2≤h:=by
    have he:=hwindowAll h hhT K hK
    nlinarith
  have he:=hd.2 K hKq
  have hactual:|F n-inversePowerTruncation f K (scale n)|≤
      C₁*(2*B₁)^(K+1)*((K+1).factorial:ℝ)^2/h^(K+1):=by
    apply he.trans
    calc
      _ ≤ C₁*B₁^(K+1)*((K+1).factorial:ℝ)^2/(h/2)^(K+1):=
        div_le_div_of_nonneg_left (by positivity) (pow_pos hhalf _)
          (pow_le_pow_left₀ hhalf.le hhalfU _)
      _ = _:=by rw[div_pow,mul_pow];field_simp
  have htail:=shifted_gevreyTwo_polynomial_real_remainder f c C₀ B₀ hC₀.le hB₀ hcoeff K h hh
    (by rw[hu];exact hd.1) hwindow
  rw[hu] at htail
  have hb₁:2*B₁≤B:=le_add_of_nonneg_right (by positivity)
  have hb₂:4*T*(Real.exp 1)^2≤B:=le_add_of_nonneg_left (by positivity)
  calc
    _ ≤ |F n-inversePowerTruncation f K (scale n)|+
        |inversePowerTruncation f K (scale n)-inversePowerTruncation (WP.HigherOrder.complexityShift c f) K h|:=abs_sub_le _ _ _
    _ ≤ C₁*(2*B₁)^(K+1)*((K+1).factorial:ℝ)^2/h^(K+1)+
        4*C₀*(4*T*(Real.exp 1)^2)^(K+1)*((K+1).factorial:ℝ)^2/h^(K+1):=add_le_add hactual htail
    _ ≤ C₁*B^(K+1)*((K+1).factorial:ℝ)^2/h^(K+1)+
        4*C₀*B^(K+1)*((K+1).factorial:ℝ)^2/h^(K+1):=by gcongr
    _ = _:=by dsimp[C];ring


end WP.Analysis
