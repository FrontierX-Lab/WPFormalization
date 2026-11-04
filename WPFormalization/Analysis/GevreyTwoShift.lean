import WPFormalization.Analysis.GevreyTwoPointwise
/-! Fixed complexity shifts preserve actual quadratic-window Gevrey-two
remainders. The coefficient substitution is the existing t/(1-c*t). -/
noncomputable section
namespace WP.Analysis
open PowerSeries
lemma shifted_gevreyTwo_polynomial_remainder (f:WP.HigherOrder.Series) (c C B:ℝ)
    (hC:0≤C)(hB:0<B)(hf:∀n,|PowerSeries.coeff n f|≤C*B^n*(n.factorial:ℝ)^2)
    (K:ℕ)(z:ℂ)(hz:‖z‖≤1/(8*(B+|c|+1)*((K:ℝ)+1)^2)):
    ‖truncatedSeriesPolynomial f K (inverseComplexShift c z)-
      ∑i∈Finset.range (K+1),((PowerSeries.coeff i (WP.HigherOrder.complexityShift c f):ℝ):ℂ)*z^i‖≤
      4*C*(4*(B+|c|+1)*(Real.exp 1)^2)^(K+1)*((K+1).factorial:ℝ)^2*‖z‖^(K+1) := by
  let B':ℝ:=2*(B+|c|+1)
  have hBp:0<B':=by dsimp[B'];positivity
  have hBB:2*B≤B':=by dsimp[B'];have ha:=abs_nonneg c;linarith
  have hBc:|c|≤B':=by dsimp[B'];have ha:=abs_nonneg c;linarith
  have hKp:0<((K:ℝ)+1)^2:=by positivity
  have hK1:1≤((K:ℝ)+1)^2:=by have hk:=Nat.cast_nonneg (α:=ℝ) K;nlinarith
  have hdata(w:ℂ)(hw:‖w‖≤1/(2*B'*((K:ℝ)+1)^2)):
      1-(c:ℂ)*w≠0 ∧ ‖truncatedSeriesPolynomial f K (inverseComplexShift c w)‖≤2*C:=by
    have hsmall:|c| *‖w‖≤1/2:=by
      have he:‖w‖*(2*B'*((K:ℝ)+1)^2)≤1:=(le_div_iff₀ (by positivity)).mp hw
      have hd:2*|c|≤2*B'*((K:ℝ)+1)^2:=by
        have hm:=mul_le_mul_of_nonneg_left hK1 hBp.le
        nlinarith
      have hm:=mul_le_mul_of_nonneg_right hd (norm_nonneg w)
      nlinarith
    obtain ⟨hne,hns⟩:=inverseComplexShift_norm c w hsmall
    have hs:‖inverseComplexShift c w‖≤1/(2*B*((K:ℝ)+1)^2):=by
      calc
        _ ≤ 2*‖w‖:=hns
        _ ≤ 2*(1/(2*B'*((K:ℝ)+1)^2)):=mul_le_mul_of_nonneg_left hw (by norm_num)
        _ ≤ 1/(2*B*((K:ℝ)+1)^2):=by
          rw[mul_one_div]
          apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
          have hm:=mul_le_mul_of_nonneg_right hBB hKp.le
          nlinarith
    exact ⟨hne,truncatedSeriesPolynomial_gevreyTwo_norm_bound f C B hC hB hf K _ hs⟩
  have hd:DifferentiableOn ℂ (fun w=>truncatedSeriesPolynomial f K (inverseComplexShift c w))
      (Metric.closedBall 0 (1/(2*B'*((K:ℝ)+1)^2))):=by
    intro w hw
    have hw':‖w‖≤1/(2*B'*((K:ℝ)+1)^2):=by simpa only[Metric.mem_closedBall,dist_zero_right] using hw
    exact ((truncatedSeriesPolynomial_analytic f K _).comp
      (inverseComplexShift_analytic c w (hdata w hw').1)).differentiableAt.differentiableWithinAt
  have hc:∀w∈Metric.sphere (0:ℂ) (1/(2*B'*((K:ℝ)+1)^2)),
      ‖truncatedSeriesPolynomial f K (inverseComplexShift c w)‖≤2*C:=by
    intro w hw
    exact (hdata w (by simpa only[Metric.mem_closedBall,dist_zero_right] using Metric.sphere_subset_closedBall hw)).2
  have hz':‖z‖≤1/(4*B'*((K:ℝ)+1)^2):=by convert hz using 1;dsimp[B'];ring
  have he:=complex_taylor_quadratic_factorial_bound
    (fun w=>truncatedSeriesPolynomial f K (inverseComplexShift c w)) B' (2*C) hBp
    (by positivity) K hd hc z hz'
  have hcoef:(∑i∈Finset.range (K+1),WP.coeff
      (fun w=>truncatedSeriesPolynomial f K (inverseComplexShift c w)) i*z^i)=
      ∑i∈Finset.range (K+1),((PowerSeries.coeff i (WP.HigherOrder.complexityShift c f):ℝ):ℂ)*z^i:=by
    apply Finset.sum_congr rfl
    intro i hi
    rw[truncatedSeriesPolynomial_shift_coeff f c K i (by have hh:=Finset.mem_range.mp hi;omega)]
  rw[hcoef] at he
  convert he using 1;dsimp[B'];ring


lemma shifted_gevreyTwo_polynomial_real_remainder (f:WP.HigherOrder.Series) (c C B:ℝ)
    (hC:0≤C)(hB:0<B)(hf:∀n,|PowerSeries.coeff n f|≤C*B^n*(n.factorial:ℝ)^2)
    (K:ℕ)(h:ℝ)(hh:0<h)(hu:0<h-c)(hw:8*(B+|c|+1)*((K:ℝ)+1)^2≤h):
    |inversePowerTruncation f K (h-c)-inversePowerTruncation (WP.HigherOrder.complexityShift c f) K h|≤
      4*C*(4*(B+|c|+1)*(Real.exp 1)^2)^(K+1)*((K+1).factorial:ℝ)^2/h^(K+1):=by
  have hz:‖((1/h:ℝ):ℂ)‖≤1/(8*(B+|c|+1)*((K:ℝ)+1)^2):=by
    rw[Complex.norm_real,Real.norm_eq_abs,abs_of_pos (one_div_pos.mpr hh)]
    exact one_div_le_one_div_of_le (by positivity) hw
  have he:=shifted_gevreyTwo_polynomial_remainder f c C B hC hB hf K ((1/h:ℝ):ℂ) hz
  have hs:inverseComplexShift c ((1/h:ℝ):ℂ)=((1/(h-c):ℝ):ℂ):=by
    have hh':(h:ℂ)≠0:=by exact_mod_cast hh.ne'
    have hu':(h:ℂ)-(c:ℂ)≠0:=by exact_mod_cast hu.ne'
    dsimp[inverseComplexShift]
    push_cast
    field_simp
  have hp(s:WP.HigherOrder.Series)(t:ℝ):truncatedSeriesPolynomial s K ((1/t:ℝ):ℂ)=
      ((inversePowerTruncation s K t):ℂ):=by
    rw[truncatedSeriesPolynomial_real]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    rw[div_pow,one_pow,mul_one_div]
  have hq:(∑i∈Finset.range (K+1),((PowerSeries.coeff i (WP.HigherOrder.complexityShift c f):ℝ):ℂ)*((1/h:ℝ):ℂ)^i)=
      ((inversePowerTruncation (WP.HigherOrder.complexityShift c f) K h):ℂ):=by
    change truncatedSeriesPolynomial (WP.HigherOrder.complexityShift c f) K ((1/h:ℝ):ℂ)=_
    exact hp _ h
  rw[hs,hp,hq,←Complex.ofReal_sub] at he
  simp only[Complex.norm_real,Real.norm_eq_abs,abs_of_pos (one_div_pos.mpr hh),div_pow,one_pow] at he
  convert he using 1;ring


end WP.Analysis
