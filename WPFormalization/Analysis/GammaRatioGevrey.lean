import WPFormalization.Analysis.FiniteExpGevrey
import WPFormalization.Analysis.GammaRatioLogGevrey
/-! Actual positive-real Gamma ratios match the prescribed Bernoulli formal exponential with a uniform Gevrey-one error in a linear truncation window. Only the registered exact classical Laplace identity is deferred. -/
set_option maxHeartbeats 800000
noncomputable section
namespace WP.Analysis
open PowerSeries Filter
open scoped Topology

lemma gammaRatioLog_coeff_gevrey_one (a : ℚ) :
    ∃C B:ℝ,0<C ∧ 0<B ∧ ∀n:ℕ,
      |PowerSeries.coeff n (WP.HigherOrder.gammaRatioLog a)|≤C*B^n*(n.factorial:ℝ) := by
  obtain ⟨r,hr,hf⟩ := (gammaRatioKernel_analytic_zero (a:ℝ)).exists_ball_analyticOnNhd
  let R:ℝ := r/2
  have hR:0<R := by dsimp only [R];positivity
  have hsub:Metric.closedBall (0:ℂ) R⊆Metric.ball (0:ℂ) r :=
    Metric.closedBall_subset_ball (by dsimp only [R];linarith)
  have hdiff:DifferentiableOn ℂ (gammaRatioKernel (a:ℝ)) (Metric.closedBall (0:ℂ) R) :=
    hf.differentiableOn.mono hsub
  obtain ⟨m,hm⟩ := (isCompact_closedBall (0:ℂ) R).bddAbove_image hdiff.continuousOn.norm
  let M:ℝ := max m 1
  have hM:0<M := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hcircle:∀z∈Metric.sphere (0:ℂ) R,‖gammaRatioKernel (a:ℝ) z‖≤M := by
    intro z hz
    exact (hm ⟨z,Metric.sphere_subset_closedBall hz,rfl⟩).trans (le_max_left _ _)
  let B:ℝ := max R⁻¹ 1
  have hB1:1≤B := le_max_right _ _
  have hB:0<B := lt_of_lt_of_le zero_lt_one hB1
  refine ⟨M,B,hM,hB,?_⟩
  intro n
  cases n with
  | zero=>simp only [PowerSeries.coeff_zero_eq_constantCoeff,WP.HigherOrder.gammaRatioLog_constant,
      abs_zero,pow_zero,Nat.factorial_zero,Nat.cast_one,mul_one];exact hM.le
  | succ n=>
    rw [←gammaRatioKernel_realCoeff_log a n,abs_mul]
    have habs : |(n.factorial:ℝ)|=(n.factorial:ℝ) := abs_of_nonneg (Nat.cast_nonneg n.factorial)
    rw [habs]
    have hc:|WP.realCoeff (gammaRatioKernel (a:ℝ)) n|≤M*B^(n+1) := by
      calc
        _ ≤ ‖WP.coeff (gammaRatioKernel (a:ℝ)) n‖ := Complex.abs_re_le_norm _
        _ ≤ M/R^n := coeff_norm_le_circle_bound _ R M hR hdiff hcircle n
        _ = M*(R⁻¹)^n := by rw [div_eq_mul_inv,inv_pow]
        _ ≤ M*B^(n+1) := mul_le_mul_of_nonneg_left
          ((pow_le_pow_left₀ (inv_pos.mpr hR).le (le_max_left _ _) n).trans
            (pow_le_pow_right₀ hB1 (Nat.le_succ n))) hM.le
    exact mul_le_mul hc (by exact_mod_cast Nat.factorial_le (Nat.le_succ n))
      (Nat.cast_nonneg _) (by positivity)

lemma gammaRatioExp_uniform_gevrey_error (a:ℚ) (ha:0<a) :
    ∃C B c h₀:ℝ,0<C ∧ 0<B ∧ 0<c ∧ 0<h₀ ∧ ∀K:ℕ,∀h:ℝ,
      h₀≤h → (K:ℝ)≤c*h →
      |Real.exp (Real.log (Real.Gamma (h+(a:ℝ)))-Real.log (Real.Gamma h)-(a:ℝ)*Real.log h)-
        ∑i∈Finset.range (K+1),PowerSeries.coeff i (WP.HigherOrder.gammaRatioSeries a)/h^i|≤
        C*B^(K+1)*((K+1).factorial:ℝ)/h^(K+1) := by
  obtain ⟨C₀,B₀,hC₀,hB₀,hcoeff⟩ := gammaRatioLog_coeff_gevrey_one a
  obtain ⟨C₁,B₁,hC₁,hB₁,hlog⟩ := gammaRatioLog_uniform_gevrey_error a ha
  obtain ⟨C₂,B₂,hC₂,hB₂,hfirst⟩ := gammaRatioLog_uniform_factorial_error a ha
  let c:ℝ := 1/(8*B₀)
  let h₀:ℝ := max 1 (8*B₀)
  let B:ℝ := B₁+2*B₀*Real.exp 1
  let C:ℝ := Real.exp (C₂+2*C₀)*C₁+2*Real.exp (2*C₀)
  refine ⟨C,B,c,h₀,by dsimp[C];positivity,by dsimp[B];positivity,
    by dsimp[c];positivity,lt_of_lt_of_le zero_lt_one (le_max_left _ _),?_⟩
  intro K h hh₀ hK
  have hh1:1≤h := (le_max_left _ _).trans hh₀
  have hh:0<h := lt_of_lt_of_le zero_lt_one hh1
  have hhB:8*B₀≤h := (le_max_right _ _).trans hh₀
  have hwindow:4*B₀*((K:ℝ)+1)≤h := by
    have hk:8*B₀*(K:ℝ)≤h := by
      have hk' : (K:ℝ)*(8*B₀)≤h := (le_div_iff₀ (by positivity:0<8*B₀)).mp
        (by simpa only [c,one_div,mul_comm,div_eq_mul_inv,one_mul] using hK)
      nlinarith
    nlinarith
  let L:ℝ := Real.log (Real.Gamma (h+(a:ℝ)))-Real.log (Real.Gamma h)-(a:ℝ)*Real.log h
  let P:ℝ := ∑i∈Finset.range (K+1),PowerSeries.coeff i (WP.HigherOrder.gammaRatioLog a)/h^i
  have hL:|L|≤C₂ := by
    have he:=hfirst 0 h hh
    simp only [Nat.zero_add,Finset.sum_range_one,PowerSeries.coeff_zero_eq_constantCoeff,
      WP.HigherOrder.gammaRatioLog_constant,zero_div,sub_zero,pow_zero,Nat.factorial_zero,
      Nat.cast_one,mul_one,pow_one] at he
    exact he.trans (div_le_self hC₂.le hh1)
  have hP:|P|≤2*C₀ := by
    have hz:‖((1/h:ℝ):ℂ)‖≤1/(2*B₀*((K:ℝ)+1)) := by
      rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos (by positivity)]
      apply one_div_le_one_div_of_le (by positivity)
      nlinarith
    have he:=truncatedSeriesPolynomial_norm_bound (WP.HigherOrder.gammaRatioLog a) C₀ B₀ hC₀.le hB₀ hcoeff K ((1/h:ℝ):ℂ) hz
    rw [truncatedSeriesPolynomial_real,Complex.norm_real,Real.norm_eq_abs] at he
    convert he using 1
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    rw [div_pow,one_pow,mul_one_div]
  have hLP:=exp_abs_sub_le (C₂+2*C₀) L P
    ((le_abs_self L).trans (hL.trans (by linarith)))
    ((le_abs_self P).trans (hP.trans (by linarith)))
  have hLerr:|L-P|≤C₁*B₁^(K+1)*((K+1).factorial:ℝ)/h^(K+1) := hlog K h hh
  have hE:=finiteExp_real_polynomial_remainder (WP.HigherOrder.gammaRatioLog a) C₀ B₀ hC₀.le hB₀
    (WP.HigherOrder.gammaRatioLog_constant a) hcoeff K h hh hwindow
  change |Real.exp P-∑i∈Finset.range (K+1),PowerSeries.coeff i (WP.HigherOrder.gammaRatioSeries a)/h^i|≤_ at hE
  calc
    _ ≤ |Real.exp L-Real.exp P|+|Real.exp P-∑i∈Finset.range (K+1),PowerSeries.coeff i (WP.HigherOrder.gammaRatioSeries a)/h^i| :=
      abs_sub_le _ _ _
    _ ≤ Real.exp (C₂+2*C₀)*(C₁*B₁^(K+1)*((K+1).factorial:ℝ)/h^(K+1))+
        2*Real.exp (2*C₀)*(2*B₀*Real.exp 1)^(K+1)*((K+1).factorial:ℝ)/h^(K+1) :=
      add_le_add (hLP.trans (mul_le_mul_of_nonneg_left hLerr (Real.exp_pos _).le)) hE
    _ ≤ Real.exp (C₂+2*C₀)*(C₁*B^(K+1)*((K+1).factorial:ℝ)/h^(K+1))+
        2*Real.exp (2*C₀)*B^(K+1)*((K+1).factorial:ℝ)/h^(K+1) := by
      have hb1 : B₁≤B := le_add_of_nonneg_right (by positivity)
      have hb2 : 2*B₀*Real.exp 1≤B := le_add_of_nonneg_left hB₁.le
      gcongr
    _ = _ := by dsimp[C];ring


lemma exp_gammaLogRatio_eq (a h:ℝ) (ha:0<a) (hh:0<h) :
    Real.exp (Real.log (Real.Gamma (h+a))-Real.log (Real.Gamma h)-a*Real.log h)=
      Real.Gamma (h+a)/(Real.Gamma h*h^a) := by
  rw [Real.exp_sub,Real.exp_sub,
    Real.exp_log (Real.Gamma_pos_of_pos (by linarith)),Real.exp_log (Real.Gamma_pos_of_pos hh),
    mul_comm a (Real.log h),←Real.rpow_def_of_pos hh]
  ring

lemma gammaRatio_uniform_gevrey_error (a:ℚ) (ha:0<a) :
    ∃C B c h₀:ℝ,0<C ∧ 0<B ∧ 0<c ∧ 0<h₀ ∧ ∀K:ℕ,∀h:ℝ,
      h₀≤h → (K:ℝ)≤c*h →
      |Real.Gamma (h+(a:ℝ))/(Real.Gamma h*h^(a:ℝ))-
        ∑i∈Finset.range (K+1),PowerSeries.coeff i (WP.HigherOrder.gammaRatioSeries a)/h^i|≤
        C*B^(K+1)*((K+1).factorial:ℝ)/h^(K+1) := by
  obtain ⟨C,B,c,h₀,hC,hB,hc,hh₀,herr⟩:=gammaRatioExp_uniform_gevrey_error a ha
  refine ⟨C,B,c,h₀,hC,hB,hc,hh₀,?_⟩
  intro K h hh hK
  have hp:0<h:=lt_of_lt_of_le hh₀ hh
  have haR:(0:ℝ)<a:=by exact_mod_cast ha
  rw [←exp_gammaLogRatio_eq (a:ℝ) h haR hp]
  exact herr K h hh hK

end WP.Analysis
