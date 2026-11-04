import WPFormalization.HigherOrder.PoissonMomentRemainder
import WPFormalization.HigherOrder.PoissonTaylorRemainder
/-! The actual Poisson Taylor error at every order, including k=0.
This proves the Gaussian-moment part D.21; retained moments above inverse
order K still require a separate finite tail estimate. -/
noncomputable section
namespace WP.HigherOrder
open MeasureTheory
open scoped Topology

lemma poissonCoefficientOperator_sub (h : ℝ) (k : ℕ) (f g : ℂ → ℂ)
    (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0) :
    poissonCoefficientOperator h k (fun u=>f u-g u)=
      poissonCoefficientOperator h k f-poissonCoefficientOperator h k g := by
  have he : (fun u : ℂ=>Complex.exp ((h:ℂ)*u)*(f u-g u))=
      (fun u : ℂ=>Complex.exp ((h:ℂ)*u)*f u-Complex.exp ((h:ℂ)*u)*g u) := by funext u;ring
  unfold poissonCoefficientOperator
  have hexp : AnalyticAt ℂ (fun u : ℂ=>Complex.exp ((h:ℂ)*u)) 0 := by fun_prop
  rw [he,←Analysis.taylor_coeff,Analysis.taylor_sub (f:=fun u : ℂ=>Complex.exp ((h:ℂ)*u)*f u) (g:=fun u : ℂ=>Complex.exp ((h:ℂ)*u)*g u) (hexp.mul hf) (hexp.mul hg),map_sub]
  simp only [Analysis.taylor_coeff]
  ring

lemma poisson_peak_sqrt_gaussian (k : ℕ) (hk : 1 ≤ k) :
    Analysis.poissonPeakInverse k*Real.sqrt (Real.pi^3/(k:ℝ)) ≤
      Real.exp 1*Real.sqrt (Real.pi^3) := by
  have hkp : 0 < (k:ℝ) := by exact_mod_cast hk
  calc _ ≤ (Real.exp 1*Real.sqrt (k:ℝ))*Real.sqrt (Real.pi^3/(k:ℝ)) :=
          mul_le_mul_of_nonneg_right (Analysis.poissonPeakInverse_le k hk) (Real.sqrt_nonneg _)
       _ = _ := by
        rw [mul_assoc,←Real.sqrt_mul hkp.le,mul_div_cancel₀ _ hkp.ne']

lemma poisson_taylor_moment_scalar (h R M : ℝ) (hh : 0 < h) (hR : 0 < R)
    (hM : 0 ≤ M) (k N : ℕ) (hk : 1 ≤ k) :
    Analysis.poissonPeakInverse k/(2*Real.pi)*(2*M*(2*((k:ℝ)/h)/R)^(2*N))*(N.factorial:ℝ)*
      (Real.pi^2/(k:ℝ))^N*Real.sqrt (Real.pi^3/(k:ℝ)) ≤
      (Real.exp 1*Real.sqrt (Real.pi^3)/(2*Real.pi))*(2*M)*
        (4*Real.pi^2/R^2)^N*(N.factorial:ℝ)*((k:ℝ)/h)^N/h^N := by
  have hkp : 0 < (k:ℝ) := by exact_mod_cast hk
  have hbase : (2*((k:ℝ)/h)/R)^2*(Real.pi^2/(k:ℝ))=
      (4*Real.pi^2/R^2)*((k:ℝ)/h)/h := by field_simp;ring
  have he : Analysis.poissonPeakInverse k/(2*Real.pi)*(2*M*(2*((k:ℝ)/h)/R)^(2*N))*(N.factorial:ℝ)*
      (Real.pi^2/(k:ℝ))^N*Real.sqrt (Real.pi^3/(k:ℝ))=
        (Analysis.poissonPeakInverse k*Real.sqrt (Real.pi^3/(k:ℝ)))/(2*Real.pi)*
          (2*M)*(N.factorial:ℝ)*(((2*((k:ℝ)/h)/R)^2)*(Real.pi^2/(k:ℝ)))^N := by
    rw [mul_pow,←pow_mul]
    ring
  rw [he,hbase]
  calc _ ≤ (Real.exp 1*Real.sqrt (Real.pi^3)/(2*Real.pi))*(2*M)*(N.factorial:ℝ)*
          ((4*Real.pi^2/R^2)*((k:ℝ)/h)/h)^N := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            exact div_le_div_of_nonneg_right (poisson_peak_sqrt_gaussian k hk) (by positivity)
       _ = _ := by rw [div_pow,mul_pow];ring

lemma poissonCoefficientOperator_taylor_error_positive (h R M : ℝ) (hh : 0 < h)
    (hR : 0 < R) (hM : 0 ≤ M) (k N : ℕ) (hk : 1 ≤ k)
    (hν : (k:ℝ)/h ≤ R/8) (f : ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall 0 R))
    (hb : ∀z∈Metric.closedBall (0:ℂ) R,‖f z‖ ≤ M) :
    ‖poissonCoefficientOperator h k f-
      ∑m∈Finset.range (2*N),WP.coeff (fun z=>f ((k:ℂ)/(h:ℂ)+z)) m*
        ((((poissonCentralPolynomial m).eval (k:ℝ):ℝ):ℂ)/(h:ℂ)^m)‖ ≤
      (Real.exp 1*Real.sqrt (Real.pi^3)/(2*Real.pi))*(2*M)*
        (4*Real.pi^2/R^2)^N*(N.factorial:ℝ)*((k:ℝ)/h)^N/h^N := by
  let ν : ℝ := (k:ℝ)/h
  let T : ℂ → ℂ := poissonTaylorPolynomial f ((k:ℂ)/(h:ℂ)) (2*N)
  let r : ℂ → ℂ := fun u=>f u-T u
  have hν0 : 0 ≤ ν := by dsimp [ν];positivity
  have hνR : (k:ℝ)/h < R := by linarith
  have hfr : AnalyticOnNhd ℂ r (Metric.ball 0 R) := by
    intro z hz
    exact (hf z (Metric.ball_subset_closedBall hz)).sub (poissonTaylorPolynomial_analytic f _ _ z)
  have hcircle (θ : ℝ) (hθ : θ∈Set.Icc (-Real.pi) Real.pi) :
      ‖r ((ν:ℂ)*Complex.exp ((θ:ℂ)*Complex.I))‖ ≤ (2*M*(2*ν/R)^(2*N))*θ^(2*N) := by
    have ht := poissonTaylorRemainder_circle_bound R M ν hR hM hν0 hν f hf hb N θ
    simpa only [r,T,ν,Complex.ofReal_div,Complex.ofReal_natCast] using ht
  have ht := poissonCoefficientOperator_circle_moment_bound h R (2*M*(2*ν/R)^(2*N)) hh hR
    (by positivity) k N hk hνR r hfr hcircle
  have hf0 : AnalyticAt ℂ f 0 := hf 0 (by simp [hR.le])
  rw [poissonCoefficientOperator_sub h k f T hf0 (poissonTaylorPolynomial_analytic f _ _ 0),
    poissonCoefficientOperator_taylor h hh.ne'] at ht
  exact ht.trans (poisson_taylor_moment_scalar h R M hh hR hM k N hk)

lemma poissonTaylorPolynomial_at_center (f : ℂ → ℂ) (ν : ℂ) (N : ℕ) (hN : 1 ≤ N) :
    poissonTaylorPolynomial f ν N ν=f ν := by
  unfold poissonTaylorPolynomial
  rw [Finset.sum_eq_single 0]
  · simp [WP.coeff]
  · intro i hi hi0
    simp [show i≠0 by omega]
  · intro hn
    exfalso
    exact hn (Finset.mem_range.mpr (by omega))

lemma poissonCoefficientOperator_taylor_error (h R M : ℝ) (hh : 0 < h)
    (hR : 0 < R) (hM : 0 ≤ M) (k N : ℕ) (hN : 1 ≤ N)
    (hν : (k:ℝ)/h ≤ R/8) (f : ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall 0 R))
    (hb : ∀z∈Metric.closedBall (0:ℂ) R,‖f z‖ ≤ M) :
    ‖poissonCoefficientOperator h k f-
      ∑m∈Finset.range (2*N),WP.coeff (fun z=>f ((k:ℂ)/(h:ℂ)+z)) m*
        ((((poissonCentralPolynomial m).eval (k:ℝ):ℝ):ℂ)/(h:ℂ)^m)‖ ≤
      (Real.exp 1*Real.sqrt (Real.pi^3)/(2*Real.pi))*(2*M)*
        (4*Real.pi^2/R^2)^N*(N.factorial:ℝ)*((k:ℝ)/h)^N/h^N := by
  by_cases hk : 1 ≤ k
  · exact poissonCoefficientOperator_taylor_error_positive h R M hh hR hM k N hk hν f hf hb
  · have hk0 : k=0 := by omega
    subst k
    rw [←poissonCoefficientOperator_taylor h hh.ne',poissonCoefficientOperator_zero,
      poissonCoefficientOperator_zero]
    simp only [Nat.cast_zero,zero_div]
    rw [poissonTaylorPolynomial_at_center f 0 (2*N) (by omega),sub_self,norm_zero]
    positivity

end WP.HigherOrder
