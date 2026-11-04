import WPFormalization.Analysis.GaussianGevreyTails
/-! Fixed-order stationary-phase Taylor integration on a moving real interval.
The Cauchy radius is R/(1+|w|), and the actual Gaussian majorant is integrable.
An analytic correction vanishing at zero supplies the common Cauchy family;
no asymptotic coefficient identity is assumed or asserted. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace WP.Analysis
lemma gaussian_shifted_absolute_power_integrable (N:ℕ) :
    Integrable (fun w:ℝ=>(1+|w|)^N*Real.exp (-(1/4:ℝ)*w^2)) := by
  have hterm(i:ℕ):Integrable (fun w:ℝ=>(|w|^i*Real.exp (-(1/4:ℝ)*w^2))*(N.choose i:ℝ)) := by
    have hi:Integrable (fun w:ℝ=>|w|^i*Real.exp (-(1/4:ℝ)*w^2)) := by
      simpa only [Real.norm_eq_abs,abs_mul,abs_pow,abs_of_pos (Real.exp_pos _)] using
        (gaussian_monomial_integrable (1/4) (by norm_num) i).norm
    exact hi.mul_const _
  have he:(fun w:ℝ=>(1+|w|)^N*Real.exp (-(1/4:ℝ)*w^2))=
      (fun w:ℝ=>∑i ∈ Finset.range (N+1),(|w|^i*Real.exp (-(1/4:ℝ)*w^2))*(N.choose i:ℝ)) := by
    funext w
    rw [add_comm (1:ℝ),add_pow,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [one_pow,mul_one]
    ring
  rw [he]
  exact integrable_finsetSum _ (fun i hi=>hterm i)

lemma stationary_fixed_taylor_integral_bound (F:ℝ → ℂ → ℂ) (M R τ:ℝ)
    (hM:0 ≤ M) (hR:0<R) (hτ:0<τ) (hτR:τ ≤ R/4)
    (hF:∀w,DifferentiableOn ℂ (F w) (Metric.closedBall 0 (R/(1+|w|))))
    (hbound:∀w z,z ∈ Metric.sphere (0:ℂ) (R/(1+|w|)) →
      ‖F w z‖ ≤ M*Real.exp (w^2/4)) (N:ℕ) :
    ‖∫w:ℝ in Icc (-(R/(4*τ))) (R/(4*τ)),Real.exp (-(1/2:ℝ)*w^2) •
      (F w (τ:ℂ)-∑n ∈ Finset.range N,WP.coeff (F w) n*(τ:ℂ)^n)‖ ≤
      2*M*(τ/R)^N*(∫w:ℝ,(1+|w|)^N*Real.exp (-(1/4:ℝ)*w^2)) := by
  let A:ℝ:=2*M*(τ/R)^N
  let g:ℝ → ℝ:=fun w=>(1+|w|)^N*Real.exp (-(1/4:ℝ)*w^2)
  have hA:0 ≤ A := by dsimp[A];positivity
  have hg:Integrable (fun w=>A*g w) := (gaussian_shifted_absolute_power_integrable N).const_mul A
  have hp(w:ℝ)(hw:w ∈ Icc (-(R/(4*τ))) (R/(4*τ))):
      ‖Real.exp (-(1/2:ℝ)*w^2) •
        (F w (τ:ℂ)-∑n ∈ Finset.range N,WP.coeff (F w) n*(τ:ℂ)^n)‖ ≤ A*g w := by
    have hwabs:|w| ≤ R/(4*τ) := abs_le.mpr ⟨by linarith[hw.1],hw.2⟩
    have hwprod:τ* |w| ≤ R/4 := by
      have hh:|w| *(4*τ) ≤ R := (le_div_iff₀ (by positivity)).mp hwabs
      nlinarith
    have hs:0<1+|w| := by positivity
    have hrad:0<R/(1+|w|) := div_pos hR hs
    have hsmall:‖(τ:ℂ)‖ ≤ (R/(1+|w|))/2 := by
      rw [Complex.norm_of_nonneg hτ.le,div_div]
      apply (le_div_iff₀ (by positivity)).mpr
      nlinarith
    have hb:=complex_taylor_remainder_bound (F w) (R/(1+|w|)) (M*Real.exp (w^2/4))
      hrad (by positivity) (hF w) (hbound w) N (τ:ℂ) hsmall
    rw [Complex.norm_of_nonneg hτ.le] at hb
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
    apply (mul_le_mul_of_nonneg_left hb (Real.exp_pos _).le).trans_eq
    have hratio:τ/(R/(1+|w|))=(τ/R)*(1+|w|) := by field_simp
    rw [hratio,mul_pow]
    have hexp:Real.exp (-(1/2:ℝ)*w^2)*Real.exp (w^2/4)=Real.exp (-(1/4:ℝ)*w^2) := by
      rw [←Real.exp_add]
      congr 1
      ring
    dsimp only [A,g]
    calc _ = 2*M*(τ/R)^N*(1+|w|)^N*(Real.exp (-(1/2:ℝ)*w^2)*Real.exp (w^2/4)) := by ring
         _ = _ := by rw [hexp];ring
  have hb:=norm_integral_le_of_norm_le hg.integrableOn (ae_restrict_of_forall_mem measurableSet_Icc hp)
  have hs:(∫w:ℝ in Icc (-(R/(4*τ))) (R/(4*τ)),A*g w) ≤ ∫w:ℝ,A*g w :=
    setIntegral_le_integral hg (Filter.Eventually.of_forall (fun w=>by dsimp only[g];positivity))
  exact (hb.trans hs).trans_eq (by rw [integral_const_mul])
lemma stationary_phase_cauchy_family (β a:ℂ → ℂ)
    (hβ:AnalyticAt ℂ β 0) (ha:AnalyticAt ℂ a 0) (hβ0:β 0=0) :
    ∃R M:ℝ,0<R ∧ 0<M ∧
      (∀w:ℝ,DifferentiableOn ℂ
        (fun τ:ℂ=>Complex.exp ((w:ℂ)^2*β (τ*(w:ℂ)))*a (τ*(w:ℂ)))
          (Metric.closedBall 0 (R/(1+|w|)))) ∧
      ∀w:ℝ,∀z ∈ Metric.sphere (0:ℂ) (R/(1+|w|)),
        ‖Complex.exp ((w:ℂ)^2*β (z*(w:ℂ)))*a (z*(w:ℂ))‖ ≤ M*Real.exp (w^2/4) := by
  let M:ℝ:=‖a 0‖+1
  have hM:0<M := by dsimp[M];positivity
  have hβb:∀ᶠz:ℂ in nhds 0,‖β z‖<1/4 := by
    have h0:‖β 0‖<(1/4:ℝ) := by simp [hβ0]
    exact hβ.continuousAt.norm.tendsto.eventually (eventually_lt_nhds h0)
  have hab:∀ᶠz:ℂ in nhds 0,‖a z‖<M :=
    ha.continuousAt.norm.tendsto.eventually (eventually_lt_nhds (by change ‖a 0‖ < ‖a 0‖+1;linarith))
  have hloc:∀ᶠz:ℂ in nhds 0,
      AnalyticAt ℂ β z ∧ AnalyticAt ℂ a z ∧ ‖β z‖ ≤ 1/4 ∧ ‖a z‖ ≤ M := by
    filter_upwards [hβ.eventually_analyticAt,ha.eventually_analyticAt,hβb,hab] with z h1 h2 h3 h4
    exact ⟨h1,h2,h3.le,h4.le⟩
  obtain ⟨ρ,hρ,hball⟩:=Metric.eventually_nhds_iff.mp hloc
  let R:ℝ:=ρ/2
  have hR:0<R := half_pos hρ
  have hRp:R<ρ := by dsimp[R];linarith
  have hpoint(w:ℝ)(z:ℂ)(hz:‖z‖ ≤ R/(1+|w|)):
      ‖z*(w:ℂ)‖<ρ := by
    have hs:0<1+|w| := by positivity
    have h1:(R/(1+|w|))* |w| ≤ R := by
      rw [div_mul_eq_mul_div]
      apply (div_le_iff₀ hs).mpr
      nlinarith
    calc _ = ‖z‖* |w| := by rw [norm_mul,Complex.norm_real,Real.norm_eq_abs]
         _ ≤ (R/(1+|w|))* |w| := mul_le_mul_of_nonneg_right hz (abs_nonneg _)
         _ < ρ := h1.trans_lt hRp
  refine ⟨R,M,hR,hM,?_,?_⟩
  · intro w z hz
    have hzz:=hpoint w z (show ‖z‖ ≤ R/(1+|w|) from by simpa only [Metric.mem_closedBall,dist_zero_right] using hz)
    have ht:=hball (by simpa only [dist_zero_right] using hzz)
    have hm:AnalyticAt ℂ (fun τ:ℂ=>τ*(w:ℂ)) z := analyticAt_id.mul analyticAt_const
    have hbcomp:AnalyticAt ℂ (fun τ:ℂ=>β (τ*(w:ℂ))) z :=
      AnalyticAt.comp (f:=fun τ:ℂ=>τ*(w:ℂ)) (x:=z) ht.1 hm
    have hacomp:AnalyticAt ℂ (fun τ:ℂ=>a (τ*(w:ℂ))) z :=
      AnalyticAt.comp (f:=fun τ:ℂ=>τ*(w:ℂ)) (x:=z) ht.2.1 hm
    exact (((analyticAt_const.mul hbcomp).cexp).mul hacomp).differentiableAt.differentiableWithinAt
  · intro w z hz
    have hzz:=hpoint w z (show ‖z‖ ≤ R/(1+|w|) from by simpa only [Metric.mem_sphere,dist_zero_right] using le_of_eq hz)
    have ht:=hball (by simpa only [dist_zero_right] using hzz)
    have he:(((w:ℂ)^2*β (z*(w:ℂ))).re) ≤ w^2/4 := by
      calc _ ≤ ‖(w:ℂ)^2*β (z*(w:ℂ))‖ := Complex.re_le_norm _
           _ = w^2*‖β (z*(w:ℂ))‖ := by rw [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs]
           _ ≤ _ := by nlinarith [ht.2.2.1,sq_nonneg w]
    rw [norm_mul,Complex.norm_exp]
    calc _ ≤ Real.exp (w^2/4)*M := mul_le_mul (Real.exp_le_exp.mpr he) ht.2.2.2
          (norm_nonneg _) (Real.exp_pos _).le
         _ = _ := by ring
end WP.Analysis
