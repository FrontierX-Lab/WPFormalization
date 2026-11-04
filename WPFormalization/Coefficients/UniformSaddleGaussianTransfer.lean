import WPFormalization.Analysis.ScaledGaussianModelError
import WPFormalization.Analysis.CharacteristicL1Split
/-! Faithful uniform saddle estimate for the actual unscaled H(0) kernel: GaussianTransfer. -/
noncomputable section
namespace WP.Coefficients
open Set Filter MeasureTheory
open scoped Topology
open WP.Analysis
lemma gaussian_dominated_uniform_tail (χ:ℝ→ℂ)(hχ:Integrable χ)(c T:ℝ)(hc:0<c)(hT:0≤ T)
    (hb:∀t:ℝ,‖χ t‖≤ Real.exp (-c*t^2)):
    (∫t:ℝ in {t:ℝ|T≤|t|},‖χ t‖)≤ Real.sqrt (2*Real.pi/c)*Real.exp (-c*T^2/2):=by
  let E:ℝ:=Real.exp (-c*T^2/2)
  have hg:Integrable (fun t:ℝ=>E*Real.exp (-(c/2)*t^2)):=
    (integrable_exp_neg_mul_sq (half_pos hc)).const_mul E
  have hset:MeasurableSet {t:ℝ|T≤|t|}:=(isClosed_le continuous_const continuous_abs).measurableSet
  have hm:=setIntegral_mono_on hχ.norm.integrableOn hg.integrableOn hset (fun t ht=>by
    apply (hb t).trans
    rw[←Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hs:T^2≤ t^2:=by
      have ht':T≤|t|:=ht
      nlinarith[sq_abs t]
    nlinarith)
  have htotal:(∫t:ℝ in {t:ℝ|T≤|t|},E*Real.exp (-(c/2)*t^2))≤∫t:ℝ,E*Real.exp (-(c/2)*t^2):=
    setIntegral_le_integral hg (ae_of_all _ (fun t=>by dsimp[E];positivity))
  apply (hm.trans htotal).trans_eq
  rw[integral_const_mul,integral_gaussian]
  have he:Real.pi/(c/2)=2*Real.pi/c:=by ring
  rw[he]
  exact mul_comm _ _
lemma gaussian_central_positive_of_uniform_charts (ρ c:ℝ)(hρ:0<ρ)(hc:0<c):
    ∃H:ℝ,0<H ∧ ∀h:ℝ,H≤ h→∀(χ:ℝ→ℂ)(L:ℂ→ℂ)(a:ℝ),
      Integrable χ→(∀t:ℝ,‖χ t‖≤ Real.exp (-c*t^2))→
      AnalyticOnNhd ℂ L (Metric.ball 0 (ρ*Real.sqrt h))→
      L 0=0→WP.coeff L 1=0→WP.coeff L 2=(1/2:ℂ)→
      (∀w:ℂ,‖w‖<ρ*Real.sqrt h→‖L w‖≤‖w‖^2)→
      (∀t:ℝ,|t|<ρ*Real.sqrt h→χ t=Complex.exp (L ((t:ℂ)*Complex.I)))→
      (a:ℂ)=((2*Real.pi:ℝ):ℂ)⁻¹*∫t:ℝ,χ t→
      1/(2*Real.sqrt (2*Real.pi))≤ a:=by
  let E:ℝ:=Real.pi/Real.sqrt (2*Real.pi)
  have hE:0<E:=by dsimp[E];positivity
  have hpow:Tendsto (fun T:ℝ=>T^2) atTop atTop:=tendsto_pow_atTop (by norm_num)
  have he₁:Tendsto (fun T:ℝ=>Real.sqrt (2*Real.pi/c)*Real.exp (-c*T^2/2)) atTop (𝓝 0):=by
    have ht:=(Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (hpow.const_mul_atTop (half_pos hc))).const_mul (Real.sqrt (2*Real.pi/c))
    convert ht using 1
    · funext T
      congr 2
      ring
    · simp
  have he₂:Tendsto (fun T:ℝ=>Real.sqrt (8*Real.pi)*Real.exp (-T^2/4)) atTop (𝓝 0):=by
    have ht:=(Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (hpow.const_mul_atTop (by norm_num:(0:ℝ)<1/4))).const_mul (Real.sqrt (8*Real.pi))
    convert ht using 1
    · funext T
      congr 2
      ring
    · simp
  have he:Tendsto (fun T:ℝ=>Real.sqrt (2*Real.pi/c)*Real.exp (-c*T^2/2)+
      Real.sqrt (8*Real.pi)*Real.exp (-T^2/4)) atTop (𝓝 0):=by
    simpa only[add_zero] using he₁.add he₂
  obtain ⟨T,hT,hcut⟩:=((eventually_ge_atTop (1:ℝ)).and
    (he.eventually (gt_mem_nhds (half_pos hE)))).exists
  have hTp:0<T:=zero_lt_one.trans_le hT
  let ε:ℝ:=E/(4*T)
  have hε:0<ε:=by dsimp[ε];positivity
  let b:ℝ:=max 1 (max (32*T/ρ) (max (4*T^3/ρ) ((8*T^3+4*T)/(ρ*ε))))
  have hb1:1≤ b:=le_max_left _ _
  have hb:0<b:=zero_lt_one.trans_le hb1
  refine ⟨b^2,sq_pos_of_pos hb,?_⟩
  intro h hh χ L a hχ hbound hLa hL0 hL1 hL2 hbL htrace hinv
  have hh0:0<h:=(sq_pos_of_pos hb).trans_le hh
  have hs:0<Real.sqrt h:=Real.sqrt_pos.mpr hh0
  have hbs:b≤ Real.sqrt h:=by nlinarith[Real.sq_sqrt hh0.le]
  have hwindow:32*T≤ρ*Real.sqrt h:=by
    have ht:=(div_le_iff₀ hρ).mp (((le_max_left _ _).trans (le_max_right _ _)).trans hbs)
    simpa only[mul_comm] using ht
  have hsmall:4*T^3/(ρ*Real.sqrt h)≤1:=by
    apply (div_le_one (mul_pos hρ hs)).mpr
    have ht:4*T^3/ρ≤ Real.sqrt h:=
      ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans hbs
    simpa only[mul_comm] using (div_le_iff₀ hρ).mp ht
  have herror:(8*T^3+4*T)/(ρ*Real.sqrt h)≤ε:=by
    have ht:(8*T^3+4*T)/(ρ*ε)≤ Real.sqrt h:=
      ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans hbs
    apply (div_le_iff₀ (mul_pos hρ hs)).mpr
    have ht':8*T^3+4*T≤ Real.sqrt h*(ρ*ε):=(div_le_iff₀ (mul_pos hρ hε)).mp ht
    nlinarith
  have hcore:∀t:ℝ,|t|≤ T→‖χ t-Complex.exp (-(t:ℂ)^2/2)‖≤ε:=by
    intro t ht
    have htr:|t|<ρ*Real.sqrt h:=by nlinarith
    rw[htrace t htr]
    have hp:=scaled_gaussian_model_core_error L (fun _=>1) ρ 1 1 h T hρ (by norm_num) (by norm_num) hh0 hT
      hwindow (by simpa only[mul_one,one_mul] using hsmall) hLa (fun _ _=>analyticAt_const)
      hL0 hL1 hL2 rfl (by simpa only[one_mul] using hbL) (by intro w hw;simp) t ht
    simp only[mul_one,one_mul] at hp
    exact hp.trans herror
  have htχ:=gaussian_dominated_uniform_tail χ hχ c T hc hTp.le hbound
  have htg:=gaussian_characteristic_uniform_tail T hTp.le
  have hl1: (∫t:ℝ,‖χ t-Complex.exp (-(t:ℂ)^2/2)‖)≤ E:=by
    have ht:=l1_error_from_core_and_tails χ _ hχ gaussian_characteristic_integrable T ε _ _ hTp.le hcore htχ htg
    have htε:2*T*ε=E/2:=by dsimp[ε];field_simp;ring
    rw[htε] at ht
    linarith
  have hi:(a:ℂ)=((2*Real.pi:ℝ):ℂ)⁻¹*∫t:ℝ,Complex.exp (-(0:ℂ)*(t:ℂ)*Complex.I)*χ t:=by
    simpa only[neg_zero,zero_mul,Complex.exp_zero,one_mul] using hinv
  have ht:=gaussian_lattice_error_of_fourier_l1 χ hχ 0 a E hi hl1
  simp only[zero_pow (by norm_num:2≠0),neg_zero,zero_div,Real.exp_zero] at ht
  have hdiv:E/(2*Real.pi)=1/(2*Real.sqrt (2*Real.pi)):=by dsimp[E];field_simp
  rw[hdiv] at ht
  have hnum:1/Real.sqrt (2*Real.pi)=2*(1/(2*Real.sqrt (2*Real.pi))):=by ring
  rw[hnum] at ht
  linarith[neg_le_of_abs_le ht]
end WP.Coefficients
