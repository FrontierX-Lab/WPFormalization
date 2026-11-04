import WPFormalization.Volumes.MarkedFourierBounds
import WPFormalization.Volumes.PointMassProof

/-! The actual marked Fourier tail on its variance scale, uniformly in the
cusp weight including its critical limit. A first half of the genuine planar
convolution power supplies the tail decay; the second half supplies the full
integral bound. Constants are chosen before genus, marking count, weight and
cutoff. The cutoff condition is T² ≤ h. This is a Fourier tail result, not a
local-limit or true-to-finite-model comparison theorem. -/
set_option maxHeartbeats 1500000
noncomputable section

namespace WP.Analysis
open Set
lemma critical_tail_power_exponential (H:ℕ) (h ε θ T:ℝ)
    (hh:0<h) (hH:h/4≤(H:ℝ)) (hε:0<ε)
    (hv:ℝ) (hvar:hv*ε^2≤2) (hangle:T^2≤h*hv*θ^2) (hT:T^2≤h):
    ((1+θ^2/(4*ε^2))^(-1/8:ℝ))^H≤Real.exp (-T^2/512):=by
  let q:ℝ:=T^2/(8*h)
  have hq0:0≤q:=by dsimp[q];positivity
  have hq1:q≤1:=by
    dsimp[q]
    apply (div_le_iff₀ (by positivity:0<8*h)).mpr
    nlinarith
  have hq:q≤θ^2/(4*ε^2):=by
    apply (div_le_div_iff₀ (by positivity:0<8*h) (by positivity:0<4*ε^2)).mpr
    have hvθ:=mul_le_mul_of_nonneg_right hvar (sq_nonneg θ)
    have htε:=mul_le_mul_of_nonneg_right hangle (sq_nonneg ε)
    nlinarith[mul_le_mul_of_nonneg_left hvθ hh.le]
  have hHp:0<(H:ℝ):=by linarith
  rw[←Real.rpow_natCast,←Real.rpow_mul (by positivity:0≤1+θ^2/(4*ε^2))]
  have hmono: (1+θ^2/(4*ε^2))^((-1/8:ℝ)*(H:ℝ))≤(1+q)^((-1/8:ℝ)*(H:ℝ)):=
    Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by nlinarith)
  apply hmono.trans
  rw[Real.rpow_def_of_pos (by positivity:0<1+q)]
  apply Real.exp_le_exp.mpr
  have hl:=log_one_add_half_lower q hq0 hq1
  have h1:=mul_le_mul_of_nonneg_left hl hHp.le
  have h2:=mul_le_mul_of_nonneg_right hH hq0
  have he:h*q=T^2/8:=by dsimp[q];field_simp <;>ring
  nlinarith

lemma half_base_tail_power_exponential (q:ℝ) (H:ℕ) (h T:ℝ)
    (hq0:0≤q) (hq:q≤1/2) (hh:0≤h) (hH:h/4≤(H:ℝ)) (hT:T^2≤h):
    q^H≤Real.exp (-(Real.log 2/4)*T^2):=by
  have hp:=pow_le_pow_left₀ hq0 hq H
  have he:(1/(2:ℝ))^H=Real.exp (-(H:ℝ)*Real.log 2):=by
    rw[neg_mul,Real.exp_neg,Real.exp_nat_mul,Real.exp_log (by norm_num),div_pow,one_pow]
    simp only[one_div]
  apply hp.trans
  rw[he]
  apply Real.exp_le_exp.mpr
  nlinarith[Real.log_pos (by norm_num:(1:ℝ)<2)]
end WP.Analysis

namespace WP.PositiveConvolution
open Set
lemma universalV_standardized_tail_power_bound (P:PsiTheory):
    ∃c:ℝ,0<c ∧ ∀(h:ℝ)(H:ℕ),0<h→h/4≤(H:ℝ)→
      ∀x∈Ioo (0:ℝ) xCritical,∀θ∈Icc (-Real.pi) Real.pi,
      ∀T:ℝ,T^2≤h→T^2≤h*euler Psi x*θ^2→
        ‖universalV P ((x:ℂ)*Complex.exp ((θ:ℂ)*Complex.I))/universalV P x‖^H≤
          Real.exp (-c*T^2):=by
  obtain ⟨δ,εA,hδ,hεA,hArc⟩:=Analysis.universalV_critical_small_arc_bound P
  obtain ⟨C₀,εO,hC₀,hεO,hεOh,hOut⟩:=universalV_outer_relative_bound P δ hδ
  obtain ⟨εV,hεV,hVar⟩:=eulerPsi_critical_upper
  let ε₀:ℝ:=min εA (min εO (min εV (min (1/(4*C₀^2)) (1/2))))
  have hε₀:0<ε₀:=by dsimp[ε₀];positivity
  have h0A:ε₀≤εA:=min_le_left _ _
  have h0O:ε₀≤εO:=(min_le_right _ _).trans (min_le_left _ _)
  have h0V:ε₀≤εV:=(min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have h0C:ε₀≤1/(4*C₀^2):=(min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have h0half:ε₀≤1/2:=(min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  let b:ℝ:=xCritical*(1-ε₀)
  have hb:0<b:=by dsimp[b];exact mul_pos Analysis.xCritical_pos_parameter (by linarith)
  have hbx:b<xCritical:=by dsimp[b];nlinarith[mul_pos Analysis.xCritical_pos_parameter hε₀]
  obtain ⟨B,K,hB,hK,hpars⟩:=compact_parameter_upper_bounds P b hb.le hbx
  let κ:ℝ:=2/(B^2*Real.pi^2)
  have hκ:0<κ:=by dsimp[κ];positivity
  let c:ℝ:=min (κ/(4*K)) (min (1/512) (Real.log 2/4))
  have hc:0<c:=by dsimp[c];exact lt_min (by positivity) (lt_min (by norm_num) (by positivity))
  have hcκ:c≤κ/(4*K):=min_le_left _ _
  have hc512:c≤1/512:=(min_le_right _ _).trans (min_le_left _ _)
  have hclog:c≤Real.log 2/4:=(min_le_right _ _).trans (min_le_right _ _)
  refine ⟨c,hc,?_⟩
  intro h H hh hH x hx θ hθ T hT hscale
  by_cases hxb:x≤b
  · have hv:euler Psi x≤K*x:=by
      have ht:deriv Psi x≤K:=(hpars x ⟨hx.1.le,hxb⟩).2
      dsimp[euler]
      nlinarith[mul_le_mul_of_nonneg_left ht hx.1.le]
    have htheta:|θ|≤Real.pi:=abs_le.mpr hθ
    have hg:=universalV_gaussian_point_bound P x B hx hB (hpars x ⟨hx.1.le,hxb⟩).1 θ htheta H
    apply hg.trans
    apply Real.exp_le_exp.mpr
    change -(κ*(H:ℝ)*x)*θ^2≤-c*T^2
    have hvscale:=mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hv (sq_nonneg θ)) hh.le
    have hHscale:=mul_le_mul_of_nonneg_right hH (mul_nonneg (mul_nonneg hK.le hx.1.le) (sq_nonneg θ))
    have hb:T^2≤4*K*((H:ℝ)*x*θ^2):=by nlinarith
    have hcoef:κ/(4*K)*T^2≤κ*((H:ℝ)*x*θ^2):=by
      have hm:=mul_le_mul_of_nonneg_left hb (div_nonneg hκ.le (by positivity:0≤4*K))
      have he:κ/(4*K)*(4*K*((H:ℝ)*x*θ^2))=κ*((H:ℝ)*x*θ^2):=by field_simp
      exact hm.trans_eq he
    have hsmall:=mul_le_mul_of_nonneg_right hcκ (sq_nonneg T)
    nlinarith
  · let ε:ℝ:=1-x/xCritical
    have hεp:0<ε:=by
      have hd:x/xCritical<1:=(div_lt_one Analysis.xCritical_pos_parameter).mpr hx.2
      dsimp[ε];linarith
    have he:xCritical*(1-ε)=x:=by dsimp[ε];field_simp[Analysis.xCritical_pos_parameter.ne'] <;>ring
    have hεlt:ε<ε₀:=by
      have ht:b<x:=lt_of_not_ge hxb
      have hd:xCritical*ε<xCritical*ε₀:=by dsimp[b] at ht;rw[←he] at ht;nlinarith
      exact (mul_lt_mul_iff_right₀ Analysis.xCritical_pos_parameter).mp hd
    by_cases hnear:|θ|≤δ
    · have ha:=hArc ε ⟨hεp,hεlt.trans_le h0A⟩ θ hnear
      simp only[Analysis.criticalRayPoint,Real.rpow_eq_pow] at ha
      rw[he] at ha
      have hp:=pow_le_pow_left₀ (norm_nonneg _) ha H
      have hv:euler Psi x*ε^2≤2:=by
        have ht:=hVar ε ⟨hεp,hεlt.trans_le h0V⟩
        rw[he] at ht
        exact (le_div_iff₀ (sq_pos_of_pos hεp)).mp ht
      have ht:=Analysis.critical_tail_power_exponential H h ε θ T hh hH hεp (euler Psi x) hv hscale hT
      exact (hp.trans ht).trans (Real.exp_le_exp.mpr (by nlinarith[sq_nonneg T]))
    · have ho:=hOut ε ⟨hεp,hεlt.trans_le h0O⟩ θ hθ (le_of_not_ge hnear)
      rw[he] at ho
      have hq:C₀*Real.sqrt ε≤1/2:=by
        have hb:ε*(4*C₀^2)≤1:=(le_div_iff₀ (by positivity)).mp (hεlt.le.trans h0C)
        have hs:(C₀*Real.sqrt ε)^2=C₀^2*ε:=by rw[mul_pow,Real.sq_sqrt hεp.le]
        have hp:0≤C₀*Real.sqrt ε:=by positivity
        nlinarith
      have ht:=Analysis.half_base_tail_power_exponential
        ‖universalV P ((x:ℂ)*Complex.exp ((θ:ℂ)*Complex.I))/universalV P x‖ H h T
        (norm_nonneg _) (ho.trans hq) hh.le hH hT
      exact ht.trans (Real.exp_le_exp.mpr (by nlinarith[sq_nonneg T]))
end WP.PositiveConvolution

namespace WP.PositiveConvolution
open Set MeasureTheory
lemma universalV_character_integral_scaled_bound (P:PsiTheory) (c₀:ℝ) (hc:0<c₀):
    ∃C:ℝ,0<C ∧ ∀h H:ℕ,1≤h→16≤H→c₀*(h:ℝ)≤H→
      ∀x∈Ioo (0:ℝ) xCritical,
      (∫θ:ℝ in (-Real.pi)..Real.pi,
        ‖universalV P ((x:ℂ)*Complex.exp ((θ:ℂ)*Complex.I))/universalV P x‖^H)*
          Real.sqrt ((h:ℝ)*euler Psi x)≤C:=by
  have harc:∃δ εA:ℝ,0<δ∧0<εA∧∀ε∈Ioo 0 εA,∀θ∈Icc (-Real.pi) Real.pi,
      |θ|≤δ→‖universalV P ((xCritical*(1-ε):ℝ)*Complex.exp ((θ:ℂ)*Complex.I))/
        universalV P ((xCritical*(1-ε):ℝ):ℂ)‖≤(1+θ^2/(4*ε^2))^(-1/8:ℝ):=by
    obtain ⟨δ,ε,hδ,hε,ha⟩:=Analysis.universalV_critical_small_arc_bound P
    refine ⟨δ,ε,hδ,hε,?_⟩
    intro ε' hε' θ hθ hnear
    simpa only[Analysis.criticalRayPoint,Real.rpow_eq_pow] using ha ε' hε' θ hnear
  obtain ⟨ε₀,Cc,hε₀,hεhalf,hCc,hcrit⟩:=critical_character_integral_scaled_bound_of_arc P c₀ hc harc
  let b:ℝ:=xCritical*(1-ε₀)
  have hb:0<b:=by dsimp[b];exact mul_pos Analysis.xCritical_pos_parameter (by linarith)
  have hbx:b<xCritical:=by dsimp[b];nlinarith[mul_pos Analysis.xCritical_pos_parameter hε₀]
  obtain ⟨Ci,hCi,hcomp⟩:=compact_character_integral_scaled_bound P c₀ b hc hb hbx
  refine ⟨max Ci Cc,hCi.trans_le (le_max_left _ _),?_⟩
  intro h H hh hH hrel x hx
  by_cases hxb:x≤b
  · exact (hcomp h H hh (by omega) hrel x ⟨hx.1,hxb⟩).trans (le_max_left _ _)
  · let ε:ℝ:=1-x/xCritical
    have hεp:0<ε:=by
      have hd:x/xCritical<1:=(div_lt_one Analysis.xCritical_pos_parameter).mpr hx.2
      dsimp[ε];linarith
    have he:xCritical*(1-ε)=x:=by dsimp[ε];field_simp[Analysis.xCritical_pos_parameter.ne'] <;>ring
    have hεlt:ε<ε₀:=by
      have ht:b<x:=lt_of_not_ge hxb
      have hd:xCritical*ε<xCritical*ε₀:=by dsimp[b] at ht;rw[←he] at ht;nlinarith
      exact (mul_lt_mul_iff_right₀ Analysis.xCritical_pos_parameter).mp hd
    have ht:=hcrit h H hh hH hrel ε ⟨hεp,hεlt⟩
    rw[he] at ht
    exact ht.trans (le_max_right _ _)
end WP.PositiveConvolution

namespace WP
open Set MeasureTheory
lemma marked_generating_fourier_tail_scaled (P:PsiTheory):
    ∃c C:ℝ,0<c ∧ 0<C ∧ ∀g p:ℕ,1≤p→Stable g p→32≤complexity g p→
      ∀x∈Ioo (0:ℝ) xCritical,∀T:ℝ,0≤T→T^2≤(complexity g p:ℝ)→
      let σ:=Real.sqrt ((complexity g p:ℝ)*euler Psi x)
      σ*(∫θ:ℝ in Ioc (-Real.pi) Real.pi ∩ {θ:ℝ | T≤σ*|θ|},
        ‖iteratedDeriv p (Phi P g) ((x:ℂ)*Complex.exp ((θ:ℂ)*Complex.I))/
          iteratedDeriv p (Phi P g) (x:ℂ)‖)≤C*Real.exp (-c*T^2):=by
  obtain ⟨c,hc,htail⟩:=PositiveConvolution.universalV_standardized_tail_power_bound P
  obtain ⟨C,hC,hfull⟩:=PositiveConvolution.universalV_character_integral_scaled_bound P (1/2) (by norm_num)
  refine ⟨c,C,hc,hC,?_⟩
  intro g p hp hs hlarge x hx T hT0 hT
  let h:ℕ:=complexity g p
  let h₁:ℕ:=h/2
  let h₂:ℕ:=h-h₁
  let σ:=Real.sqrt ((h:ℝ)*euler Psi x)
  let q:ℝ→ℝ:=fun θ=>‖universalV P ((x:ℂ)*Complex.exp ((θ:ℂ)*Complex.I))/universalV P x‖
  let f:ℝ→ℝ:=fun θ=>‖iteratedDeriv p (Phi P g) ((x:ℂ)*Complex.exp ((θ:ℂ)*Complex.I))/
      iteratedDeriv p (Phi P g) (x:ℂ)‖
  let A:Set ℝ:=Ioc (-Real.pi) Real.pi ∩ {θ:ℝ | T≤σ*|θ|}
  have hh:0<(h:ℝ):=by exact_mod_cast (show 0<h by dsimp[h];omega)
  have hv:0<euler Psi x:=mul_pos hx.1 (Analysis.Psi_deriv_pos_interior x ⟨hx.1.le,hx.2⟩)
  have hσ:0<σ:=Real.sqrt_pos.mpr (mul_pos hh hv)
  have hσsq:σ^2=(h:ℝ)*euler Psi x:=Real.sq_sqrt (mul_pos hh hv).le
  have h₁lower:(h:ℝ)/4≤h₁:=by
    have hn:h≤4*h₁:=by dsimp[h₁];dsimp[h] at *;omega
    have hn' : (h:ℝ)≤4*(h₁:ℝ):=by exact_mod_cast hn
    linarith
  have h₂lower:(1/2:ℝ)*(h:ℝ)≤h₂:=by
    have hn:h≤2*h₂:=by dsimp[h₂,h₁];omega
    have hn':(h:ℝ)≤2*(h₂:ℝ):=by exact_mod_cast hn
    linarith
  have h₂16:16≤h₂:=by dsimp[h₂,h₁];dsimp[h] at *;omega
  have hsplit:h=h₁+h₂:=by dsimp[h₂];omega
  have hcontq:Continuous q:=by
    exact ((PositiveConvolution.universalV_circle_continuous P x hx).div_const _).norm
  have hcontf:Continuous f:=by
    apply Continuous.norm
    apply Continuous.div_const
    rw[continuous_iff_continuousAt]
    intro θ
    have hn:‖(x:ℂ)*Complex.exp ((θ:ℂ)*Complex.I)‖<xCritical:=by
      rw[norm_mul,Complex.norm_of_nonneg hx.1.le,Complex.norm_exp_ofReal_mul_I,mul_one]
      exact hx.2
    exact (marked_generating_analytic_disk P g p _ (by simpa only[Metric.mem_ball,dist_zero_right] using hn)).continuousAt.comp
      (by fun_prop)
  have hab:-Real.pi≤Real.pi:=by linarith[Real.pi_pos]
  have hIf:IntegrableOn f (Ioc (-Real.pi) Real.pi):=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp (hcontf.intervalIntegrable _ _)
  have hIq:IntegrableOn (fun θ=>q θ^h₂) (Ioc (-Real.pi) Real.pi):=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp ((hcontq.pow h₂).intervalIntegrable _ _)
  have hA:MeasurableSet A:=measurableSet_Ioc.inter (isClosed_le continuous_const (by fun_prop)).measurableSet
  have hAs:A⊆Ioc (-Real.pi) Real.pi:=inter_subset_left
  have hpoint:∀θ∈A,f θ≤Real.exp (-c*T^2)*q θ^h₂:=by
    intro θ hθ
    have hθcc:θ∈Icc (-Real.pi) Real.pi:=⟨hθ.1.1.le,hθ.1.2⟩
    have hts:T^2≤(h:ℝ)*euler Psi x*θ^2:=by
      have ht:=pow_le_pow_left₀ hT0 hθ.2 2
      rw[mul_pow,sq_abs,hσsq] at ht
      exact ht
    have ht:=htail (h:ℝ) h₁ hh h₁lower x hx θ hθcc T hT hts
    have hnorm:‖(x:ℂ)*Complex.exp ((θ:ℂ)*Complex.I)‖=x:=by
      rw[norm_mul,Complex.norm_of_nonneg hx.1.le,Complex.norm_exp_ofReal_mul_I,mul_one]
    have hcirc:f θ≤q θ^h:=marked_generating_circle_domination P g p hp hs x hx _ hnorm
    have he:q θ^h=q θ^h₁*q θ^h₂:=by rw[←pow_add,←hsplit]
    rw[he] at hcirc
    exact hcirc.trans (mul_le_mul_of_nonneg_right ht (pow_nonneg (norm_nonneg _) _))
  have hInt:(∫θ:ℝ in A,f θ)≤Real.exp (-c*T^2)*(∫θ:ℝ in Ioc (-Real.pi) Real.pi,q θ^h₂):=by
    have hIe:IntegrableOn (fun θ=>Real.exp (-c*T^2)*q θ^h₂) (Ioc (-Real.pi) Real.pi):=
      hIq.const_mul (Real.exp (-c*T^2))
    have hi:=setIntegral_mono_on (hIf.mono_set hAs)
      (hIe.mono_set hAs) hA hpoint
    rw[integral_const_mul] at hi
    have hsInt:(∫θ:ℝ in A,q θ^h₂)≤∫θ:ℝ in Ioc (-Real.pi) Real.pi,q θ^h₂:=
      setIntegral_mono_set hIq (Filter.Eventually.of_forall (fun θ=>pow_nonneg (norm_nonneg _) _))
        (Filter.Eventually.of_forall (fun θ hθ=>hAs hθ))
    exact hi.trans (mul_le_mul_of_nonneg_left hsInt (Real.exp_pos _).le)
  have hI: (∫θ:ℝ in Ioc (-Real.pi) Real.pi,q θ^h₂)*σ≤C:=by
    have ht:=hfull h h₂ (by dsimp[h];omega) h₂16 h₂lower x hx
    rw[intervalIntegral.integral_of_le hab] at ht
    exact ht
  have hfinal:=mul_le_mul_of_nonneg_left hInt hσ.le
  calc
    _≤σ*(Real.exp (-c*T^2)*(∫θ:ℝ in Ioc (-Real.pi) Real.pi,q θ^h₂)):=hfinal
    _=Real.exp (-c*T^2)*((∫θ:ℝ in Ioc (-Real.pi) Real.pi,q θ^h₂)*σ):=by ring
    _≤Real.exp (-c*T^2)*C:=mul_le_mul_of_nonneg_left hI (Real.exp_pos _).le
    _=_:=by ring
end WP
