import WPFormalization.Volumes.MarkedCharacteristicCore
import WPFormalization.Volumes.MarkedScaledFourierTail
import WPFormalization.Analysis.GaussianCorePolynomialBound
import WPFormalization.Analysis.LogarithmicGaussianCutoff
import WPFormalization.Analysis.CharacteristicL1Split
/-! A uniform polynomial L1 Gaussian error for the actual marked
characteristic function. The proved global analytic charts, the actual
8.2 real remainder, the actual Fourier tail, and one logarithmic cutoff
are all instantiated. Constants precede every genus and physical weight. -/
noncomputable section
namespace WP
open Set Filter Complex MeasureTheory
open scoped Topology
set_option autoImplicit false
set_option maxHeartbeats 2000000

lemma marked_characteristic_quantitative_l1 (P:PsiTheory)(p:ℕ)(hp:1≤p):
    ∃C κ M₀:ℝ,0<C ∧ 0<κ ∧ 0<M₀ ∧
      ∀g:ℕ,∀x∈Ioo (0:ℝ) xCritical,
        let h:ℝ:=complexity g p
        let m:ℝ:=min h (h*Psi x)
        M₀≤ m→(∫t:ℝ,‖scaledMarkedFourier P g p x t-Complex.exp (-(t:ℂ)^2/2)‖)≤C*m^(-κ):=by
  obtain ⟨ρ,C,D,E,H,hρ,hC,hD,hE,hH,hcore⟩:=marked_characteristic_gaussian_core_bound P p hp
  obtain ⟨ct,Ct,hct,hCt,htail⟩:=scaledMarkedFourier_uniform_tail P
  let A:ℝ:=4*D*Real.sqrt E+(8*C*D+4*D)/ρ
  have hA:0<A:=by dsimp[A];positivity
  let B:ℝ:=256*C
  have hB:0<B:=by dsimp[B];positivity
  let c:ℝ:=min ct (1/4)
  have hc:0<c:=lt_min hct (by norm_num)
  have hcct:c≤ct:=min_le_left _ _
  have hcq:c≤1/4:=min_le_right _ _
  obtain ⟨a,ha,ha1,hcut⟩:=Analysis.logarithmic_gaussian_cutoff_core_rate B hB.le
  let r:ℝ:=min (ρ/32) 1
  have hr:0<r:=lt_min (by positivity) zero_lt_one
  have hrρ:r≤ρ/32:=min_le_left _ _
  have hr1:r≤1:=min_le_right _ _
  have hQ:0<4*C/ρ:=by positivity
  have hwin:=Analysis.logarithmic_gaussian_cutoff_window a r (4*C/ρ) ha ha1 hr hQ
  obtain ⟨Hcut,hcutoff⟩:=eventually_atTop.mp (hcut.and hwin)
  let M₀:ℝ:=max (max H 32) (max Hcut 1)
  have hM₀H:H≤M₀:=(le_max_left H 32).trans (le_max_left _ _)
  have hM₀32:32≤M₀:=(le_max_right H 32).trans (le_max_left _ _)
  have hM₀cut:Hcut≤M₀:=(le_max_left Hcut 1).trans (le_max_right _ _)
  have hM₀1:1≤M₀:=(le_max_right Hcut 1).trans (le_max_right _ _)
  let κ:ℝ:=min (1/4) (c*a)
  have hκ:0<κ:=lt_min (by norm_num) (mul_pos hc ha)
  have hκq:κ≤1/4:=min_le_left _ _
  have hκca:κ≤c*a:=min_le_right _ _
  let Ctotal:ℝ:=32*A+Ct+Real.sqrt (8*Real.pi)
  have hCtotal:0<Ctotal:=by dsimp[Ctotal];positivity
  refine ⟨Ctotal,κ,M₀,hCtotal,hκ,zero_lt_one.trans_le hM₀1,?_⟩
  intro g x hx
  dsimp only
  let h:ℝ:=complexity g p
  let m:ℝ:=min h (h*Psi x)
  intro hm₀
  have hm1:1≤ m:=hM₀1.trans hm₀
  have hm:0 < m:=zero_lt_one.trans_le hm1
  have hmh:m≤h:=min_le_left _ _
  have hh:0<h:=hm.trans_le hmh
  have hhH:H≤h:=(hM₀H.trans hm₀).trans hmh
  have hh32:(32:ℝ)≤h:=(hM₀32.trans hm₀).trans hmh
  have hn32:32≤complexity g p:=by
    have hn:(32:ℝ)≤(complexity g p:ℝ):=hh32
    exact_mod_cast hn
  have hs:Stable g p:=by unfold Stable complexity at *;omega
  obtain ⟨hcutm,hwinm⟩:=hcutoff m (hM₀cut.trans hm₀)
  let T:ℝ:=Real.sqrt (a*Real.log m)
  have hT:1≤T:=hcutm.2.1
  have hT0:0≤T:=by linarith only[hT]
  have hTr:T≤r*Real.sqrt m:=hwinm.2.1
  have hwindow:32*T≤ρ*Real.sqrt m:=by
    have ht:=mul_le_mul_of_nonneg_right hrρ (Real.sqrt_nonneg m)
    nlinarith only[hTr,ht]
  have hsmall:4*C*T^3/(ρ*Real.sqrt m)≤1:=by
    convert hwinm.2.2 using 1 <;>ring
  have hTroot:T≤Real.sqrt m:=(hTr.trans (mul_le_mul_of_nonneg_right hr1 (Real.sqrt_nonneg m))).trans_eq (one_mul _)
  have hTsq:T^2≤h:=by
    have hmroot:=Real.sq_sqrt hm.le
    nlinarith only[hTroot,hT0,Real.sqrt_nonneg m,hmroot,hmh]
  have hpoint:∀t:ℝ,|t|≤T→‖scaledMarkedFourier P g p x t-Complex.exp (-(t:ℂ)^2/2)‖≤
      A*(1+T)^3*Real.exp (B*T^2)/Real.sqrt m:=by
    intro t ht
    have he:=hcore g hs hhH x hx hm T hT hwindow hsmall t ht
    exact he.trans (Analysis.gaussian_core_two_term_le_polynomial ρ C D E h m T hρ hC hD hE hm hmh hT)
  let U:ℝ:=Real.exp (-c*T^2)
  have hft:(∫t:ℝ in {t:ℝ|T≤|t|},‖scaledMarkedFourier P g p x t‖)≤Ct*U:=by
    apply (htail g p hp hs hn32 x hx T hT0 hTsq).trans
    apply mul_le_mul_of_nonneg_left _ hCt.le
    apply Real.exp_le_exp.mpr
    nlinarith only[mul_le_mul_of_nonneg_right hcct (sq_nonneg T)]
  have hgt:(∫t:ℝ in {t:ℝ|T≤|t|},‖Complex.exp (-(t:ℂ)^2/2)‖)≤Real.sqrt (8*Real.pi)*U:=by
    apply (Analysis.gaussian_characteristic_uniform_tail T hT0).trans
    apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
    apply Real.exp_le_exp.mpr
    nlinarith only[mul_le_mul_of_nonneg_right hcq (sq_nonneg T)]
  have hl1:=Analysis.l1_error_from_core_and_tails (scaledMarkedFourier P g p x)
    (fun t:ℝ=>Complex.exp (-(t:ℂ)^2/2)) (scaledMarkedFourier_integrable P g p x hx)
    Analysis.gaussian_characteristic_integrable T (A*(1+T)^3*Real.exp (B*T^2)/Real.sqrt m)
    (Ct*U) (Real.sqrt (8*Real.pi)*U) hT0 hpoint hft hgt
  have hcentral:2*T*(A*(1+T)^3*Real.exp (B*T^2)/Real.sqrt m)≤32*A*m^(-1/4:ℝ):=by
    have hpoly:T*(1+T)^3≤(1+T)^4:=by
      have hpw:=mul_le_mul_of_nonneg_right (show T≤1+T by linarith) (pow_nonneg (by linarith only[hT]:0≤1+T) 3)
      convert hpw using 1 <;>ring
    have hc₁:2*T*(A*(1+T)^3*Real.exp (B*T^2)/Real.sqrt m)≤
        2*A*((1+T)^4*Real.exp (B*T^2)/Real.sqrt m):=by
      have hm₁:=mul_le_mul_of_nonneg_left hpoly (by positivity:0≤2*A*Real.exp (B*T^2)/Real.sqrt m)
      convert hm₁ using 1 <;>ring
    have hc₂:=mul_le_mul_of_nonneg_left hcutm.2.2 (by positivity:0≤2*A)
    exact hc₁.trans (by convert hc₂ using 1 <;>ring)
  have hU:U=m^(-(c*a)):=Analysis.logarithmic_gaussian_cutoff_tail a c m ha.le hm1
  have hrate₁:m^(-1/4:ℝ)≤ m^(-κ):=Real.rpow_le_rpow_of_exponent_le hm1 (by linarith only[hκq])
  have hrate₂:m^(-(c*a))≤ m^(-κ):=Real.rpow_le_rpow_of_exponent_le hm1 (by linarith only[hκca])
  apply hl1.trans
  have hcRate:=mul_le_mul_of_nonneg_left hrate₁ (by positivity:0≤32*A)
  have htRate:=mul_le_mul_of_nonneg_left hrate₂ (by positivity:0≤Ct+Real.sqrt (8*Real.pi))
  change 2*T*(A*(1+T)^3*Real.exp (B*T^2)/Real.sqrt m)+Ct*U+Real.sqrt (8*Real.pi)*U≤Ctotal*m^(-κ)
  rw[hU]
  have he:32*A*m^(-κ)+(Ct+Real.sqrt (8*Real.pi))*m^(-κ)=Ctotal*m^(-κ):=by dsimp[Ctotal];ring
  linarith only[hcentral,hcRate,htRate,he]
end WP
