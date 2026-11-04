import WPFormalization.Volumes.CriticalActualCentralTransfer
import WPFormalization.Volumes.CriticalModelFourierLocal
import WPFormalization.Volumes.CriticalFourierGeometry
import WPFormalization.Volumes.CriticalPoissonScale
import WPFormalization.Volumes.MarkedFourierIntegralTail
import WPFormalization.Volumes.CriticalOptimalComparison
import WPFormalization.Analysis.QuarterFourierWindow
import WPFormalization.Analysis.QuarterExponentialBound
/-! The genuine optimal marked generating function has an exponentially accurate
critical coefficient comparison with the same finite analytic source.
Every central Fourier, full L1, tail, period and real base-factor input is
supplied from the proved actual objects. Smaller parameter and spatial
caps are retained for the subsequent all-order source expansion. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace WP.Analysis
set_option maxHeartbeats 2000000 in
lemma CriticalGaussianCoordinateData.actual_critical_coefficient_model_comparison
    (d:CriticalGaussianCoordinateData)(P:PsiTheory)(p:ℕ)(hp:1≤p)
    (Ω:Set ℂ)(f:ℕ→ℂ→ℂ)(C B κ a H0:ℝ)
    (hΩ:IsOpen Ω)(hcover:∀Y∈Icc (0:ℝ) y₀,(Y:ℂ)∈Ω)
    (hC:0<C)(hB:0<B)(hκ:0<κ)(ha:0<a)(hH0:0<H0)
    (hf:∀j,AnalyticOnNhd ℂ (f j) Ω)
    (hrest:∀j Y,Y∈Icc (0:ℝ) y₀→f j (Y:ℂ)=(HigherOrder.markedCoefficient P p j Y:ℂ))
    (hbound:∀j z,z∈Ω→‖f j z‖≤C*B^j*(j.factorial:ℝ)^2)
    (hmodels:∀g:ℕ,H0≤(complexity g p:ℝ)→
      let h:ℝ:=complexity g p
      let J:=⌊κ*Real.sqrt h⌋₊
      2*B*((J:ℝ)+1)^2≤h ∧
      (∀z∈Ω,‖HigherOrder.finiteMarkedFactor f h J z-1‖≤2*C*B/h ∧
        1/2≤‖HigherOrder.finiteMarkedFactor f h J z‖ ∧
        ‖HigherOrder.finiteMarkedFactor f h J z‖≤2 ∧ HigherOrder.finiteMarkedFactor f h J z≠0) ∧
      (∀Y∈Icc (0:ℝ) y₀,HigherOrder.finiteMarkedFactor f h J (Y:ℂ)=(HigherOrder.realFiniteMarkedFactor P p h J Y:ℂ)) ∧
      (∀Y∈Ico (0:ℝ) y₀,|(Real.pi*markedF P g p (XR Y)/markedModel g p Y)/
        HigherOrder.realFiniteMarkedFactor P p h J Y-1|≤2*C*Real.exp (-a*Real.sqrt h))) :
    ∃Q:ℂ→ℂ,AnalyticAt ℂ Q 0 ∧ Q 0=1 ∧
      (∀ᶠδ:ℝ in 𝓝 0,0<δ→Q (δ:ℂ)=(WP.Theta (y₀-δ):ℂ)) ∧
      ∀Rcap τcap:ℝ,0<Rcap→0<τcap→
      ∃R τ Ce be H:ℝ,0<R ∧ R≤Rcap ∧ R<y₀ ∧ 0<τ ∧ τ≤τcap ∧ 0<Ce ∧ 0<be ∧ 0<H ∧
      ∀g:ℕ,H≤(complexity g p:ℝ)→∀δ∈Ioo (0:ℝ) R,∀k:ℕ,
        (k:ℝ)=(complexity g p:ℝ)*WP.Psi (XR (y₀-δ))→
      let h:ℝ:=complexity g p
      let J:=⌊κ*Real.sqrt h⌋₊
      ‖((realCoeff (iteratedDeriv p (Phi P g)) k/extractionQ g p k:ℝ):ℂ)-
        (finiteMorseSourceIntegral (fun u:ℂ=>d.kernel.centeredPhase d.L d.q ((δ:ℂ),u))
          (fun s u=>d.preMorseAmplitude Q p f s ((δ:ℂ),u)) h (τ/Real.sqrt (Real.sqrt h)) J/
          (Real.sqrt (2*Real.pi):ℂ))*(((poissonNormalizer k)⁻¹:ℝ):ℂ)‖≤
        Ce*Real.exp (-be*Real.sqrt h) := by
  have hweak:∀g:ℕ,H0≤(complexity g p:ℝ)→
      let h:ℝ:=complexity g p
      let J:=⌊κ*Real.sqrt h⌋₊
      2*B*((J:ℝ)+1)^2≤h ∧
      (∀Y∈Icc (0:ℝ) y₀,1/2≤‖HigherOrder.finiteMarkedFactor f h J (Y:ℂ)‖) ∧
      (∀Y∈Ico (0:ℝ) y₀,|(Real.pi*markedF P g p (XR Y)/markedModel g p Y)/
        HigherOrder.realFiniteMarkedFactor P p h J Y-1|≤2*C*Real.exp (-a*Real.sqrt h)) := by
    intro g hg
    have hm:=hmodels g hg
    exact ⟨hm.1,(fun Y hY=>(hm.2.1 _ (hcover Y hY)).2.1),hm.2.2.2⟩
  obtain ⟨Q,Rc,τc,bc,Cc,Hc,hQ,hQ0,hQphys,hRc,hRcy,hτc,hbc,hCc,hHc,hH0c,hcmp⟩:=
    d.critical_optimal_comparison_of_parameter_data P p hp Ω f C B κ a H0
      hΩ hcover hC hB ha hH0 hf hrest hbound hweak
  obtain ⟨Rg,ρg,hRg,hρg,hGi⟩:=d.common_centered_model_fourier_integrability Q p f Ω C B hQ hQ0 hΩ
    (hcover _ ⟨y₀_pos.le,le_rfl⟩) hC hB hf hbound
  obtain ⟨Rv,bv,hRv,hRvy,hbv,hvbound⟩:=d.critical_variance_sqrt_lower
  obtain ⟨Rp,Cp,Bp,cp,Hp,M,hRp,hRpy,hCp,hBp,hcp,hHp,hM,hpoisson⟩:=d.kernel.inverse_poisson_uniform_scaled_data
  obtain ⟨ct,Ct,hct,hCt,hTailData⟩:=actual_marked_fourier_integral_tails P
  refine ⟨Q,hQ,hQ0,hQphys,?_⟩
  intro Rcap τcap hRcap hτcap
  let R0:ℝ:=min Rcap (min Rc (min Rg (min Rv Rp)))
  let R:ℝ:=R0/2
  have hR0:0<R0:=lt_min hRcap (lt_min hRc (lt_min hRg (lt_min hRv hRp)))
  have hR:0<R:=half_pos hR0
  have hRR0:R<R0:=half_lt_self hR0
  have hRRcap:R≤Rcap:=hRR0.le.trans (min_le_left _ _)
  have hRRc:R<Rc:=hRR0.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hRRg:R<Rg:=hRR0.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hRRv:R<Rv:=hRR0.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
  have hRRp:R<Rp:=hRR0.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))))
  let τ0:ℝ:=min τcap (min τc (min ρg (min 1 (Real.pi*bv))))
  let τ:ℝ:=τ0/2
  have hτ0:0<τ0:=lt_min hτcap (lt_min hτc (lt_min hρg (lt_min zero_lt_one (mul_pos Real.pi_pos hbv))))
  have hτ:0<τ:=half_pos hτ0
  have hττ0:τ<τ0:=half_lt_self hτ0
  have hττcap:τ≤τcap:=hττ0.le.trans (min_le_left _ _)
  have hττc:τ≤τc:=hττ0.le.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hτρg:τ≤ρg:=hττ0.le.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hτ1:τ≤1:=hττ0.le.trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
  have hτbv:τ≤Real.pi*bv:=hττ0.le.trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))))
  let be:ℝ:=min a (min (ct*τ^2) (bc/2))
  have hbe:0<be:=lt_min ha (lt_min (by positivity) (half_pos hbc))
  have hbea:be≤a:=min_le_left _ _
  have hbect:be≤ct*τ^2:=(min_le_right _ _).trans (min_le_left _ _)
  have hbec:be≤bc/2:=(min_le_right _ _).trans (min_le_right _ _)
  let D:ℝ:=2*M/Real.sqrt (2*Real.pi)
  let Ce:ℝ:=D*(2*C*Ct+Ct+8*τ*Cc/bc)
  let H:ℝ:=Hc+Hp+H0+32+1
  have hD:0<D:=by dsimp[D];positivity
  have hCe:0<Ce:=by dsimp[Ce];positivity
  have hH:0<H:=by dsimp[H];positivity
  refine ⟨R,τ,Ce,be,H,hR,hRRcap,hRRc.trans hRcy,hτ,hττcap,hCe,hbe,hH,?_⟩
  intro g hg δ hδ k hroot
  dsimp only
  let h:ℝ:=complexity g p
  let J:ℕ:=⌊κ*Real.sqrt h⌋₊
  let x:ℝ:=XR (y₀-δ)
  let T:ℝ:=τ*Real.sqrt (Real.sqrt h)
  have hhC:Hc≤h:=by dsimp[H] at hg;linarith
  have hhP:Hp≤h:=by dsimp[H] at hg;linarith
  have hh0:H0≤h:=by dsimp[H] at hg;linarith
  have hh32:32≤h:=by dsimp[H] at hg;linarith
  have hh1:1≤h:=by linarith
  have hh:0<h:=by linarith
  have hhN:32≤complexity g p:=by exact_mod_cast (show (32:ℝ)≤(complexity g p:ℝ) from hh32)
  have hs:Stable g p:=by
    have hn:1≤complexity g p:=by exact_mod_cast (show (1:ℝ)≤(complexity g p:ℝ) from hh1)
    unfold Stable complexity at *
    omega
  have hδc:δ∈Ioo (0:ℝ) Rc:=⟨hδ.1,hδ.2.trans hRRc⟩
  have hδv:δ∈Ioo (0:ℝ) Rv:=⟨hδ.1,hδ.2.trans hRRv⟩
  have hδp:δ∈Ioo (0:ℝ) Rp:=⟨hδ.1,hδ.2.trans hRRp⟩
  have hδY:δ∈Ioo (0:ℝ) y₀:=⟨hδ.1,(hδ.2.trans hRRc).trans hRcy⟩
  have hY: y₀-δ∈Ico (0:ℝ) y₀:=⟨by linarith[hδY.2],by linarith[hδ.1]⟩
  have hx:x∈Ioo (0:ℝ) xCritical:=by
    constructor
    · simpa only[XR_zero] using XR_strictMonoOn (show (0:ℝ)∈Iic y₀ from y₀_pos.le) (show y₀-δ∈Iic y₀ from hY.2.le) (show 0<y₀-δ by linarith[hδY.2])
    · exact XR_strictMonoOn (show y₀-δ∈Iic y₀ from hY.2.le) (show y₀∈Iic y₀ from by simp) hY.2
  have hwindow:=quarter_fourier_window h (WP.euler WP.Psi x) τ bv hh1 hτ.le hτ1 hbv (hvbound δ hδv) hτbv
  have hT:0≤T:=by dsimp[T];positivity
  have hm:=hmodels g hh0
  obtain ⟨hΨ,hPco,hPdata⟩:=hpoisson δ hδp
  have hkh:h≤(k:ℝ):=by
    calc h=h*1:=by ring
         _≤h*WP.Psi x:=mul_le_mul_of_nonneg_left hΨ hh.le
         _=(k:ℝ):=hroot.symm
  have hk:1≤k:=by exact_mod_cast (hh1.trans hkh)
  have hy:|(poissonNormalizer k)⁻¹|≤M:=by
    have ht:=(hPdata h hhP).1
    rwa[←hroot] at ht
  have hδg:‖(δ:ℂ)‖<Rg:=by rw[Complex.norm_of_nonneg hδ.1.le];exact hδ.2.trans hRRg
  have hGint:=hGi (δ:ℂ) hδg τ ⟨hτ,hτρg⟩ h hh1 J
  obtain ⟨hFull,hTail⟩:=hTailData g p hp hs hhN x hx
  have hTail':(∫t:ℝ in (Icc (-T) T)ᶜ,‖scaledMarkedFourier P g p x t‖)≤Ct*Real.exp (-ct*T^2):=hTail T hT hwindow.1
  have hpoint:∀t∈Icc (-T) T,‖scaledMarkedFourier P g p x t-
      d.centeredFiniteMarkedModel Q p f h J (δ:ℂ) (Complex.I*(t:ℂ))‖≤Cc*Real.exp (-bc*Real.sqrt h) := by
    intro t ht
    have htA:|t|≤T:=abs_le.mpr ⟨by linarith[ht.1],ht.2⟩
    have htP:t∈Icc (-(Real.pi*Real.sqrt (h*WP.euler WP.Psi x))) (Real.pi*Real.sqrt (h*WP.euler WP.Psi x)):=by
      constructor <;>linarith[ht.1,ht.2,hwindow.2]
    rw[scaledMarkedFourier_eq_centered_on_period P g p k x t hroot htP]
    exact hcmp g hhC δ hδc k hroot (Complex.I*(t:ℂ)) (by
      rw[norm_mul,Complex.norm_I,one_mul,Complex.norm_real,Real.norm_eq_abs]
      exact htA.trans (mul_le_mul_of_nonneg_right hττc (Real.sqrt_nonneg _)))
  let z:ℂ:=HigherOrder.finiteMarkedFactor f h J ((y₀:ℂ)-(δ:ℂ))
  have hZ:=hm.2.1 ((y₀-δ:ℝ):ℂ) (hcover _ ⟨hY.1,hY.2.le⟩)
  have hzne:z≠0:=by simpa only[Complex.ofReal_sub] using hZ.2.2.2
  have hz2:‖z‖≤2:=by simpa only[Complex.ofReal_sub] using hZ.2.2.1
  have hzreal:z=(HigherOrder.realFiniteMarkedFactor P p h J (y₀-δ):ℂ):=by
    simpa only[Complex.ofReal_sub] using hm.2.2.1 _ ⟨hY.1,hY.2.le⟩
  have hrel:‖((Real.pi*markedF P g p x/markedModel g p (y₀-δ):ℝ):ℂ)/z-1‖≤
      2*C*Real.exp (-a*Real.sqrt h) := by
    have he:((Real.pi*markedF P g p x/markedModel g p (y₀-δ)/
        HigherOrder.realFiniteMarkedFactor P p h J (y₀-δ)-1:ℝ):ℂ)=
        ((Real.pi*markedF P g p x/markedModel g p (y₀-δ):ℝ):ℂ)/z-1 := by
      rw[hzreal]
      push_cast
      rfl
    rw[←he,Complex.norm_real,Real.norm_eq_abs]
    exact hm.2.2.2 _ hY
  have hcent:=d.actual_relativeQ_central_model_error P g p k J hp hs hk hh Q f δ hδY hroot
    T (Cc*Real.exp (-bc*Real.sqrt h)) (Ct*Real.exp (-ct*T^2)) Ct M 2
    (2*C*Real.exp (-a*Real.sqrt h)) hT hM.le (by norm_num) hy hzne hz2 hrel hGint hpoint hTail' hFull
  have hcut:T/Real.sqrt h=τ/Real.sqrt (Real.sqrt h):=by
    have heq:Real.sqrt h=(Real.sqrt (Real.sqrt h))^2:=(Real.sq_sqrt (Real.sqrt_nonneg h)).symm
    have hss:0<Real.sqrt (Real.sqrt h):=by positivity
    calc _=τ*Real.sqrt (Real.sqrt h)/(Real.sqrt (Real.sqrt h))^2:=congrArg (fun r:ℝ=>τ*Real.sqrt (Real.sqrt h)/r) heq
         _=_:=by field_simp[hss.ne']
  rw[hcut] at hcent
  apply hcent.trans
  have hexp (v:ℝ)(hv:be≤v):Real.exp (-v*Real.sqrt h)≤Real.exp (-be*Real.sqrt h):=
    Real.exp_le_exp.mpr (by nlinarith[Real.sqrt_nonneg h])
  have hT2:T^2=τ^2*Real.sqrt h:=by dsimp[T];rw[mul_pow,Real.sq_sqrt (Real.sqrt_nonneg h)]
  have htailExp:Real.exp (-ct*T^2)≤Real.exp (-be*Real.sqrt h):=by
    have he:-ct*T^2=-(ct*τ^2)*Real.sqrt h:=by rw[hT2];ring
    rw[he]
    exact hexp _ hbect
  have hquarter:=quarter_power_exp_neg_sqrt_bound bc h hbc hh1
  have hpointTerm:2*T*(Cc*Real.exp (-bc*Real.sqrt h))≤
      (8*τ*Cc/bc)*Real.exp (-be*Real.sqrt h) := by
    calc _=(2*τ*Cc)*(Real.sqrt (Real.sqrt h)*Real.exp (-bc*Real.sqrt h)):=by dsimp[T];ring
         _≤(2*τ*Cc)*((4/bc)*Real.exp (-(bc/2)*Real.sqrt h)):=
           mul_le_mul_of_nonneg_left hquarter (by positivity)
         _=(8*τ*Cc/bc)*Real.exp (-(bc/2)*Real.sqrt h):=by ring
         _≤_:=mul_le_mul_of_nonneg_left (hexp _ hbec) (by positivity)
  have hrealTerm:(2*C*Real.exp (-a*Real.sqrt h))*Ct≤(2*C*Ct)*Real.exp (-be*Real.sqrt h):=by
    calc _=(2*C*Ct)*Real.exp (-a*Real.sqrt h):=by ring
         _≤_:=mul_le_mul_of_nonneg_left (hexp _ hbea) (by positivity)
  have htailTerm:Ct*Real.exp (-ct*T^2)≤Ct*Real.exp (-be*Real.sqrt h):=
    mul_le_mul_of_nonneg_left htailExp hCt.le
  calc _≤D*((2*C*Ct)*Real.exp (-be*Real.sqrt h)+Ct*Real.exp (-be*Real.sqrt h)+
      (8*τ*Cc/bc)*Real.exp (-be*Real.sqrt h)):=
        mul_le_mul_of_nonneg_left (add_le_add (add_le_add hrealTerm htailTerm) hpointTerm) hD.le
       _=_:=by dsimp[Ce];ring
end WP.Analysis
