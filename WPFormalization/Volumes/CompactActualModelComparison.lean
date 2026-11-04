import WPFormalization.Volumes.CompactActualCentralTransfer
import WPFormalization.Volumes.CompactModelIntegrability
import WPFormalization.Volumes.CompactOptimalComparison
import WPFormalization.Analysis.PoissonInverseUniformScale
import WPFormalization.Analysis.VarianceCompactLower
import WPFormalization.Volumes.CriticalFourierGeometry
import WPFormalization.Volumes.MarkedFourierIntegralTail
import WPFormalization.Analysis.QuarterFourierWindow
import WPFormalization.Analysis.QuarterExponentialBound
/-! The actual compact optimal coefficient comparison supplies every local Fourier, full L1, outer-tail, period, central integrability and base-factor input. The SAME given canonical f/B/kappa/J and the once-selected actual S/l/Bc are retained. Arbitrary smaller spatial caps are supported for composition with the original raw Gaussian expansion. The subsequent P-only canonical producer supplies the real optimal-source premise. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace WP.Analysis
set_option maxHeartbeats 2000000 in
lemma actual_compact_coefficient_model_comparison
    (P:PsiTheory)(p:ℕ)(hp:1≤p)
    (α β:ℝ)(hα:0<α)(hαβ:α≤β)(hβc:β<xCritical)
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
    ∃S l Bc:ℂ→ℂ,
      (∀x∈Icc α β,AnalyticAt ℂ S (x:ℂ) ∧ AnalyticAt ℂ l (x:ℂ) ∧
        (∀ᶠt:ℝ in 𝓝 x,S (t:ℂ)=(extractionS t:ℂ)) ∧
        complexEuler S (x:ℂ)=(WP.Psi x:ℂ) ∧
        ((complexEuler^[2]) S) (x:ℂ)=(WP.euler WP.Psi x:ℂ) ∧
        l (x:ℂ)=((Real.sqrt (WP.euler WP.Psi x))⁻¹:ℝ) ∧
        ∀ᶠq:ℂ in 𝓝 (x:ℂ),(l q)^2*((complexEuler^[2]) S) q=1) ∧
      (∀x∈Ico (0:ℝ) xCritical,AnalyticAt ℂ Bc (x:ℂ) ∧ Bc (x:ℂ)=(extractionB p x:ℂ)) ∧
      ∀τcap:ℝ,0<τcap→∃τ Ce be H:ℝ,0<τ ∧ τ≤τcap ∧ 0<Ce ∧ 0<be ∧ 0<H ∧
      ∀g:ℕ,H≤(complexity g p:ℝ)→∀x∈Icc α β,∀k:ℕ,
        (k:ℝ)=(complexity g p:ℝ)*WP.Psi x→
      let h:ℝ:=complexity g p
      let J:=⌊κ*Real.sqrt h⌋₊
      ‖((realCoeff (iteratedDeriv p (Phi P g)) k/extractionQ g p k:ℝ):ℂ)-
        (finiteMorseSourceIntegral (fun u:ℂ=>centeredExponentialPhase S l ((x:ℂ),u))
          (fun s u=>compactPremorseAmplitude P Bc l f s ((x:ℂ),u)) h (τ/Real.sqrt (Real.sqrt h)) J/
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
  obtain ⟨S,l,Bc,τc,bc,Cc,Hc,hτc,hbc,hCc,hHc,hH0c,hData,hBc,hcmp⟩ :=
    compact_optimal_comparison_of_parameter_data P p hp α β hα hαβ hβc Ω f C B κ a H0
      hΩ hcover hC hB ha hH0 hf hrest hbound hweak
  obtain ⟨Ug,rg,Cg,hUg,hcoverg,hrg,hCg,hAf,hGrowth⟩ :=
    compact_uniform_model_data_of_given_physical_family P p α β hα hαβ hβc S l Bc
      (fun x hx => (hData x hx).1) (fun x hx => (hData x hx).2.1)
      (fun x hx => (hData x hx).2.2.2.2.2.2) hBc Ω f C B hΩ hcover hC hB hf hrest hbound
  let ρg : ℝ := rg/4
  have hρg : 0 < ρg := by dsimp [ρg]; positivity
  obtain ⟨v,hv,hvbound⟩ := compact_eulerPsi_positive_lower α β hα hαβ hβc
  let bv : ℝ := Real.sqrt v
  have hbv : 0 < bv := Real.sqrt_pos.mpr hv
  have hphysical (x : ℝ) (hx : x∈Icc α β) : x∈Ioo (0:ℝ) xCritical :=
    ⟨hα.trans_le hx.1,hx.2.trans_lt hβc⟩
  have hαI : α∈Ioo (0:ℝ) xCritical := ⟨hα,hαβ.trans_lt hβc⟩
  have hYα := (inverseY_branch α ⟨hα.le,hαI.2⟩).1
  have hYαpos : 0 < inverseY α := by
    by_contra hn
    have he : inverseY α = 0 := le_antisymm (le_of_not_gt hn) hYα.1
    have he' := (inverseY_branch α ⟨hα.le,hαI.2⟩).2
    rw [he,XR_zero] at he'
    linarith
  have hPα : 0 < WP.Psi α := by
    have he := density_strictMonoOn ⟨le_rfl,y₀_pos⟩ hYα hYαpos
    rw [density_zero_value] at he
    exact half_pos he
  have hPmin (x : ℝ) (hx : x∈Icc α β) : WP.Psi α ≤ WP.Psi x :=
    Psi_strictMonoOn.monotoneOn hαI (hphysical x hx) hx.1
  obtain ⟨Cp,Bp,cp,Hp,M,hCp,hBp,hcp,hHp,hM,hpoisson⟩ := poissonInverse_uniform_scaled_data (WP.Psi α) hPα
  obtain ⟨ct,Ct,hct,hCt,hTailData⟩:=actual_marked_fourier_integral_tails P
  refine ⟨S,l,Bc,hData,hBc,?_⟩
  intro τcap hτcap
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
  refine ⟨τ,Ce,be,H,hτ,hττcap,hCe,hbe,hH,?_⟩
  intro g hg x hxcompact k hroot
  dsimp only
  let h:ℝ:=complexity g p
  let J:ℕ:=⌊κ*Real.sqrt h⌋₊
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
  have hx : x∈Ioo (0:ℝ) xCritical := hphysical x hxcompact
  have hY : inverseY x∈Ico (0:ℝ) y₀ := (inverseY_branch x ⟨hx.1.le,hx.2⟩).1
  have hwindow:=quarter_fourier_window h (WP.euler WP.Psi x) τ bv hh1 hτ.le hτ1 hbv (Real.sqrt_le_sqrt (hvbound x hxcompact)) hτbv
  have hT:0≤T:=by dsimp[T];positivity
  have hm:=hmodels g hh0
  obtain ⟨hPco,hPdata⟩ := hpoisson (WP.Psi x) (hPmin x hxcompact)
  have hk : 1 ≤ k := by
    have hkpos : (0:ℝ) < k := by rw [hroot]; exact mul_pos hh (hPα.trans_le (hPmin x hxcompact))
    exact_mod_cast (show 0 < k by exact_mod_cast hkpos)
  have hy : |(poissonNormalizer k)⁻¹| ≤ M := by
    have ht := (hPdata h hhP).1
    rwa [←hroot] at ht
  have hxg : (x:ℂ)∈Ug := hcoverg x hxcompact
  have hTR : T < rg * Real.sqrt h := by
    have hs1 : 1 ≤ Real.sqrt h := by simpa using Real.sqrt_le_sqrt hh1
    have hss : Real.sqrt (Real.sqrt h) ≤ Real.sqrt h := Real.sqrt_le_self_iff.mpr (Or.inr hs1)
    have hτrg : τ ≤ rg/4 := hτρg
    have hs : 0 < Real.sqrt h := Real.sqrt_pos.mpr hh
    calc T ≤ τ * Real.sqrt h := mul_le_mul_of_nonneg_left hss hτ.le
         _ ≤ (rg/4) * Real.sqrt h := mul_le_mul_of_nonneg_right hτrg hs.le
         _ < rg * Real.sqrt h := by nlinarith
  have hGint := compact_finite_model_axis_integrable_at P Bc S l f (x:ℂ) rg Cg B h T J
    hrg hCg.le hB hh hTR
    (fun u hu => ⟨(hGrowth _ hxg u hu).1,(hGrowth _ hxg u hu).2.1⟩)
    (fun j u hu => ⟨hAf j _ ⟨hxg,by simpa only [Metric.mem_ball,dist_zero_right] using hu⟩,
      (hGrowth _ hxg u hu).2.2.2 j⟩) hm.1 (by
        rw [PositiveConvolution.planarInverse_ofReal P x ⟨hx.1.le,hx.2⟩]
        exact (hm.2.1 _ (hcover _ ⟨hY.1,hY.2.le⟩)).2.1)
  obtain ⟨hFull,hTail⟩:=hTailData g p hp hs hhN x hx
  have hTail':(∫t:ℝ in (Icc (-T) T)ᶜ,‖scaledMarkedFourier P g p x t‖)≤Ct*Real.exp (-ct*T^2):=hTail T hT hwindow.1
  have hpoint:∀t∈Icc (-T) T,‖scaledMarkedFourier P g p x t-
      compactCenteredFiniteModel P Bc S l f h J (x:ℂ) (Complex.I*(t:ℂ))‖≤Cc*Real.exp (-bc*Real.sqrt h) := by
    intro t ht
    have htA:|t|≤T:=abs_le.mpr ⟨by linarith[ht.1],ht.2⟩
    have htP:t∈Icc (-(Real.pi*Real.sqrt (h*WP.euler WP.Psi x))) (Real.pi*Real.sqrt (h*WP.euler WP.Psi x)):=by
      constructor <;>linarith[ht.1,ht.2,hwindow.2]
    rw[scaledMarkedFourier_eq_centered_on_period P g p k x t hroot htP]
    exact hcmp g hhC x hxcompact k hroot (Complex.I*(t:ℂ)) (by
      rw[norm_mul,Complex.norm_I,one_mul,Complex.norm_real,Real.norm_eq_abs]
      exact htA.trans (mul_le_mul_of_nonneg_right hττc (Real.sqrt_nonneg _)))
  let z:ℂ:=HigherOrder.finiteMarkedFactor f h J ((inverseY x:ℝ):ℂ)
  have hZ:=hm.2.1 ((inverseY x:ℝ):ℂ) (hcover _ ⟨hY.1,hY.2.le⟩)
  have hzne:z≠0:=by simpa only using hZ.2.2.2
  have hz2:‖z‖≤2:=by simpa only using hZ.2.2.1
  have hzreal:z=(HigherOrder.realFiniteMarkedFactor P p h J (inverseY x):ℂ):=by
    simpa only using hm.2.2.1 _ ⟨hY.1,hY.2.le⟩
  have hrel:‖((Real.pi*markedF P g p x/markedModel g p (inverseY x):ℝ):ℂ)/z-1‖≤
      2*C*Real.exp (-a*Real.sqrt h) := by
    have he:((Real.pi*markedF P g p x/markedModel g p (inverseY x)/
        HigherOrder.realFiniteMarkedFactor P p h J (inverseY x)-1:ℝ):ℂ)=
        ((Real.pi*markedF P g p x/markedModel g p (inverseY x):ℝ):ℂ)/z-1 := by
      rw[hzreal]
      push_cast
      rfl
    rw[←he,Complex.norm_real,Real.norm_eq_abs]
    simpa only [(inverseY_branch x ⟨hx.1.le,hx.2⟩).2] using hm.2.2.2 _ hY
  have hcent:=compact_actual_relativeQ_central_model_error P g p k J hp hs hk hh Bc S l f x hx hroot
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
