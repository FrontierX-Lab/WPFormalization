import WPFormalization.Volumes.OriginPointwiseFourierTransfer
import WPFormalization.Volumes.OriginOptimalComparison
import WPFormalization.Analysis.QuarterExponentialBound
/-! Uniform actual coefficient comparison with the same optimal finite
origin model above kappa_lo sqrt(h). Every Fourier, tail and prefactor input
is supplied from actual objects and the same-source conclusions. -/
noncomputable section
namespace WP.HigherOrder
open Set Filter MeasureTheory
open scoped Topology
set_option maxHeartbeats 2000000 in
lemma origin_nontiny_coefficient_comparison_of_source (P:PsiTheory)(p:ℕ)(hp:1≤p)
    (Ω:Set ℂ)(L:ℕ→ℂ→ℂ)(S Bc:ℂ→ℂ)(ρ B D κ a Cerr H0 κlo:ℝ)
    (hρ:0<ρ)(hρx:ρ<xCritical)(hB:0<B)(hD:0<D)(ha:0<a)(hCerr:0<Cerr)(hH0:0<H0)(hκlo:0<κlo)
    (hS:AnalyticAt ℂ S 0)(hSd:deriv S 0=2)(hBc:AnalyticAt ℂ Bc 0)(hBc0:Bc 0≠0)
    (hSr:∀x∈Icc (0:ℝ) ρ,S (x:ℂ)=(extractionS x:ℂ))
    (hBr:∀x∈Icc (0:ℝ) ρ,Bc (x:ℂ)=(extractionB p x:ℂ))
    (hmap:∀z:ℂ,‖z‖≤ρ→PositiveConvolution.planarInverse P z∈Ω)
    (hAb:∀j z,‖z‖≤ρ→‖originMarkedAmplitude P p j Bc L z‖≤D*B^j*(j.factorial:ℝ)^2)
    (hBn:∀x∈Icc (0:ℝ) ρ,‖Bc (x:ℂ)-1‖≤1/2)
    (hphase:∀x∈Ioo (0:ℝ) ρ,∀θ:ℝ,
      (S ((x:ℂ)*Complex.exp ((θ:ℂ)*Complex.I))-S (x:ℂ)).re≤-(x/2)*(1-Real.cos θ))
    (hmodels:∀g:ℕ,H0≤(complexity g p:ℝ)→
      let h:ℝ:=complexity g p
      let J:=⌊κ*Real.sqrt h⌋₊
      2*B*((J:ℝ)+1)^2≤h ∧
      (∀z∈Ω,1/2≤‖finiteMarkedFactor L h J z‖ ∧ ‖finiteMarkedFactor L h J z‖≤2) ∧
      (∀z:ℂ,‖z‖≤ρ→AnalyticAt ℂ (normalizedFiniteMarkedModel P g p S Bc L J) z) ∧
      (∀x∈Icc (0:ℝ) ρ,normalizedFiniteMarkedModel P g p S Bc L J (x:ℂ)≠0 ∧
        ‖normalizedMarkedGenerating P g p (x:ℂ)/normalizedFiniteMarkedModel P g p S Bc L J (x:ℂ)-1‖≤
          Cerr*Real.exp (-a*Real.sqrt h))):
    ∃η Ce be H:ℝ,0<η ∧ η<ρ ∧ 0<Ce ∧ 0<be ∧ 0<H ∧ H0≤H ∧
      ∀g:ℕ,H≤(complexity g p:ℝ)→∀x∈Ioo (0:ℝ) η,∀k:ℕ,
        (k:ℝ)=(complexity g p:ℝ)*Psi x→κlo*Real.sqrt (complexity g p:ℝ)≤(k:ℝ)→
        let h:ℝ:=complexity g p
        let J:=⌊κ*Real.sqrt h⌋₊
        ‖WP.coeff (iteratedDeriv p (Phi P g)) k/(extractionQ g p k:ℂ)-
          WP.coeff (normalizedFiniteMarkedModel P g p S Bc L J) k/
            ((Real.pi*extractionQ g p k/markedModel g p 0:ℝ):ℂ)‖≤Ce*Real.exp (-be*Real.sqrt h):=by
  have hSrg:∀ᶠt:ℝ in 𝓝 0,0≤t→S (t:ℂ)=(extractionS t:ℂ):=by
    filter_upwards[eventually_lt_nhds hρ] with t ht ht0
    exact hSr t ⟨ht0,ht.le⟩
  have hBrg:∀ᶠt:ℝ in 𝓝 0,0≤t→Bc (t:ℂ)=(extractionB p t:ℂ):=by
    filter_upwards[eventually_lt_nhds hρ] with t ht ht0
    exact hBr t ⟨ht0,ht.le⟩
  obtain ⟨ηc,τc,bc,Cc,Hc,hηc,hηcρ,hτc,hbc,hCc,hHc,hH0c,hcmp⟩:=
    origin_optimal_comparison_of_source P p hp Ω L S Bc ρ κ a Cerr H0 κlo
      hρ hρx ha hCerr hH0 hκlo hS hSd hBc hBc0 hSrg hBrg hmap
      (fun g hg=>⟨(hmodels g hg).2.1,(hmodels g hg).2.2.1,(hmodels g hg).2.2.2⟩)
  obtain ⟨rv,hrv,hrvx,hvar⟩:=WP.Analysis.eulerPsi_origin_upper
  obtain ⟨Hp,hHp,hpref⟩:=WP.Analysis.normalizedFiniteModel_prefactor_bound_nonTiny κlo hκlo
  obtain ⟨ct,Ct,hct,hCt,htails⟩:=WP.Analysis.actual_marked_fourier_integral_tails P
  let η:ℝ:=min ηc rv/2
  let τ:ℝ:=min τc 1
  let cm:ℝ:=1/(8*Real.pi^2)
  let Cm:ℝ:=8*D*Real.sqrt (16*Real.pi^3)
  let DP:ℝ:=4*Real.sqrt (2*Real.pi)
  let be:ℝ:=min a (min (ct*τ^2) (min (cm*τ^2) (bc/2)))
  let Ce:ℝ:=DP/(2*Real.pi)*(Cerr*Ct+Ct+Cm+8*τ*Cc/bc)
  let H:ℝ:=H0+Hc+Hp+33
  have hη:0<η:=by dsimp[η];positivity
  have hηηc:η<ηc:=(div_le_div_of_nonneg_right (min_le_left ηc rv) (by norm_num)).trans_lt (half_lt_self hηc)
  have hηrv:η<rv:=(div_le_div_of_nonneg_right (min_le_right ηc rv) (by norm_num)).trans_lt (half_lt_self hrv)
  have hτ:0<τ:=lt_min hτc zero_lt_one
  have hτc':τ≤τc:=min_le_left _ _
  have hτ1:τ≤1:=min_le_right _ _
  have hcm:0<cm:=by dsimp[cm];positivity
  have hCm:0<Cm:=by dsimp[Cm];positivity
  have hDP:0<DP:=by dsimp[DP];positivity
  have hbe:0<be:=lt_min ha (lt_min (by positivity) (lt_min (by positivity) (half_pos hbc)))
  have hbea:be≤a:=min_le_left _ _
  have hbect:be≤ct*τ^2:=(min_le_right _ _).trans (min_le_left _ _)
  have hbecm:be≤cm*τ^2:=(min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hbec:be≤bc/2:=(min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hCe:0<Ce:=by dsimp[Ce];positivity
  have hH:0<H:=by dsimp[H];positivity
  refine ⟨η,Ce,be,H,hη,hηηc.trans hηcρ,hCe,hbe,hH,by dsimp[H];linarith,?_⟩
  intro g hg x hx k hroot hlower
  dsimp only
  let h:ℝ:=complexity g p
  let J:ℕ:=⌊κ*Real.sqrt h⌋₊
  let T:ℝ:=τ*Real.sqrt (Real.sqrt h)
  have hg0:H0≤h:=by dsimp[H] at hg;linarith
  have hgc:Hc≤h:=by dsimp[H] at hg;linarith
  have hgp:Hp≤h:=by dsimp[H] at hg;linarith
  have hh32:32≤h:=by dsimp[H] at hg;linarith
  have hh1:1≤h:=by linarith
  have hh:0<h:=by linarith
  have hhNat:32≤complexity g p:=by exact_mod_cast (show (32:ℝ)≤(complexity g p:ℝ) from hh32)
  have hs:Stable g p:=by unfold Stable complexity at *;omega
  have hkpos:0<(k:ℝ):=(mul_pos hκlo (Real.sqrt_pos.mpr hh)).trans_le hlower
  have hk:1≤k:=by exact_mod_cast (show 0<k by exact_mod_cast hkpos)
  have hxρ:x∈Ioo (0:ℝ) ρ:=⟨hx.1,hx.2.trans (hηηc.trans hηcρ)⟩
  have hxc:x∈Ioo (0:ℝ) xCritical:=⟨hx.1,hxρ.2.trans hρx⟩
  have hxbase:x∈Icc (0:ℝ) ρ:=⟨hx.1.le,hxρ.2.le⟩
  have hm:=hmodels g hg0
  have hMreal:=hm.2.2.2 x hxbase
  have hMball:AnalyticOnNhd ℂ (normalizedFiniteMarkedModel P g p S Bc L J) (Metric.ball 0 ρ):=by
    intro z hz
    exact hm.2.2.1 z (by simpa only[Metric.mem_ball,dist_zero_right] using (show ‖z‖<ρ from by simpa only[Metric.mem_ball,dist_zero_right] using hz).le)
  have hP:=hm.2.1 (PositiveConvolution.planarInverse P (x:ℂ))
    (hmap (x:ℂ) (by rw[Complex.norm_of_nonneg hx.1.le];exact hxρ.2.le))
  rw[PositiveConvolution.planarInverse_ofReal P x ⟨hx.1.le,hxc.2⟩] at hP
  have hBpref:=hpref P g p k J hgp hlower hs S Bc L x hxc hroot (hSr x hxbase) (hBr x hxbase) hP.2
  have hT:0≤T:=by dsimp[T];positivity
  have hT2:T^2=τ^2*Real.sqrt h:=by dsimp[T];rw[mul_pow,Real.sq_sqrt (Real.sqrt_nonneg h)]
  have hTsq:T^2≤h:=by
    rw[hT2]
    have hsqrt:Real.sqrt h≤h:=(Real.sqrt_le_iff).mpr ⟨hh.le,by nlinarith⟩
    have hτsq:τ^2≤1:=by nlinarith[hτ.le]
    nlinarith[Real.sqrt_nonneg h]
  have hpoint:∀w:ℂ,‖w‖≤T→
      ‖centeredMarkedGenerating P g p k x (Real.sqrt (h*euler Psi x)) w-centeredOriginFiniteModel P g p J S Bc L x w‖≤
        Cc*Real.exp (-bc*Real.sqrt h):=by
    intro w hw
    exact hcmp g hgc x ⟨hx.1,hx.2.trans hηηc⟩ k hroot hlower w
      (hw.trans (mul_le_mul_of_nonneg_right hτc' (Real.sqrt_nonneg _)))
  have ht:=htails g p hp hs hhNat x hxc
  have htailF:=ht.2 T hT hTsq
  have hvx:euler Psi x≤4*x:=hvar x ⟨hx.1.le,(hx.2.trans hηrv).le⟩
  have htailG0:=origin_finite_model_standardized_tail_at P g p J S Bc L B D ρ x (h*Psi x) T
    hB hD hρx hxρ hh hvx hT hm.1 hAb (hBn x hxbase) (by rw[PositiveConvolution.planarInverse_ofReal P x ⟨hx.1.le,hxc.2⟩];exact hP.1) (hphase x hxρ) hm.2.2.1
  let G:ℝ→ℂ:=WP.Analysis.scaledCenteredFourier
    (WP.Analysis.sourceCirclePGF (normalizedFiniteMarkedModel P g p S Bc L J) x) (h*Psi x) (Real.sqrt (h*euler Psi x))
  have hGi:Integrable G:=WP.Analysis.scaledCenteredFourier_integrable _
    (WP.Analysis.sourceCirclePGF_sphere_continuous _ x ρ hx.1 hxρ.2 hMball) _ _
  have htailG:(∫t:ℝ in (Icc (-T) T)ᶜ,‖G t‖)≤Cm*Real.exp (-cm*T^2):=by
    apply le_trans _ htailG0
    apply setIntegral_mono_set hGi.norm.integrableOn (ae_of_all _ (fun t=>norm_nonneg _))
    apply ae_of_all
    intro t ht
    have ho:¬(-T≤t ∧ t≤T):=by simpa using ht
    have ht':t< -T ∨ T<t:=by
      rcases not_and_or.mp ho with hl | hr
      · exact Or.inl (lt_of_not_ge hl)
      · exact Or.inr (lt_of_not_ge hr)
    change T≤|t|
    rcases ht' with hl | hr
    · rw[abs_of_neg (by linarith)]
      linarith
    · exact hr.le.trans (le_abs_self _)
  have he:=WP.Analysis.actual_origin_coefficient_error_from_centered_fourier P g p k J hp hs hk S Bc L ρ x T
    (Cc*Real.exp (-bc*Real.sqrt h)) (Ct*Real.exp (-ct*T^2)) (Cm*Real.exp (-cm*T^2)) Ct DP
    (Cerr*Real.exp (-a*Real.sqrt h)) hh hρx hxρ hroot hT (by positivity) (by positivity)
    hMball hMreal.1 hBpref hMreal.2 hpoint ht.1 htailF htailG
  apply he.trans
  have hexp(v:ℝ)(hv:be≤v):Real.exp (-v*Real.sqrt h)≤Real.exp (-be*Real.sqrt h):=
    Real.exp_le_exp.mpr (by nlinarith[Real.sqrt_nonneg h])
  have hp:=WP.Analysis.quarter_power_exp_neg_sqrt_bound bc h hbc hh1
  have hp':2*T*(Cc*Real.exp (-bc*Real.sqrt h))≤(8*τ*Cc/bc)*Real.exp (-be*Real.sqrt h):=by
    calc _=(2*τ*Cc)*(Real.sqrt (Real.sqrt h)*Real.exp (-bc*Real.sqrt h)):=by dsimp[T];ring
         _≤(2*τ*Cc)*((4/bc)*Real.exp (-(bc/2)*Real.sqrt h)):=mul_le_mul_of_nonneg_left hp (by positivity)
         _≤(2*τ*Cc)*((4/bc)*Real.exp (-be*Real.sqrt h)):=mul_le_mul_of_nonneg_left
           (mul_le_mul_of_nonneg_left (hexp (bc/2) hbec) (by positivity)) (by positivity)
         _=_:=by ring
  have hrf: Ct*Real.exp (-ct*T^2)≤Ct*Real.exp (-be*Real.sqrt h):=by
    rw[hT2,show -ct*(τ^2*Real.sqrt h)=-(ct*τ^2)*Real.sqrt h by ring]
    exact mul_le_mul_of_nonneg_left (hexp _ hbect) hCt.le
  have hrg:Cm*Real.exp (-cm*T^2)≤Cm*Real.exp (-be*Real.sqrt h):=by
    rw[hT2,show -cm*(τ^2*Real.sqrt h)=-(cm*τ^2)*Real.sqrt h by ring]
    exact mul_le_mul_of_nonneg_left (hexp _ hbecm) hCm.le
  have hrelbound:(Cerr*Real.exp (-a*Real.sqrt h))*Ct≤(Cerr*Ct)*Real.exp (-be*Real.sqrt h):=by
    convert mul_le_mul_of_nonneg_left (hexp a hbea) (by positivity:0≤Cerr*Ct) using 1 <;>ring
  have hsum:=add_le_add hrelbound (add_le_add (add_le_add hrf hrg) hp')
  have hscaled:=mul_le_mul_of_nonneg_left hsum (div_nonneg hDP.le (by positivity:0≤2*Real.pi))
  convert hscaled using 1 <;>dsimp only[Ce,h] <;>ring
end WP.HigherOrder
