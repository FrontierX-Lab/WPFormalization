import WPFormalization.Analysis.TinyCircleCoefficient
import WPFormalization.Volumes.OriginNormalizerLower
import WPFormalization.Analysis.CoefficientSubstitution
/-! Genuine tiny-frequency coefficient comparison for the same actual
canonical family and the same optimal J. The proved factorial lower bound
absorbs the Cauchy-circle loss. The final P-only producer supplies every
source hypothesis from StrongOptimalModel, including k=0. -/
set_option maxHeartbeats 1000000
noncomputable section
namespace WP.HigherOrder
open Set Filter
open scoped Topology
lemma tiny_frequency_coefficient_comparison_of_source (P:PsiTheory)(p:ℕ)
    (S Bc:ℂ→ℂ)(L:ℕ→ℂ→ℂ)(ρs κ a d Cerr H0:ℝ)
    (hρs:0<ρs)(hρsx:ρs<xCritical)(ha:0<a)(hd:0<d)(hCerr:0<Cerr)(hH0:0<H0)
    (hS:AnalyticAt ℂ S 0)(hS0:S 0=0)(hSd:deriv S 0=2)
    (hSr:∀x∈Icc (0:ℝ) ρs,S (x:ℂ)=(extractionS x:ℂ))
    (hBr:∀x∈Icc (0:ℝ) ρs,Bc (x:ℂ)=(extractionB p x:ℂ))
    (hBn:∀x∈Icc (0:ℝ) ρs,‖Bc (x:ℂ)-1‖≤1/2)
    (hmodels:∀g:ℕ,H0≤(complexity g p:ℝ)→
      let h:ℝ:=complexity g p
      let J:=⌊κ*Real.sqrt h⌋₊
      (∀z:ℂ,‖z‖≤ρs→AnalyticAt ℂ (normalizedFiniteMarkedModel P g p S Bc L J) z) ∧
      (∀z:ℂ,‖z‖≤d/(4*Real.sqrt h)→
        ‖normalizedMarkedGenerating P g p z-normalizedFiniteMarkedModel P g p S Bc L J z‖≤
          Cerr*Real.exp (-a*Real.sqrt h))):
    ∃κlo C0 H:ℝ,0<κlo ∧ 0<C0 ∧ 0<H ∧ H0≤H ∧
      ∀g:ℕ,H≤(complexity g p:ℝ)→∀k:ℕ,(k:ℝ)≤κlo*Real.sqrt (complexity g p:ℝ)→
      let h:ℝ:=complexity g p
      let J:=⌊κ*Real.sqrt h⌋₊
      let Qn:ℝ:=Real.pi*extractionQ g p k/markedModel g p 0
      0<Qn ∧
      (‖WP.coeff (normalizedMarkedGenerating P g p) k-
          WP.coeff (normalizedFiniteMarkedModel P g p S Bc L J) k‖/Qn≤C0*Real.exp (-a*Real.sqrt h)) ∧
      ‖WP.coeff (iteratedDeriv p (Phi P g)) k/(extractionQ g p k:ℂ)-
        WP.coeff (normalizedFiniteMarkedModel P g p S Bc L J) k/(Qn:ℂ)‖≤C0*Real.exp (-a*Real.sqrt h):=by
  let d0:ℝ:=min d ρs
  let κlo:ℝ:=d0/4
  have hd0:0<d0:=lt_min hd hρs
  have hκlo:0<κlo:=by dsimp[κlo];positivity
  have hd0d:d0≤d:=min_le_left _ _
  have hd0s:d0≤ρs:=min_le_right _ _
  obtain ⟨cQ,Hq,hcQ,hHq,hQlower⟩:=Analysis.extractionQ_normalized_tiny_lower_of_source p S Bc ρs κlo
    hρs hρsx hκlo hS hS0 hSd hSr hBr hBn
  let H:ℝ:=max H0 (max Hq 1)
  have hH:0<H:=hH0.trans_le (le_max_left _ _)
  refine ⟨κlo,Cerr/cQ,H,hκlo,by positivity,hH,le_max_left _ _,?_⟩
  intro g hg k hk
  dsimp only
  let h:ℝ:=complexity g p
  let J:=⌊κ*Real.sqrt h⌋₊
  let Qn:ℝ:=Real.pi*extractionQ g p k/markedModel g p 0
  let r:ℝ:=d0/(4*Real.sqrt h)
  have hg0:H0≤h:=(le_max_left _ _).trans hg
  have hgq:Hq≤h:=((le_max_left _ _).trans (le_max_right _ _)).trans hg
  have hh1:1≤h:=((le_max_right _ _).trans (le_max_right _ _)).trans hg
  have hh:0<h:=lt_of_lt_of_le zero_lt_one hh1
  have hs:0<Real.sqrt h:=Real.sqrt_pos.mpr hh
  have hs1:1≤Real.sqrt h:=by
    have ht:=Real.sqrt_le_sqrt hh1
    simpa only[Real.sqrt_one] using ht
  have hr:0<r:=by dsimp[r];positivity
  have hrsmall:r<ρs:=by
    have hl:r≤d0/4:=div_le_div_of_nonneg_left hd0.le (by norm_num) (by nlinarith)
    have hm:d0/4≤ρs/4:=by linarith
    linarith
  have hrcap:r≤d/(4*Real.sqrt h):=div_le_div_of_nonneg_right hd0d (by positivity)
  have hm:=hmodels g hg0
  have hQ:cQ*(2*h)^k/(k.factorial:ℝ)≤Qn:=hQlower g hgq k hk
  have hQpos:0<Qn:=lt_of_lt_of_le (by positivity) hQ
  have hNana:AnalyticOnNhd ℂ (normalizedMarkedGenerating P g p) (Metric.closedBall 0 r):=by
    intro z hz
    have hn:‖z‖≤r:=by simpa only[Metric.mem_closedBall,dist_zero_right] using hz
    exact normalizedMarkedGenerating_analytic_disk P g p ρs hρsx.le z
      (by simpa only[Metric.mem_ball,dist_zero_right] using hn.trans_lt hrsmall)
  have hMana:AnalyticOnNhd ℂ (normalizedFiniteMarkedModel P g p S Bc L J) (Metric.closedBall 0 r):=by
    intro z hz
    have hn:‖z‖≤r:=by simpa only[Metric.mem_closedBall,dist_zero_right] using hz
    exact hm.1 z (hn.trans hrsmall.le)
  have he:=Analysis.tiny_circle_coefficient_error_bound
    (normalizedMarkedGenerating P g p) (normalizedFiniteMarkedModel P g p S Bc L J)
    h d0 Cerr a cQ κlo Qn k hh hd0 hCerr.le hcQ hκlo.le (by dsimp[κlo];linarith) hk hQ
    hNana hMana (fun z hz=>hm.2 z (hz.trans hrcap))
  refine ⟨hQpos,he,?_⟩
  have hst:Stable g p:=by
    have hn:0<complexity g p:=by exact_mod_cast (show (0:ℝ)<(complexity g p:ℝ) from hh)
    unfold Stable complexity at *
    omega
  have hM0:markedModel g p 0≠0:=(markedModel_pos_parameter g p hst 0 ⟨le_rfl,y₀_pos⟩).ne'
  let c:ℂ:=((Real.pi/markedModel g p 0:ℝ):ℂ)
  have hc:c≠0:=by
    dsimp only[c]
    exact Complex.ofReal_ne_zero.mpr (div_ne_zero Real.pi_ne_zero hM0)
  have hn:WP.coeff (normalizedMarkedGenerating P g p) k=c*WP.coeff (iteratedDeriv p (Phi P g)) k:=by
    have hf:normalizedMarkedGenerating P g p=(fun z:ℂ=>c*iteratedDeriv p (Phi P g) z):=by
      funext z
      unfold normalizedMarkedGenerating
      dsimp[c]
      push_cast
      ring
    rw[hf,Analysis.coeff_const_mul]
  have hscale:(Qn:ℂ)=c*(extractionQ g p k:ℂ):=by
    dsimp[Qn,c]
    push_cast
    ring
  have hratio:WP.coeff (normalizedMarkedGenerating P g p) k/(Qn:ℂ)=
      WP.coeff (iteratedDeriv p (Phi P g)) k/(extractionQ g p k:ℂ):=by
    rw[hn,hscale]
    exact mul_div_mul_left _ _ hc
  rw[←hratio,←sub_div,norm_div,Complex.norm_of_nonneg hQpos.le]
  exact he
end WP.HigherOrder

namespace WP.HigherOrder
open Set Filter
open scoped Topology
lemma actual_tiny_frequency_coefficient_model (P:PsiTheory)(p:ℕ)(hp:1≤p):
    ∃(Ω:Set ℂ)(L:ℕ→ℂ→ℂ)(C B κ κlo a H C0:ℝ)(S Bc:ℂ→ℂ),
      IsOpen Ω ∧ (∀Y∈Icc (0:ℝ) y₀,(Y:ℂ)∈Ω) ∧
      0<C ∧ 0<B ∧ 0<κ ∧ 0<κlo ∧ 0<a ∧ 0<H ∧ 0<C0 ∧
      (∀j,AnalyticOnNhd ℂ (L j) Ω) ∧ (∀z,L 0 z=1) ∧
      (∀j Y,Y∈Icc (0:ℝ) y₀→L j (Y:ℂ)=(markedCoefficient P p j Y:ℂ)) ∧
      (∀j z,z∈Ω→‖L j z‖≤C*B^j*(j.factorial:ℝ)^2) ∧
      AnalyticAt ℂ S 0 ∧ S 0=0 ∧ deriv S 0=2 ∧ Bc 0=1 ∧
      ∀g:ℕ,H≤(complexity g p:ℝ)→
        let h:ℝ:=complexity g p
        let J:=⌊κ*Real.sqrt h⌋₊
        2*B*((J:ℝ)+1)^2≤h ∧
        ∀k:ℕ,(k:ℝ)≤κlo*Real.sqrt h→
        let Qn:ℝ:=Real.pi*extractionQ g p k/markedModel g p 0
        0<Qn ∧
        ‖WP.coeff (iteratedDeriv p (Phi P g)) k/(extractionQ g p k:ℂ)-
          WP.coeff (normalizedFiniteMarkedModel P g p S Bc L J) k/(Qn:ℂ)‖≤
            C0*Real.exp (-a*Real.sqrt h):=by
  obtain ⟨Ω,L,C,B,κ,a,H,S,Bc,ρ,D,Cs,d,Csmall,DM,E,
    hΩ,hcover,hC,hB,hκ,ha,hH,hρ,hρx,hD,hCs,hd,hCsmall,hDM,hE,
    hLa,hL0,hLr,hLb,hSa,hS0,hSd,hBc0,htrace,hlocal,hAa,hAb,hcircle,hmodels⟩:=
    actual_strong_optimal_origin_model_data P p hp
  obtain ⟨κlo,C0,H1,hκlo,hC0,hH1,hHH1,htiny⟩:=
    tiny_frequency_coefficient_comparison_of_source P p S Bc L ρ κ (a/4) d Csmall H
      hρ hρx (by positivity) hd hCsmall hH hSa hS0 hSd
      (fun x hx=>(htrace x hx).1) (fun x hx=>(htrace x hx).2.2)
      (fun x hx=>(hlocal (x:ℂ) (by rw[Complex.norm_of_nonneg hx.1];exact hx.2)).2.2.2.1)
      (by
        intro g hg
        have hm:=hmodels g hg
        exact ⟨fun z hz=>(hm.2.2.2.1 z hz).1,hm.2.2.2.2.2.1⟩)
  refine ⟨Ω,L,C,B,κ,κlo,a/4,H1,C0,S,Bc,hΩ,hcover,hC,hB,hκ,hκlo,by positivity,
    hH1,hC0,hLa,hL0,hLr,hLb,hSa,hS0,hSd,hBc0,?_⟩
  intro g hg
  refine ⟨(hmodels g (hHH1.trans hg)).1,?_⟩
  intro k hk
  have ht:=htiny g hg k hk
  exact ⟨ht.1,ht.2.2⟩
end WP.HigherOrder
