import WPFormalization.HigherOrder.OriginPoissonAmplitude
import WPFormalization.Volumes.OriginSaddleMatching
import WPFormalization.Analysis.PoissonPhaseCoordinates
import WPFormalization.Analysis.PoissonPhaseCoefficient
noncomputable section
namespace WP.HigherOrder
open Set Filter
open scoped Topology
lemma actual_origin_poisson_family_with_source_analytic (P:PsiTheory) (p:ℕ)
    (Ω:Set ℂ) (L:ℕ→ℂ→ℂ) (C B:ℝ)
    (hΩ:IsOpen Ω) (hcover:∀Y∈Icc (0:ℝ) y₀,(Y:ℂ)∈Ω)
    (hC:0<C) (hB:0<B)
    (hLa:∀j,AnalyticOnNhd ℂ (L j) Ω)
    (hLr:∀j Y,Y∈Icc (0:ℝ) y₀→L j Y=(markedCoefficient P p j Y:ℂ))
    (hLb:∀j z,z∈Ω→‖L j z‖≤C*B^j*(j.factorial:ℝ)^2):
    ∃(S x Q:ℂ→ℂ)(Z:ℂ × ℂ → ℂ)(Bc:ℂ→ℂ)(R ρ D:ℝ),
      0<R∧0<ρ∧ρ<xCritical∧0<D∧
      AnalyticAt ℂ S 0∧S 0=0∧deriv S 0=2∧
      (∀ᶠt:ℝ in 𝓝 0,0≤t→S (t:ℂ)=(extractionS t:ℂ)∧
        (t:ℂ)*deriv S (t:ℂ)=(WP.Psi t:ℂ))∧
      (∀ᶠν:ℝ in 𝓝[≥] (0:ℝ),x (ν:ℂ)=(XR (densityY (2*ν)):ℂ))∧
      AnalyticOnNhd ℂ x (Metric.ball 0 R)∧AnalyticOnNhd ℂ Q (Metric.ball 0 R)∧
      AnalyticOnNhd ℂ Z (Metric.ball 0 R ×ˢ Metric.ball 0 R)∧
      x 0=0∧deriv x 0=(2:ℂ)⁻¹∧Q 0=2∧Bc 0=1∧
      (∀ν:ℂ,‖ν‖<R→x ν*deriv S (x ν)=ν∧(ν≠0→Q ν=ν/x ν)∧Z (0,ν)=0∧Z (ν,ν)=x ν)∧
      (∀u ν:ℂ,‖u‖<R→‖ν‖<R→phaseQuotient Z u ν≠0∧
        S (Z (u,ν))-u-ν*Complex.log (phaseQuotient Z u ν)=S (x ν)-ν+ν*Complex.log (Q ν))∧
      (∀j,AnalyticOnNhd ℂ (originPoissonAmplitude P p j Bc L Z)
        (Metric.ball 0 R ×ˢ Metric.ball 0 R))∧
      (∀j v,v∈Metric.ball (0:ℂ) R ×ˢ Metric.ball (0:ℂ) R→
        ‖originPoissonAmplitude P p j Bc L Z v‖≤D*B^j*(j.factorial:ℝ)^2)∧
      (∀j,AnalyticAt ℂ (originMarkedAmplitude P p j Bc L) 0)∧
      (∀j t,t∈Icc (0:ℝ) ρ → originMarkedAmplitude P p j Bc L (t:ℂ)=
        ((extractionB p t*markedCoefficient P p j (inverseY t):ℝ):ℂ))∧
      (∀j (h:ℂ)(k:ℕ),h≠0→‖(k:ℂ)/h‖<R→let ν:ℂ:=(k:ℂ)/h;
        WP.coeff (fun z=>Complex.exp (h*S z)*originMarkedAmplitude P p j Bc L z) k=
          Complex.exp (h*(S (x ν)-ν+ν*Complex.log (Q ν)))*
            WP.coeff (fun u=>Complex.exp (h*u)*originPoissonAmplitude P p j Bc L Z (u,ν)) k):=by
  obtain ⟨S,hS,hS0,hSd,hSphys⟩:=Analysis.exists_extractionS_origin_complex_phase
  have hspos:0<(deriv S 0).re:=by rw[hSd];norm_num
  obtain ⟨R,hR,x,Q,Z,q,hx,hQ,hZ,hq,hx0,hxd,hQ0,hZ0,haxes,hdata⟩:=
    Analysis.exists_poisson_phase_coordinates S hS hspos
  have hp0:(0:ℂ × ℂ)∈Metric.ball (0:ℂ) R ×ˢ Metric.ball (0:ℂ) R:=by
    constructor <;> simpa only[Metric.mem_ball,dist_zero_right,Prod.fst_zero,Prod.snd_zero,norm_zero] using hR
  have hqne:q 0≠0:=(hdata 0 0 (by simpa only[norm_zero] using hR) (by simpa only[norm_zero] using hR)).2.1
  have heq:∀ᶠv:ℂ × ℂ in 𝓝 0,phaseQuotient Z v.1 v.2=q v:=by
    filter_upwards[Metric.ball_mem_nhds (0:ℂ × ℂ) hR] with v hv
    have hn:‖v‖<R:=by simpa only[Metric.mem_ball,dist_zero_right] using hv
    have hm:max ‖v.1‖ ‖v.2‖<R:=by simpa only[Prod.norm_def] using hn
    exact (hdata v.1 v.2 ((le_max_left _ _).trans_lt hm) ((le_max_right _ _).trans_lt hm)).1
  have hU:AnalyticAt ℂ (phaseAmplitude Z (fun _:ℂ=>1)) 0:=
    Analysis.phaseAmplitude_analyticAt_zero Z q (hZ 0 hp0) hZ0 (hq 0 hp0) hqne heq _ analyticAt_const
  obtain ⟨Bc,ρ,δ,D,hρ,hρx,hδ,hD,hBc0,hBcp,hampA,hfsA,hfsB,hampR⟩:=
    origin_poisson_amplitude_family_of_parameter_data P p Ω L C B hΩ hcover hC hB hLa hLr hLb
      Z (hZ 0 hp0) hZ0 hU
  let r:ℝ:=min R δ
  have hr:0<r:=lt_min hR hδ
  have hrR:r≤R:=min_le_left _ _
  have hrδ:r≤δ:=min_le_right _ _
  have hsub:Metric.ball (0:ℂ) r ×ˢ Metric.ball (0:ℂ) r⊆
      Metric.ball (0:ℂ) δ ×ˢ Metric.ball (0:ℂ) δ:=
    Set.prod_mono (Metric.ball_subset_ball hrδ) (Metric.ball_subset_ball hrδ)
  have hsaddle:∀ᶠν:ℂ in 𝓝 0,x ν*deriv S (x ν)=ν:=by
    filter_upwards[Metric.ball_mem_nhds (0:ℂ) hR] with ν hν
    exact (haxes ν (by simpa only[Metric.mem_ball,dist_zero_right] using hν)).1
  have hEuler:∀ᶠt:ℝ in 𝓝 0,0≤t→(t:ℂ)*deriv S (t:ℂ)=(WP.Psi t:ℂ):=by
    filter_upwards[hSphys] with t ht htp
    exact (ht htp).2
  have hmatch:=Analysis.origin_saddle_matches_densityY S x hS (by rw[hSd];norm_num)
    (hx 0 (by simpa only[Metric.mem_ball,dist_zero_right,norm_zero] using hR)) hx0 hsaddle hEuler
  refine ⟨S,x,Q,Z,Bc,r,ρ,D,hr,hρ,hρx,hD,hS,hS0,hSd,hSphys,hmatch,
    hx.mono (Metric.ball_subset_ball hrR),hQ.mono (Metric.ball_subset_ball hrR),
    hZ.mono (Set.prod_mono (Metric.ball_subset_ball hrR) (Metric.ball_subset_ball hrR)),hx0,
    by simpa only[hSd] using hxd,by simpa only[hSd] using hQ0,hBc0,?_,?_,?_,?_,
    (fun j=>hampA j 0 (by simpa only[Metric.mem_ball,dist_zero_right,norm_zero] using hρ)),hampR,?_⟩
  · intro ν hν
    exact haxes ν (hν.trans_le hrR)
  · intro u ν hu hν
    obtain ⟨he,hne,hf,hp⟩:=hdata u ν (hu.trans_le hrR) (hν.trans_le hrR)
    exact ⟨by rw[he];exact hne,by simpa only[he] using hp⟩
  · intro j
    exact (hfsA j).mono hsub
  · intro j v hv
    exact hfsB j v (hsub hv)
  · intro j h k hh hν
    have hH:AnalyticAt ℂ (originMarkedAmplitude P p j Bc L) 0:=hampA j 0
      (by simpa only[Metric.mem_ball,dist_zero_right,norm_zero] using hρ)
    exact Analysis.poisson_phase_coefficient_identity S x Q Z q R hR hS hq hdata
      (originMarkedAmplitude P p j Bc L) hH h k hh (hν.trans_le hrR)
end WP.HigherOrder
