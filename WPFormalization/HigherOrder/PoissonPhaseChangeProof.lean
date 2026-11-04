import WPFormalization.Analysis.PoissonPhaseCoordinates
import WPFormalization.Analysis.PoissonPhaseCoefficient
import WPFormalization.Analysis.PoissonPhaseAmplitude
noncomputable section
namespace WP
open Set Filter
open scoped Topology
theorem analytic_phase_change_complex_proof (S : ℂ → ℂ) (hS : AnalyticAt ℂ S 0) (hspos : 0 < (deriv S 0).re) :
    ∃ R : ℝ, 0 < R ∧ ∃ x Q : ℂ → ℂ, ∃ Z : ℂ × ℂ → ℂ,
      AnalyticOnNhd ℂ x (Metric.ball 0 R) ∧
      AnalyticOnNhd ℂ Q (Metric.ball 0 R) ∧
      AnalyticOnNhd ℂ Z (Metric.ball 0 R ×ˢ Metric.ball 0 R) ∧
      x 0 = 0 ∧ deriv x 0 = (deriv S 0)⁻¹ ∧ Q 0 = deriv S 0 ∧
      (∀ ν : ℂ, ‖ν‖ < R → x ν*deriv S (x ν) = ν ∧
        (ν ≠ 0 → Q ν = ν/x ν) ∧ Z (0,ν) = 0 ∧ Z (ν,ν) = x ν) ∧
      (∀ u ν : ℂ, ‖u‖ < R → ‖ν‖ < R →
        phaseQuotient Z u ν ≠ 0 ∧
        S (Z (u,ν))-u-ν*Complex.log (phaseQuotient Z u ν) =
          S (x ν)-ν+ν*Complex.log (Q ν)) ∧
      (∀ H : ℂ → ℂ, AnalyticAt ℂ H 0 → ∃ δ : ℝ, 0 < δ ∧
        AnalyticOnNhd ℂ (phaseAmplitude Z H) (Metric.ball 0 δ ×ˢ Metric.ball 0 δ) ∧
        ∀ h : ℂ, ∀ k : ℕ, h ≠ 0 → ‖(k : ℂ)/h‖ < δ →
          let ν : ℂ := (k : ℂ)/h
          coeff (fun z => Complex.exp (h*S z)*H z) k =
            Complex.exp (h*(S (x ν)-ν+ν*Complex.log (Q ν))) *
              coeff (fun u => Complex.exp (h*u)*phaseAmplitude Z H (u,ν)) k) := by
  obtain ⟨R,hR,x,Q,Z,q,hx,hQ,hZ,hq,hx0,hxd,hQ0,hZ0,haxes,hdata⟩:=
    Analysis.exists_poisson_phase_coordinates S hS hspos
  refine ⟨R,hR,x,Q,Z,hx,hQ,hZ,hx0,hxd,hQ0,haxes,?_,?_⟩
  · intro u ν hu hν
    obtain ⟨he,hne,hf,hp⟩:=hdata u ν hu hν
    exact ⟨by rw[he];exact hne,by simpa only[he] using hp⟩
  · intro H hH
    have hp0:(0:ℂ × ℂ)∈Metric.ball (0:ℂ) R ×ˢ Metric.ball (0:ℂ) R:=by
      constructor <;> simpa only[Metric.mem_ball,dist_zero_right,Prod.fst_zero,Prod.snd_zero,norm_zero] using hR
    have hqne:q 0≠0:=(hdata 0 0 (by simpa only[norm_zero] using hR) (by simpa only[norm_zero] using hR)).2.1
    have heq:∀ᶠv:ℂ × ℂ in 𝓝 0,phaseQuotient Z v.1 v.2=q v:=by
      filter_upwards[Metric.ball_mem_nhds (0:ℂ × ℂ) hR] with v hv
      have hn:‖v‖<R:=by simpa only[Metric.mem_ball,dist_zero_right] using hv
      have hm:max ‖v.1‖ ‖v.2‖<R:=by simpa only[Prod.norm_def] using hn
      exact (hdata v.1 v.2 ((le_max_left _ _).trans_lt hm) ((le_max_right _ _).trans_lt hm)).1
    have hAmp:AnalyticAt ℂ (phaseAmplitude Z H) 0:=
      Analysis.phaseAmplitude_analyticAt_zero Z q (hZ 0 hp0) hZ0 (hq 0 hp0) hqne heq H hH
    obtain ⟨r,hr,hball⟩:=Metric.eventually_nhds_iff.mp hAmp.eventually_analyticAt
    let δ:=min R r
    have hδ:0<δ:=lt_min hR hr
    refine ⟨δ,hδ,?_,?_⟩
    · intro v hv
      have hu:‖v.1‖<δ:=by simpa only[Metric.mem_ball,dist_zero_right] using hv.1
      have hν:‖v.2‖<δ:=by simpa only[Metric.mem_ball,dist_zero_right] using hv.2
      apply hball
      simpa only[dist_zero_right,Prod.norm_def] using (max_lt hu hν).trans_le (min_le_right R r)
    · intro h k hh hk
      have hν:‖(k:ℂ)/h‖<R:=hk.trans_le (min_le_left R r)
      exact Analysis.poisson_phase_coefficient_identity S x Q Z q R hR hS hq hdata H hH h k hh hν
theorem analytic_phase_change_proof (S : ℂ → ℂ) (hS : AnalyticAt ℂ S 0) (hzero : S 0 = 0)
    (hsreal : (deriv S 0).im = 0) (hspos : 0 < (deriv S 0).re) :
    ∃ R : ℝ, 0 < R ∧ ∃ x Q : ℂ → ℂ, ∃ Z : ℂ × ℂ → ℂ,
      AnalyticOnNhd ℂ x (Metric.ball 0 R) ∧
      AnalyticOnNhd ℂ Q (Metric.ball 0 R) ∧
      AnalyticOnNhd ℂ Z (Metric.ball 0 R ×ˢ Metric.ball 0 R) ∧
      x 0 = 0 ∧ deriv x 0 = (deriv S 0)⁻¹ ∧ Q 0 = deriv S 0 ∧
      (∀ ν : ℂ, ‖ν‖ < R → x ν*deriv S (x ν) = ν ∧
        (ν ≠ 0 → Q ν = ν/x ν) ∧ Z (0,ν) = 0 ∧ Z (ν,ν) = x ν) ∧
      (∀ u ν : ℂ, ‖u‖ < R → ‖ν‖ < R →
        phaseQuotient Z u ν ≠ 0 ∧
        S (Z (u,ν))-u-ν*Complex.log (phaseQuotient Z u ν) =
          S (x ν)-ν+ν*Complex.log (Q ν)) ∧
      (∀ H : ℂ → ℂ, AnalyticAt ℂ H 0 → ∃ δ : ℝ, 0 < δ ∧
        AnalyticOnNhd ℂ (phaseAmplitude Z H) (Metric.ball 0 δ ×ˢ Metric.ball 0 δ) ∧
        ∀ h k : ℕ, 1 ≤ h → (k : ℝ)/h < δ →
          let ν : ℂ := (k : ℂ)/h
          coeff (fun z => Complex.exp (h*S z)*H z) k =
            Complex.exp (h*(S (x ν)-ν+ν*Complex.log (Q ν))) *
              coeff (fun u => Complex.exp (h*u)*phaseAmplitude Z H (u,ν)) k) := by
  obtain ⟨R,hR,x,Q,Z,hx,hQ,hZ,hx0,hxd,hQ0,haxes,hphase,hamp⟩:=
    analytic_phase_change_complex_proof S hS hspos
  refine ⟨R,hR,x,Q,Z,hx,hQ,hZ,hx0,hxd,hQ0,haxes,hphase,?_⟩
  intro H hH
  obtain ⟨δ,hδ,hAmp,hcoeff⟩:=hamp H hH
  refine ⟨δ,hδ,hAmp,?_⟩
  intro h k hh hk
  have hh0:(h:ℂ)≠0:=by exact_mod_cast (show h≠0 by omega)
  apply hcoeff (h:ℂ) k hh0
  simpa only[norm_div,Complex.norm_natCast] using hk

end WP
