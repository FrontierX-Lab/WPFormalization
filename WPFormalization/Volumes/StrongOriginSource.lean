import WPFormalization.Analysis.OriginPhaseCircleDecay
import WPFormalization.Volumes.OriginMarkedAmplitude
import WPFormalization.Volumes.ExtractionPhaseEuler
import WPFormalization.Volumes.CriticalArcFourier
/-! One actual origin source for a fixed canonical coefficient family.
The genuine extraction phase, actual amplitude, Euler normalization,
common analytic disk, all-order coefficient-amplitude bounds and full-circle
phase decay are retained together. No optimal order is reselected here. -/
noncomputable section
namespace WP.HigherOrder
open Set Filter
open scoped Topology
lemma strong_origin_source_of_parameter_data (P:PsiTheory)(p:ℕ)
    (Ω:Set ℂ)(L:ℕ→ℂ→ℂ)(C B:ℝ)
    (hΩ:IsOpen Ω)(hcover:∀Y∈Icc (0:ℝ) y₀,(Y:ℂ)∈Ω)
    (hC:0<C)(hB:0<B)
    (hLa:∀j,AnalyticOnNhd ℂ (L j) Ω)
    (hLr:∀j Y,Y∈Icc (0:ℝ) y₀→L j (Y:ℂ)=(markedCoefficient P p j Y:ℂ))
    (hLb:∀j z,z∈Ω→‖L j z‖≤C*B^j*(j.factorial:ℝ)^2):
    ∃(S Bc:ℂ→ℂ)(ρ D Cs:ℝ),0<ρ ∧ ρ<xCritical ∧ 0<D ∧ 0<Cs ∧
      AnalyticAt ℂ S 0 ∧ S 0=0 ∧ deriv S 0=2 ∧ Bc 0=1 ∧
      (∀x∈Icc (0:ℝ) ρ,S (x:ℂ)=(extractionS x:ℂ) ∧
        (x:ℂ)*deriv S (x:ℂ)=(WP.Psi x:ℂ) ∧ Bc (x:ℂ)=(extractionB p x:ℂ)) ∧
      (∀z:ℂ,‖z‖≤ρ→AnalyticAt ℂ S z ∧ ‖S z‖≤Cs*‖z‖ ∧
        AnalyticAt ℂ Bc z ∧ ‖Bc z-1‖≤1/2 ∧ PositiveConvolution.planarInverse P z∈Ω) ∧
      (∀j,AnalyticOnNhd ℂ (originMarkedAmplitude P p j Bc L) (Metric.ball 0 ρ)) ∧
      (∀j z,‖z‖≤ρ→‖originMarkedAmplitude P p j Bc L z‖≤D*B^j*(j.factorial:ℝ)^2) ∧
      (∀x∈Ioo (0:ℝ) ρ,∀θ:ℝ,
        (S ((x:ℂ)*Complex.exp ((θ:ℂ)*Complex.I))-S (x:ℂ)).re≤-(x/2)*(1-Real.cos θ)):=by
  obtain ⟨Bc,ρ0,D,hρ0,hρ0x,hD,hBc0,hBphys,hlocal,hAa,hAb,hAr⟩:=
    origin_marked_amplitude_family_of_parameter_data P p Ω L C B hΩ hcover hC hB hLa hLr hLb
  obtain ⟨S,hSa,hS0,hSd,hSphys⟩:=Analysis.exists_extractionS_origin_complex_phase
  obtain ⟨rs,Cs,hrs,hCs,hSbound⟩:=Analysis.complex_analytic_zero_linear_bound S hSa hS0
  obtain ⟨rr,hrr,hrealball⟩:=Metric.eventually_nhds_iff.mp hSphys
  have hBcA:AnalyticAt ℂ Bc 0:=(hlocal 0 (by simpa using hρ0.le)).1
  have hBcnear:∀ᶠz:ℂ in 𝓝 0,‖Bc z-1‖<(1/2:ℝ):=by
    have hc:ContinuousAt (fun z:ℂ=>‖Bc z-1‖) 0:=(hBcA.continuousAt.sub continuous_const.continuousAt).norm
    have hz:‖Bc 0-1‖<(1/2:ℝ):=by rw[hBc0,sub_self,norm_zero];norm_num
    exact hc.tendsto.eventually (eventually_lt_nhds hz)
  obtain ⟨rb,hrb,hBcball⟩:=Metric.eventually_nhds_iff.mp hBcnear
  have hSreal:∀ᶠx:ℝ in 𝓝 0,0≤x→(S (x:ℂ)).im=0:=by
    filter_upwards[hSphys] with x hx hxp
    rw[(hx hxp).1,Complex.ofReal_im]
  obtain ⟨rc,hrc,hcircle⟩:=Analysis.origin_phase_circle_decay_of_real_germ S hSa hSd hSreal
  let ρ:ℝ:=min ρ0 (min rs (min (rr/2) (min (rb/2) (rc/2))))
  have hρ:0<ρ:=lt_min hρ0 (lt_min hrs (lt_min (by positivity) (lt_min (by positivity) (by positivity))))
  have hρ0':ρ≤ρ0:=min_le_left _ _
  have hρs:ρ≤rs:=(min_le_right _ _).trans (min_le_left _ _)
  have hρrr:ρ≤rr/2:=(min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hρrb:ρ≤rb/2:=(min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hρrc:ρ≤rc/2:=(min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hρx:ρ<xCritical:=hρ0'.trans_lt hρ0x
  refine ⟨S,Bc,ρ,D,Cs,hρ,hρx,hD,hCs,hSa,hS0,hSd,hBc0,?_,?_,?_,?_,?_⟩
  · intro x hx
    have hxi:x∈Ico (0:ℝ) xCritical:=⟨hx.1,hx.2.trans_lt hρx⟩
    have hs:=hrealball (y:=x) (by rw[Real.dist_eq,sub_zero,abs_of_nonneg hx.1];linarith[hx.2]) hx.1
    exact ⟨hs.1,hs.2,(hBphys x hxi).2⟩
  · intro z hz
    have hs:=hSbound z (hz.trans hρs)
    have hb:=hlocal z (hz.trans hρ0')
    have hn:‖Bc z-1‖≤(1/2:ℝ):=(hBcball (y:=z) (by rw[dist_zero_right];linarith)).le
    exact ⟨hs.1,hs.2,hb.1,hn,hb.2.2⟩
  · intro j
    exact (hAa j).mono (Metric.ball_subset_ball hρ0')
  · intro j z hz
    exact hAb j z (hz.trans hρ0')
  · intro x hx θ
    exact hcircle x ⟨hx.1,by linarith[hx.2]⟩ θ
end WP.HigherOrder
