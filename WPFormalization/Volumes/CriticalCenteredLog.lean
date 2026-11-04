import WPFormalization.Volumes.CriticalModelGrowth
import WPFormalization.Analysis.CoefficientScaling
/-! The genuine centered critical log action and leading amplitude.
The actual pre-Morse phase supplies a common analytic disk, its exact first
three jets, a uniform quadratic bound and the cubic Cauchy remainder.
The actual leading amplitude has axis value one and a common norm bound.
These local data retain the existing critical coordinate and physical domain;
they do not themselves assert the final generating-function comparison. -/
noncomputable section
namespace WP.Analysis
open Set Filter
open scoped Topology

def CriticalGaussianCoordinateData.centeredLogAction (d:CriticalGaussianCoordinateData)
    (h:ℝ)(δ:ℂ)(w:ℂ):ℂ:=
  (h:ℂ)*d.kernel.centeredPhase d.L d.q (δ,-Complex.I*w/(Real.sqrt h:ℂ))

lemma CriticalGaussianCoordinateData.centered_phase_uniform_jets (d:CriticalGaussianCoordinateData):
    ∃ρ:ℝ,0<ρ ∧
      AnalyticOnNhd ℂ (d.kernel.centeredPhase d.L d.q) (Metric.ball 0 ρ) ∧
      ∀δ:ℂ,‖δ‖<ρ→
        d.kernel.centeredPhase d.L d.q (δ,0)=0 ∧
        deriv (fun u:ℂ=>d.kernel.centeredPhase d.L d.q (δ,u)) 0=0 ∧
        iteratedDeriv 2 (fun u:ℂ=>d.kernel.centeredPhase d.L d.q (δ,u)) 0=-1:=by
  let F:ℂ × ℂ→ℂ:=d.kernel.centeredPhase d.L d.q
  have hF:AnalyticAt ℂ F (0,0):=
    d.kernel.centeredPhase_analytic d.L d.q d.L_analytic d.q_analytic d.q_zero
  have hns:∀ᶠδ:ℝ in 𝓝 0,0<δ→
      (δ:ℂ)^2*d.L (δ:ℂ)=((Real.sqrt (euler Psi (XR (y₀-δ))))⁻¹:ℝ):=by
    filter_upwards[d.physical_normalization] with δ hδ hpos
    exact (hδ hpos).1
  have hsq:=d.kernel.normalization_square d.L d.L_analytic hns
  have hj:=d.kernel.centeredPhase_jets d.L d.q d.L_analytic d.q_analytic d.q_zero d.q_axis d.q_fold hsq
  obtain ⟨Rf,hRf,hFa⟩:=hF.exists_ball_analyticOnNhd
  obtain ⟨Rj,hRj,hjball⟩:=Metric.eventually_nhds_iff.mp hj
  let ρ:ℝ:=min Rf Rj
  have hρ:0<ρ:=lt_min hRf hRj
  refine ⟨ρ,hρ,hFa.mono (Metric.ball_subset_ball (min_le_left _ _)),?_⟩
  intro δ hδ
  have hδf:‖δ‖<Rf:=hδ.trans_le (min_le_left _ _)
  have hδj:‖δ‖<Rj:=hδ.trans_le (min_le_right _ _)
  have hjet:=hjball (by simpa only[dist_zero_right] using hδj)
  have hFδ:AnalyticAt ℂ F (δ,0):=hFa _ (by
    simpa [Metric.mem_ball,dist_eq_norm,Prod.norm_def,max_lt_iff] using hδf)
  refine ⟨hjet.1,?_,?_⟩
  · exact (sndPartial_eq_deriv F (δ,0) hFδ).symm.trans hjet.2.1
  · exact (sndPartial_two_eq_iteratedDeriv F (δ,0) hFδ).symm.trans hjet.2.2

lemma CriticalGaussianCoordinateData.centeredLogAction_jets
    (d:CriticalGaussianCoordinateData)(h:ℝ)(hh:0<h)(δ:ℂ)
    (hzero:d.kernel.centeredPhase d.L d.q (δ,0)=0)
    (hone:deriv (fun u:ℂ=>d.kernel.centeredPhase d.L d.q (δ,u)) 0=0)
    (htwo:iteratedDeriv 2 (fun u:ℂ=>d.kernel.centeredPhase d.L d.q (δ,u)) 0=-1):
    d.centeredLogAction h δ 0=0 ∧ deriv (d.centeredLogAction h δ) 0=0 ∧
      iteratedDeriv 2 (d.centeredLogAction h δ) 0=1 ∧
      WP.coeff (d.centeredLogAction h δ) 2=(1/2:ℂ):=by
  let F:ℂ→ℂ:=fun u=>d.kernel.centeredPhase d.L d.q (δ,u)
  let c:ℂ:=-Complex.I/(Real.sqrt h:ℂ)
  have he:d.centeredLogAction h δ=fun w=>(h:ℂ)*F (c*w):=by
    funext w
    unfold CriticalGaussianCoordinateData.centeredLogAction
    dsimp[F,c]
    congr 2
    ring
  have hs:(Real.sqrt h:ℂ)≠0:=by exact_mod_cast (Real.sqrt_pos.mpr hh).ne'
  have hc:(h:ℂ)*c^2*(-1:ℂ)=1:=by
    dsimp[c]
    rw[div_pow,neg_sq,Complex.I_sq,←Complex.ofReal_pow,Real.sq_sqrt hh.le]
    field_simp [(by exact_mod_cast hh.ne' : (h:ℂ)≠0)]
  have h0:d.centeredLogAction h δ 0=0:=by
    rw[he]
    change (h:ℂ)*F (c*0)=0
    rw[mul_zero]
    change (h:ℂ)*d.kernel.centeredPhase d.L d.q (δ,0)=0
    rw[hzero,mul_zero]
  have h1:deriv (d.centeredLogAction h δ) 0=0:=by
    rw[he,deriv_const_mul_field,deriv_comp_mul_left,mul_zero]
    change (h:ℂ)*(c*deriv (fun u:ℂ=>d.kernel.centeredPhase d.L d.q (δ,u)) 0)=0
    rw[hone,mul_zero,mul_zero]
  have h2:iteratedDeriv 2 (d.centeredLogAction h δ) 0=1:=by
    rw[he,iteratedDeriv_const_mul_field,iteratedDeriv_comp_mul_left,mul_zero]
    change (h:ℂ)*(c^2*iteratedDeriv 2 (fun u:ℂ=>d.kernel.centeredPhase d.L d.q (δ,u)) 0)=1
    rw[htwo,←mul_assoc,hc]
  exact ⟨h0,h1,h2,by rw[WP.coeff,h2];norm_num⟩

lemma CriticalGaussianCoordinateData.centered_log_action_common_bound (d:CriticalGaussianCoordinateData):
    ∃ρ C:ℝ,0<ρ ∧ 0<C ∧ ∀δ:ℂ,‖δ‖<ρ→∀h:ℝ,0<h→
      AnalyticOnNhd ℂ (d.centeredLogAction h δ) (Metric.ball 0 (ρ*Real.sqrt h)) ∧
      d.centeredLogAction h δ 0=0 ∧ deriv (d.centeredLogAction h δ) 0=0 ∧
      WP.coeff (d.centeredLogAction h δ) 2=(1/2:ℂ) ∧
      ∀w:ℂ,‖w‖<ρ*Real.sqrt h→‖d.centeredLogAction h δ w‖≤C*‖w‖^2:=by
  obtain ⟨Rp,C,hRp,hC,hbound⟩:=d.centered_phase_quadratic_bound
  obtain ⟨Rj,hRj,hFa,hjets⟩:=d.centered_phase_uniform_jets
  let ρ:ℝ:=min Rp Rj
  have hρ:0<ρ:=lt_min hRp hRj
  have hρp:ρ≤Rp:=min_le_left _ _
  have hρj:ρ≤Rj:=min_le_right _ _
  refine ⟨ρ,C,hρ,hC,?_⟩
  intro δ hδ h hh
  have hs:0<Real.sqrt h:=Real.sqrt_pos.mpr hh
  have hu(w:ℂ)(hw:‖w‖<ρ*Real.sqrt h):‖-Complex.I*w/(Real.sqrt h:ℂ)‖<ρ:=by
    rw[norm_div,norm_mul,norm_neg,Complex.norm_I,one_mul,Complex.norm_of_nonneg hs.le]
    exact (div_lt_iff₀ hs).mpr hw
  have hj:=hjets δ (hδ.trans_le hρj)
  have ht:=d.centeredLogAction_jets h hh δ hj.1 hj.2.1 hj.2.2
  refine ⟨?_,ht.1,ht.2.1,ht.2.2.2,?_⟩
  · intro w hw
    have hw':‖w‖<ρ*Real.sqrt h:=by simpa only[Metric.mem_ball,dist_zero_right] using hw
    have hf:AnalyticAt ℂ (d.kernel.centeredPhase d.L d.q) (δ,-Complex.I*w/(Real.sqrt h:ℂ)):=hFa _ (by
      change dist ((δ,-Complex.I*w/(Real.sqrt h:ℂ)):ℂ × ℂ) 0<Rj
      simpa only[dist_zero_right,Prod.norm_def,max_lt_iff] using
        And.intro (hδ.trans_le hρj) ((hu w hw').trans_le hρj))
    have hT:AnalyticAt ℂ (fun w:ℂ=>(δ,-Complex.I*w/(Real.sqrt h:ℂ))) w:=by fun_prop
    have hcomp:AnalyticAt ℂ (fun z:ℂ=>d.kernel.centeredPhase d.L d.q
        (δ,-Complex.I*z/(Real.sqrt h:ℂ))) w:=
      AnalyticAt.comp (f:=fun z:ℂ=>(δ,-Complex.I*z/(Real.sqrt h:ℂ))) (x:=w) hf hT
    exact analyticAt_const.mul hcomp
  · intro w hw
    have hb:=hbound δ _ (hδ.trans_le hρp) ((hu w hw).trans_le hρp)
    unfold CriticalGaussianCoordinateData.centeredLogAction
    rw[norm_mul,Complex.norm_of_nonneg hh.le]
    have hm:=mul_le_mul_of_nonneg_left hb hh.le
    have he:h*(C*‖-Complex.I*w/(Real.sqrt h:ℂ)‖^2)=C*‖w‖^2:=by
      rw[norm_div,norm_mul,norm_neg,Complex.norm_I,one_mul,Complex.norm_of_nonneg hs.le,div_pow,Real.sq_sqrt hh.le]
      field_simp
    exact hm.trans_eq he
end WP.Analysis

namespace WP.Analysis
open Set Filter
open scoped Topology

def CriticalGaussianCoordinateData.leadingCenteredAmplitude (d:CriticalGaussianCoordinateData)
    (Q:ℂ→ℂ)(p:ℕ)(h:ℝ)(δ w:ℂ):ℂ:=
  d.kernel.jointAmplitude Q p d.q (δ,-Complex.I*w/(Real.sqrt h:ℂ))

lemma CriticalGaussianCoordinateData.leading_centered_amplitude_common_bound
    (d:CriticalGaussianCoordinateData)(Q:ℂ→ℂ)(hQ:AnalyticAt ℂ Q 0)(hQ0:Q 0=1)(p:ℕ):
    ∃ρ:ℝ,0<ρ ∧ ∀δ:ℂ,‖δ‖<ρ→∀h:ℝ,0<h→
      AnalyticOnNhd ℂ (d.leadingCenteredAmplitude Q p h δ) (Metric.ball 0 (ρ*Real.sqrt h)) ∧
      d.leadingCenteredAmplitude Q p h δ 0=1 ∧
      ∀w:ℂ,‖w‖<ρ*Real.sqrt h→‖d.leadingCenteredAmplitude Q p h δ w‖≤2:=by
  let A:ℂ × ℂ→ℂ:=d.kernel.jointAmplitude Q p d.q
  have hA:AnalyticAt ℂ A (0,0):=d.kernel.jointAmplitude_analytic Q hQ hQ0 p d.q d.q_analytic d.q_zero
  have hA0:A (0,0)=1:=d.kernel.jointAmplitude_zero Q hQ0 p d.q d.q_zero
  have hbound:∀ᶠz:ℂ × ℂ in 𝓝 (0,0),AnalyticAt ℂ A z ∧ ‖A z‖<2:=by
    have hc:ContinuousAt (fun z:ℂ × ℂ=>‖A z‖) (0,0):=hA.continuousAt.norm
    have hnorm:‖A (0,0)‖<(2:ℝ):=by rw[hA0,norm_one];norm_num
    exact hA.eventually_analyticAt.and (hc.tendsto.eventually (eventually_lt_nhds hnorm))
  obtain ⟨Ra,hRa,hball⟩:=Metric.eventually_nhds_iff.mp hbound
  obtain ⟨Rj,hRj,haxis⟩:=Metric.eventually_nhds_iff.mp
    (d.kernel.jointAmplitude_axis Q hQ hQ0 p d.q d.q_axis)
  let ρ:ℝ:=min Ra Rj
  have hρ:0<ρ:=lt_min hRa hRj
  have hρa:ρ≤Ra:=min_le_left _ _
  have hρj:ρ≤Rj:=min_le_right _ _
  refine ⟨ρ,hρ,?_⟩
  intro δ hδ h hh
  have hs:0<Real.sqrt h:=Real.sqrt_pos.mpr hh
  have hu(w:ℂ)(hw:‖w‖<ρ*Real.sqrt h):‖-Complex.I*w/(Real.sqrt h:ℂ)‖<ρ:=by
    rw[norm_div,norm_mul,norm_neg,Complex.norm_I,one_mul,Complex.norm_of_nonneg hs.le]
    exact (div_lt_iff₀ hs).mpr hw
  have hp(w:ℂ)(hw:‖w‖<ρ*Real.sqrt h):dist (δ,-Complex.I*w/(Real.sqrt h:ℂ)) ((0,0):ℂ × ℂ)<Ra:=by
    simpa only[dist_eq_norm,Prod.mk_sub_mk,sub_zero,Prod.norm_def,max_lt_iff] using
      And.intro (hδ.trans_le hρa) ((hu w hw).trans_le hρa)
  refine ⟨?_,?_,?_⟩
  · intro w hw
    have hn:‖w‖<ρ*Real.sqrt h:=by simpa only[Metric.mem_ball,dist_zero_right] using hw
    have hT:AnalyticAt ℂ (fun v:ℂ=>(δ,-Complex.I*v/(Real.sqrt h:ℂ))) w:=by fun_prop
    exact AnalyticAt.comp (f:=fun v:ℂ=>(δ,-Complex.I*v/(Real.sqrt h:ℂ))) (x:=w) (hball (hp w hn)).1 hT
  · unfold CriticalGaussianCoordinateData.leadingCenteredAmplitude
    simp only[mul_zero,zero_div]
    exact haxis (by simpa only[dist_zero_right] using hδ.trans_le hρj)
  · intro w hw
    exact (hball (hp w hw)).2.le
end WP.Analysis

namespace WP.Analysis
open Set Filter
open scoped Topology
lemma CriticalGaussianCoordinateData.centered_log_cubic_remainder (d:CriticalGaussianCoordinateData):
    ∃ρ C:ℝ,0<ρ ∧ 0<C ∧ ∀δ:ℂ,‖δ‖<ρ→∀h:ℝ,0<h→∀w:ℂ,
      ‖w‖≤ρ*Real.sqrt h/4→
      ‖d.centeredLogAction h δ w-w^2/2‖≤C*‖w‖^3/Real.sqrt h:=by
  obtain ⟨ρ,C,hρ,hC,hdata⟩:=d.centered_log_action_common_bound
  refine ⟨ρ,4*C/ρ,hρ,by positivity,?_⟩
  intro δ hδ h hh w hw
  obtain ⟨ha,hzero,hone,htwo,hbound⟩:=hdata δ hδ h hh
  let R:ℝ:=ρ*Real.sqrt h/2
  have hs:0<Real.sqrt h:=Real.sqrt_pos.mpr hh
  have hR:0<R:=by dsimp[R];positivity
  have hRsmall:R<ρ*Real.sqrt h:=by dsimp[R];nlinarith[mul_pos hρ hs]
  have hdiff:DifferentiableOn ℂ (d.centeredLogAction h δ) (Metric.closedBall 0 R):=by
    intro z hz
    apply (ha z _).differentiableAt.differentiableWithinAt
    have hn:‖z‖≤R:=by simpa only[Metric.mem_closedBall,dist_zero_right] using hz
    simpa only[Metric.mem_ball,dist_zero_right] using hn.trans_lt hRsmall
  have hb:∀z∈Metric.sphere (0:ℂ) R,‖d.centeredLogAction h δ z‖≤C*R^2:=by
    intro z hz
    have hn:‖z‖=R:=by simpa only[Metric.mem_sphere,dist_zero_right] using hz
    simpa only[hn] using hbound z (hn.trans_lt hRsmall)
  have hz:‖w‖≤R/2:=by dsimp[R];linarith
  have he:=complex_quadratic_remainder_bound (d.centeredLogAction h δ) R (C*R^2) hR (by positivity) hdiff hb w hz
  have hc0:WP.coeff (d.centeredLogAction h δ) 0=0:=by simpa [WP.coeff] using hzero
  have hc1:WP.coeff (d.centeredLogAction h δ) 1=0:=by simpa [WP.coeff,iteratedDeriv_one] using hone
  rw[hc0,hc1,htwo,zero_mul,zero_add,zero_add] at he
  have hnorm:(1/2:ℂ)*w^2=w^2/2:=by ring
  rw[hnorm] at he
  have hfactor:2*(C*R^2)/R^3*‖w‖^3=(4*C/ρ)*‖w‖^3/Real.sqrt h:=by
    dsimp[R]
    field_simp
    <;>ring
  exact he.trans_eq hfactor
end WP.Analysis
