import WPFormalization.Analysis.OriginLeadingGaussian
import WPFormalization.Analysis.StationaryTaylorCoefficients
import WPFormalization.Volumes.ExtractionPhaseEuler
import WPFormalization.Analysis.PoissonPhaseSecondDerivative
import Mathlib.Analysis.RCLike.Sqrt
noncomputable section
namespace WP.Analysis
open Set Filter ComplexOrder
open scoped Topology
lemma origin_variance_unit_real_germ (S:ℂ→ℂ) (hS:AnalyticAt ℂ S 0)
    (hSr:∀ᶠt:ℝ in 𝓝 0,0≤t→S (t:ℂ)=(extractionS t:ℂ)):
    ∀ᶠx:ℝ in 𝓝 0,0<x→deriv S (x:ℂ)+(x:ℂ)*iteratedDeriv 2 S (x:ℂ)=((deriv WP.Psi x:ℝ):ℂ):=by
  have hE:=extractionS_origin_complex_euler S hS hSr
  have ht:Tendsto (fun x:ℝ=>(x:ℂ)) (𝓝 0) (𝓝 (0:ℂ)):=by
    simpa only[Complex.ofReal_zero] using Complex.continuous_ofReal.continuousAt.tendsto (x:=(0:ℝ))
  filter_upwards[ht.eventually hS.eventually_analyticAt,hE.eventually_nhds,eventually_lt_nhds xCritical_pos_parameter] with x hSx hloc hxc hx
  have he:(fun t:ℝ=>(t:ℂ)*deriv S (t:ℂ))=ᶠ[𝓝 x] (fun t:ℝ=>(WP.Psi t:ℂ)):=by
    filter_upwards[hloc,eventually_gt_nhds hx] with t ht htp
    exact ht htp.le
  exact euler_derivative_of_real_germ S x _ hSx
    (Psi_analyticAt_interior x ⟨hx.le,hxc⟩).differentiableAt.hasDerivAt he
lemma origin_reciprocal_gaussian_scale_real_germ (S:ℂ→ℂ) (q:ℂ→ℂ) (hS:AnalyticAt ℂ S 0)
    (hSr:∀ᶠt:ℝ in 𝓝 0,0≤t→S (t:ℂ)=(extractionS t:ℂ))
    (hq:∀z:ℂ,q z=(Complex.sqrt (deriv S z+z*iteratedDeriv 2 S z))⁻¹):
    ∀ᶠx:ℝ in 𝓝 0,0<x→q (x:ℂ)=((Real.sqrt (deriv WP.Psi x))⁻¹:ℝ):=by
  filter_upwards[origin_variance_unit_real_germ S hS hSr,eventually_lt_nhds xCritical_pos_parameter] with x hv hxc hx
  have hp:0≤(deriv WP.Psi x:ℝ):=(Psi_deriv_pos_interior x ⟨hx.le,hxc⟩).le
  rw[hq,hv hx]
  have hroot:Complex.sqrt ((deriv WP.Psi x:ℝ):ℂ)=(Real.sqrt (deriv WP.Psi x):ℂ):=by
    simpa only[Complex.ofReal_re] using Complex.sqrt_of_nonneg (show (0:ℂ)≤((deriv WP.Psi x:ℝ):ℂ) by exact_mod_cast hp)
  rw[hroot,Complex.ofReal_inv]
lemma leading_model_centered_tilt_identity (S Bc:ℂ→ℂ) (h x u q G Amp:ℂ)
    (hB:Bc x≠0)
    (hphase:S (x*Complex.exp (u*q))-S x-x*deriv S x*(u*q)=x*G)
    (hamp:Amp=Bc (x*Complex.exp (u*q))/Bc x):
    Complex.exp (-h*x*deriv S x*(u*q))*
      ((Complex.exp (h*S (x*Complex.exp (u*q)))*Bc (x*Complex.exp (u*q)))/
        (Complex.exp (h*S x)*Bc x))=Complex.exp (h*x*G)*Amp:=by
  let z:ℂ:=x*Complex.exp (u*q)
  have he:Complex.exp (-h*x*deriv S x*(u*q))*Complex.exp (h*S z)/Complex.exp (h*S x)=
      Complex.exp (h*x*G):=by
    rw[←Complex.exp_add,←Complex.exp_sub]
    apply congrArg Complex.exp
    linear_combination h*hphase
  calc
    _=(Complex.exp (-h*x*deriv S x*(u*q))*Complex.exp (h*S z)/Complex.exp (h*S x))*(Bc z/Bc x):=by
      dsimp[z]
      field_simp
      <;>ring
    _=Complex.exp (h*x*G)*Amp:=by rw[he,hamp]
lemma normalized_gaussian_argument (h x β:ℝ) (w:ℂ) (hh:0<h) (hx:0<x):
    (w/(Real.sqrt (h*x):ℂ))*((Real.sqrt β:ℂ))⁻¹=w/(Real.sqrt (h*(x*β)):ℂ):=by
  have he:Real.sqrt (h*(x*β))=Real.sqrt (h*x)*Real.sqrt β:=by
    rw[show h*(x*β)=(h*x)*β by ring,Real.sqrt_mul (by positivity:0≤h*x)]
  rw[he,Complex.ofReal_mul]
  ring
def originStandardLog (G:ℂ × ℂ → ℂ) (h x:ℝ) (w:ℂ):ℂ:=
  ((h*x:ℝ):ℂ)*G ((x:ℂ),w/(Real.sqrt (h*x):ℂ))
def originStandardAmplitude (Amp:ℂ × ℂ → ℂ) (h x:ℝ) (w:ℂ):ℂ:=
  Amp ((x:ℂ),w/(Real.sqrt (h*x):ℂ))
lemma coeff_complex_scale_left (f:ℂ→ℂ) (c:ℂ) (n:ℕ):
    WP.coeff (fun w:ℂ=>f (c*w)) n=c^n*WP.coeff f n:=by
  unfold WP.coeff
  rw[iteratedDeriv_comp_mul_left,mul_zero,mul_div_assoc]
lemma origin_standard_log_coeff (G:ℂ × ℂ → ℂ) (h x:ℝ) (n:ℕ):
    WP.coeff (originStandardLog G h x) n=
      ((h*x:ℝ):ℂ)*((Real.sqrt (h*x):ℂ))⁻¹^n*WP.coeff (fun w:ℂ=>G ((x:ℂ),w)) n:=by
  unfold originStandardLog
  rw[coeff_const_mul]
  have he:(fun w:ℂ=>G ((x:ℂ),w/(Real.sqrt (h*x):ℂ)))=
      (fun w:ℂ=>G ((x:ℂ),((Real.sqrt (h*x):ℂ))⁻¹*w)):=by funext w;congr 1;ring
  rw[he,coeff_complex_scale_left (fun z:ℂ=>G ((x:ℂ),z)) ((Real.sqrt (h*x):ℂ))⁻¹ n]
  ring
lemma origin_standard_gaussian_data_of_physical_source (S Bc:ℂ→ℂ)
    (hS:AnalyticAt ℂ S 0) (hSd:deriv S 0=2) (hBc:AnalyticAt ℂ Bc 0) (hBc0:Bc 0≠0)
    (hSr:∀ᶠt:ℝ in 𝓝 0,0≤t→S (t:ℂ)=(extractionS t:ℂ)):
    ∃(G Amp:ℂ × ℂ → ℂ)(η ρ C D K:ℝ),0<η∧η<xCritical∧0<ρ∧0<C∧0<D∧0<K∧
      (∀x:ℝ,x∈Ioo (0:ℝ) η→WP.Psi x≤K*x)∧
      ∀(h x:ℝ),0<h→x∈Ioo (0:ℝ) η→
        AnalyticOnNhd ℂ (originStandardLog G h x) (Metric.ball 0 (ρ*Real.sqrt (h*x)))∧
        AnalyticOnNhd ℂ (originStandardAmplitude Amp h x) (Metric.ball 0 (ρ*Real.sqrt (h*x)))∧
        WP.coeff (originStandardLog G h x) 0=0∧WP.coeff (originStandardLog G h x) 1=0∧
        WP.coeff (originStandardLog G h x) 2=1/2∧originStandardAmplitude Amp h x 0=1∧
        ∀w:ℂ,‖w‖≤ρ*Real.sqrt (h*x)→
          ‖originStandardLog G h x w‖≤C*‖w‖^2∧‖originStandardAmplitude Amp h x w‖≤D∧
          let z:ℂ:=(x:ℂ)*Complex.exp (w/(Real.sqrt (h*WP.euler WP.Psi x):ℂ));
          Complex.exp (-(h:ℂ)*(WP.Psi x:ℂ)*(w/(Real.sqrt (h*WP.euler WP.Psi x):ℂ)))*
            ((Complex.exp ((h:ℂ)*S z)*Bc z)/(Complex.exp ((h:ℂ)*S (x:ℂ))*Bc (x:ℂ)))=
              Complex.exp (originStandardLog G h x w)*originStandardAmplitude Amp h x w:=by
  obtain ⟨G,Amp,J,q,r,C,hr,hC,hq,hqdef,haxis,hdata⟩:=origin_leading_gaussian_local_data S Bc hS hSd hBc hBc0
  have hE:=extractionS_origin_complex_euler S hS hSr
  have hqphys:=origin_reciprocal_gaussian_scale_real_germ S q hS hSr hqdef
  have ht:Tendsto (fun x:ℝ=>(x:ℂ)) (𝓝 0) (𝓝 (0:ℂ)):=by
    simpa only[Complex.ofReal_zero] using Complex.continuous_ofReal.continuousAt.tendsto (x:=(0:ℝ))
  have hdn:∀ᶠx:ℝ in 𝓝 0,‖deriv S (x:ℂ)‖<3:=
    ht.eventually (hS.deriv.continuousAt.norm.tendsto.eventually (eventually_lt_nhds (by rw[hSd];norm_num)))
  have hbn:∀ᶠx:ℝ in 𝓝 0,Bc (x:ℂ)≠0:=ht.eventually (hBc.continuousAt.eventually_ne hBc0)
  obtain ⟨s,hs,hsloc⟩:=Metric.eventually_nhds_iff.mp ((hE.and hqphys).and (hdn.and hbn))
  let η:ℝ:=min (r/2) (min (s/2) (xCritical/2))
  let ρ:ℝ:=r/2
  have hη:0<η:=lt_min (half_pos hr) (lt_min (half_pos hs) (half_pos xCritical_pos_parameter))
  have hηr:η<r:=(min_le_left _ _).trans_lt (half_lt_self hr)
  have hηs:η<s:=((min_le_right _ _).trans (min_le_left _ _)).trans_lt (half_lt_self hs)
  have hηx:η<xCritical:=((min_le_right _ _).trans (min_le_right _ _)).trans_lt (half_lt_self xCritical_pos_parameter)
  have hρ:0<ρ:=half_pos hr
  have hρr:ρ<r:=half_lt_self hr
  have hpoint(x:ℝ)(hx:x∈Ioo (0:ℝ) η):
      ((x:ℂ)*deriv S (x:ℂ)=(WP.Psi x:ℂ))∧q (x:ℂ)=((Real.sqrt (deriv WP.Psi x))⁻¹:ℝ)∧
      ‖deriv S (x:ℂ)‖≤3∧Bc (x:ℂ)≠0:=by
    have hl:=hsloc (show dist x 0<s by rw[Real.dist_eq,sub_zero,abs_of_pos hx.1];exact hx.2.trans hηs)
    exact ⟨hl.1.1 hx.1.le,hl.1.2 hx.1,hl.2.1.le,hl.2.2⟩
  refine ⟨G,Amp,η,ρ,C,C,3,hη,hηx,hρ,hC,hC,by norm_num,?_,?_⟩
  · intro x hx
    have hp:=hpoint x hx
    have hn:=congrArg Complex.re hp.1
    have hrn:(deriv S (x:ℂ)).re≤3:=(Complex.re_le_norm _).trans hp.2.2.1
    simp only[Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero] at hn
    calc
      WP.Psi x=x*(deriv S (x:ℂ)).re:=hn.symm
      _≤x*3:=mul_le_mul_of_nonneg_left hrn hx.1.le
      _=3*x:=by ring
  · intro h x hh hx
    let t:ℝ:=Real.sqrt (h*x)
    have htx:0<h*x:=mul_pos hh hx.1
    have htpos:0<t:=Real.sqrt_pos.mpr htx
    have ht0:(t:ℂ)≠0:=by exact_mod_cast htpos.ne'
    have htsq:t^2=h*x:=Real.sq_sqrt htx.le
    have hxc:‖(x:ℂ)‖≤r:=by rw[Complex.norm_real,Real.norm_eq_abs,abs_of_pos hx.1];exact (hx.2.trans hηr).le
    have hp:=hpoint x hx
    have hu(w:ℂ)(hw:‖w‖≤ρ*t):‖w/(t:ℂ)‖≤r:=by
      rw[norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos htpos]
      exact ((div_le_iff₀ htpos).mpr hw).trans hρr.le
    have hd0:=hdata (x:ℂ) 0 hxc (by simpa using hr.le)
    have ha0:originStandardAmplitude Amp h x 0=1:=by simpa only[originStandardAmplitude,zero_div] using (haxis (x:ℂ) hxc).2.1
    have hc0:WP.coeff (originStandardLog G h x) 0=0:=by rw[origin_standard_log_coeff,hd0.2.2.2.2.2.2.2.1,mul_zero]
    have hc1:WP.coeff (originStandardLog G h x) 1=0:=by rw[origin_standard_log_coeff,hd0.2.2.2.2.2.2.2.2.1,mul_zero]
    have hc2:WP.coeff (originStandardLog G h x) 2=1/2:=by
      rw[origin_standard_log_coeff,hd0.2.2.2.2.2.2.2.2.2]
      have hsC:((h*x:ℝ):ℂ)=(t:ℂ)^2:=by rw[←Complex.ofReal_pow,htsq]
      rw[hsC]
      field_simp
      <;>rfl
    have hLa:AnalyticOnNhd ℂ (originStandardLog G h x) (Metric.ball 0 (ρ*t)):=by
      intro w hw
      have hwn:‖w‖≤ρ*t:=(show ‖w‖<ρ*t by simpa only[Metric.mem_ball,dist_zero_right] using hw).le
      have hinner:AnalyticAt ℂ (fun v:ℂ=>((x:ℂ),v/(t:ℂ))) w:=analyticAt_const.prod (analyticAt_id.div_const)
      exact analyticAt_const.mul (AnalyticAt.comp (g:=G)
        (f:=fun v:ℂ=>((x:ℂ),v/(t:ℂ))) (x:=w) ((hdata (x:ℂ) (w/(t:ℂ)) hxc (hu w hwn)).1) hinner)
    have hAa:AnalyticOnNhd ℂ (originStandardAmplitude Amp h x) (Metric.ball 0 (ρ*t)):=by
      intro w hw
      have hwn:‖w‖≤ρ*t:=(show ‖w‖<ρ*t by simpa only[Metric.mem_ball,dist_zero_right] using hw).le
      have hinner:AnalyticAt ℂ (fun v:ℂ=>((x:ℂ),v/(t:ℂ))) w:=analyticAt_const.prod (analyticAt_id.div_const)
      exact AnalyticAt.comp (g:=Amp) (f:=fun v:ℂ=>((x:ℂ),v/(t:ℂ))) (x:=w)
        ((hdata (x:ℂ) (w/(t:ℂ)) hxc (hu w hwn)).2.1) hinner
    refine ⟨hLa,hAa,hc0,hc1,hc2,ha0,?_⟩
    intro w hw
    have hd:=hdata (x:ℂ) (w/(t:ℂ)) hxc (hu w hw)
    refine ⟨?_,hd.2.2.2.2.1,?_⟩
    · unfold originStandardLog
      rw[norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos htx]
      have hb:=mul_le_mul_of_nonneg_left hd.2.2.2.1 htx.le
      rw[norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos htpos] at hb
      have he:(h*x)*(C*(‖w‖/t)^2)=C*‖w‖^2:=by rw[←htsq];field_simp
      exact hb.trans_eq he
    · let v:ℂ:=w/(Real.sqrt (h*WP.euler WP.Psi x):ℂ)
      have heq:(w/(t:ℂ))*q (x:ℂ)=v:=by
        rw[hp.2.1]
        simpa only[v,t,WP.euler,Complex.ofReal_inv] using normalized_gaussian_argument h x (deriv WP.Psi x) w hh hx.1
      have he:=leading_model_centered_tilt_identity S Bc (h:ℂ) (x:ℂ) (w/(t:ℂ)) (q (x:ℂ))
        (G ((x:ℂ),w/(t:ℂ))) (Amp ((x:ℂ),w/(t:ℂ))) hp.2.2.2 hd.2.2.2.2.2.1 hd.2.2.2.2.2.2.1
      rw[heq] at he
      have hcmean:(h:ℂ)*(x:ℂ)*deriv S (x:ℂ)=(h:ℂ)*(WP.Psi x:ℂ):=by rw[mul_assoc,hp.1]
      simpa only[originStandardLog,originStandardAmplitude,Complex.ofReal_mul,hcmean,neg_mul] using he
end WP.Analysis
