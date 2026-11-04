import WPFormalization.Volumes.CriticalGaussianAmplitudes
import WPFormalization.HigherOrder.OptimalMarkedModel
import WPFormalization.Volumes.CriticalModelLens
import WPFormalization.Volumes.CriticalMorseNormalization
import WPFormalization.Volumes.CriticalAmplitudeUnits
/-! Common critical bounds for the actual pre-Morse marked model.
The normalized phase and genuine inverse lens come from the actual kernel data.
The finite model uses the same canonical coefficient family and the explicit
native order budget 2 B (J+1)^2 <= h. Its complex bound is uniform on a disk
of radius rho sqrt(h); the real-angle phase has Gaussian decay. Physical
pointwise amplitude/phase identities are proved algebraically below. These
bounds alone do not assert the still-pending actual generating-function
comparison or the final canonical extraction theorem. -/
noncomputable section
namespace WP.Analysis
open Set Filter
open scoped Topology

lemma CriticalGaussianCoordinateData.centered_phase_quadratic_bound (d:CriticalGaussianCoordinateData):
    ∃ρ C:ℝ,0<ρ ∧ 0<C ∧ ∀δ u:ℂ,‖δ‖<ρ→‖u‖<ρ→
      ‖d.kernel.centeredPhase d.L d.q (δ,u)‖≤C*‖u‖^2:=by
  let F:ℂ × ℂ→ℂ:=d.kernel.centeredPhase d.L d.q
  have hF:AnalyticAt ℂ F (0,0):=
    d.kernel.centeredPhase_analytic d.L d.q d.L_analytic d.q_analytic d.q_zero
  have hns:∀ᶠδ:ℝ in 𝓝 0,0<δ→
      (δ:ℂ)^2*d.L (δ:ℂ)=((Real.sqrt (euler Psi (XR (y₀-δ))))⁻¹:ℝ):=by
    filter_upwards[d.physical_normalization] with δ hδ hpos
    exact (hδ hpos).1
  have hsq:=d.kernel.normalization_square d.L d.L_analytic hns
  have hj:=d.kernel.centeredPhase_jets d.L d.q d.L_analytic d.q_analytic d.q_zero d.q_axis d.q_fold hsq
  have haxis:∀ᶠδ:ℂ in 𝓝 0,F (δ,0)=0:=by
    filter_upwards[hj] with δ hδ
    exact hδ.1
  have hmap:Tendsto (fun δ:ℂ=>(δ,(0:ℂ))) (𝓝 0) (𝓝 ((0,0):ℂ × ℂ)):=
    (show ContinuousAt (fun δ:ℂ=>(δ,(0:ℂ))) 0 by fun_prop).tendsto
  have hderiv:∀ᶠδ:ℂ in 𝓝 0,deriv (fun u:ℂ=>F (δ,u)) 0=0:=by
    filter_upwards[hj,hmap.eventually hF.eventually_analyticAt] with δ hδ hFa
    rw[←sndPartial_eq_deriv F (δ,0) hFa]
    exact hδ.2.1
  exact analytic_parameter_quadratic_bound F hF haxis hderiv

lemma CriticalGaussianCoordinateData.centered_exponential_bound (d:CriticalGaussianCoordinateData):
    ∃ρ C:ℝ,0<ρ ∧ 0<C ∧ ∀δ:ℂ,‖δ‖<ρ→∀h:ℝ,0<h→∀w:ℂ,
      ‖w‖<ρ*Real.sqrt h→
      ‖Complex.exp ((h:ℂ)*d.kernel.centeredPhase d.L d.q
        (δ,-Complex.I*w/(Real.sqrt h:ℂ)))‖≤Real.exp (C*‖w‖^2):=by
  obtain ⟨ρ,C,hρ,hC,hphase⟩:=d.centered_phase_quadratic_bound
  refine ⟨ρ,C,hρ,hC,?_⟩
  intro δ hδ h hh w hw
  have hs:0<Real.sqrt h:=Real.sqrt_pos.mpr hh
  have hu:‖-Complex.I*w/(Real.sqrt h:ℂ)‖<ρ:=by
    rw[norm_div,norm_mul,norm_neg,Complex.norm_I,one_mul,Complex.norm_of_nonneg hs.le]
    exact (div_lt_iff₀ hs).mpr hw
  have hb:=hphase δ _ hδ hu
  apply (Complex.norm_exp_le_exp_norm _).trans
  apply Real.exp_le_exp.mpr
  rw[norm_mul,Complex.norm_of_nonneg hh.le]
  have hm:=mul_le_mul_of_nonneg_left hb hh.le
  have he:h*(C*‖-Complex.I*w/(Real.sqrt h:ℂ)‖^2)=C*‖w‖^2:=by
    rw[norm_div,norm_mul,norm_neg,Complex.norm_I,one_mul,Complex.norm_of_nonneg hs.le,div_pow,Real.sq_sqrt hh.le]
    field_simp
  exact hm.trans_eq he
end WP.Analysis

namespace WP.Analysis
open Set Complex
lemma CriticalGaussianCoordinateData.tiltPoint_standardized (d:CriticalGaussianCoordinateData)
    (δ h:ℝ) (hh:0≤h)
    (hn:(δ:ℂ)^2*d.L (δ:ℂ)=((Real.sqrt (euler Psi (XR (y₀-δ))))⁻¹:ℝ)) (w:ℂ):
    d.tiltPoint (δ:ℂ) (-Complex.I*w/(Real.sqrt h:ℂ))=
      ((XR (y₀-δ):ℝ):ℂ)*Complex.exp (w/(Real.sqrt (h*euler Psi (XR (y₀-δ))):ℂ)):=by
  unfold CriticalGaussianCoordinateData.tiltPoint
  rw[←Complex.ofReal_sub,X_eq_ofReal_XR]
  congr 1
  congr 1
  have he:Complex.I*(-Complex.I*w/(Real.sqrt h:ℂ))*(δ:ℂ)^2*d.L (δ:ℂ)=
      w/(Real.sqrt h:ℂ)*((δ:ℂ)^2*d.L (δ:ℂ)):=by
    calc
      _=-(Complex.I^2)*(w/(Real.sqrt h:ℂ))*((δ:ℂ)^2*d.L (δ:ℂ)):=by ring
      _=_:=by rw[Complex.I_sq];ring
  rw[he,hn,Complex.ofReal_inv,Real.sqrt_mul hh,Complex.ofReal_mul]
  simp only[div_eq_mul_inv,mul_inv_rev]
  ring

lemma CriticalGaussianCoordinateData.standardized_lens_and_phase_bound
    (d:CriticalGaussianCoordinateData) (P:PsiTheory):
    ∃ρ C:ℝ,0<ρ ∧ ρ<y₀ ∧ 0<C ∧ ∀δ∈Ioo (0:ℝ) ρ,∀h:ℝ,0<h→∀w:ℂ,
      ‖w‖<ρ*Real.sqrt h→
      let u:ℂ:=-Complex.I*w/(Real.sqrt h:ℂ)
      let z:ℂ:=((XR (y₀-δ):ℝ):ℂ)*Complex.exp (w/(Real.sqrt (h*euler Psi (XR (y₀-δ))):ℂ))
      ‖z‖<xCritical ∧ PositiveConvolution.planarInverse P z=(y₀:ℂ)-(δ:ℂ)*d.q ((δ:ℂ),u) ∧
        ‖Complex.exp ((h:ℂ)*d.kernel.centeredPhase d.L d.q ((δ:ℂ),u))‖≤Real.exp (C*‖w‖^2):=by
  obtain ⟨Rl,hRl,hRly,hlens⟩:=d.q_planar_inverse_common_lens P
  obtain ⟨Rp,C,hRp,hC,hphase⟩:=d.centered_exponential_bound
  obtain ⟨Rn,hRn,hL,hq,hU,haxis,hfold,hphysical⟩:=d.common_neighborhood
  let ρ:ℝ:=min Rl (min Rp Rn)
  have hρ:0<ρ:=lt_min hRl (lt_min hRp hRn)
  have hρl:ρ≤Rl:=min_le_left _ _
  have hρp:ρ≤Rp:=(min_le_right _ _).trans (min_le_left _ _)
  have hρn:ρ≤Rn:=(min_le_right _ _).trans (min_le_right _ _)
  refine ⟨ρ,C,hρ,hρl.trans_lt hRly,hC,?_⟩
  intro δ hδ h hh w hw
  dsimp only
  let u:ℂ:=-Complex.I*w/(Real.sqrt h:ℂ)
  have hs:0<Real.sqrt h:=Real.sqrt_pos.mpr hh
  have hu:‖u‖<ρ:=by
    dsimp[u]
    rw[norm_div,norm_mul,norm_neg,Complex.norm_I,one_mul,Complex.norm_of_nonneg hs.le]
    exact (div_lt_iff₀ hs).mpr hw
  have ht:=hlens δ ⟨hδ.1,hδ.2.trans_le hρl⟩ u (hu.trans_le hρl)
  have hnorm:=(hphysical δ ⟨hδ.1,hδ.2.trans_le hρn⟩).1
  rw[d.tiltPoint_standardized δ h hh.le hnorm w] at ht
  refine ⟨ht.1,ht.2,?_⟩
  apply hphase (δ:ℂ)
  · rw[Complex.norm_of_nonneg hδ.1.le]
    exact hδ.2.trans_le hρp
  · exact hh
  · exact hw.trans_le (mul_le_mul_of_nonneg_right hρp hs.le)
end WP.Analysis

namespace WP.Analysis
open Set Filter
open scoped Topology

def CriticalGaussianCoordinateData.preMorseAmplitude (d:CriticalGaussianCoordinateData)
    (Q:ℂ→ℂ) (p:ℕ) (L:ℕ→ℂ→ℂ) (j:ℕ) (z:ℂ × ℂ):ℂ:=
  d.kernel.jointAmplitude Q p d.q z*L j ((y₀:ℂ)-z.1*d.q z)

lemma CriticalGaussianCoordinateData.pre_morse_amplitude_family
    (d:CriticalGaussianCoordinateData) (p:ℕ) (Ω:Set ℂ) (L:ℕ→ℂ→ℂ) (C B:ℝ)
    (hΩ:IsOpen Ω) (hcover:(y₀:ℂ)∈Ω) (hC:0<C) (hB:0<B)
    (hLa:∀j,AnalyticOnNhd ℂ (L j) Ω)
    (hLb:∀j z,z∈Ω→‖L j z‖≤C*B^j*(j.factorial:ℝ)^2):
    ∃(Q:ℂ→ℂ)(ρ D:ℝ),AnalyticAt ℂ Q 0 ∧ Q 0=1 ∧
      (∀ᶠδ:ℝ in 𝓝 0,0<δ→Q (δ:ℂ)=(WP.Theta (y₀-δ):ℂ)) ∧
      0<ρ ∧ 0<D ∧
      (∀j,AnalyticOnNhd ℂ (d.preMorseAmplitude Q p L j) (Metric.ball 0 ρ ×ˢ Metric.ball 0 ρ)) ∧
      (∀(j:ℕ)(δ u:ℂ),‖δ‖<ρ→‖u‖<ρ→‖d.preMorseAmplitude Q p L j (δ,u)‖≤D*B^j*(j.factorial:ℝ)^2):=by
  obtain ⟨Q,hQ,hQ0,hQr⟩:=exists_criticalThetaUnit
  let A:ℂ × ℂ→ℂ:=d.kernel.jointAmplitude Q p d.q
  let y:ℂ × ℂ→ℂ:=fun z=>(y₀:ℂ)-z.1*d.q z
  have hA:AnalyticAt ℂ A (0,0):=d.kernel.jointAmplitude_analytic Q hQ hQ0 p d.q d.q_analytic d.q_zero
  have hy:AnalyticAt ℂ y (0,0):=analyticAt_const.sub (analyticAt_fst.mul d.q_analytic)
  have hy0:y (0,0)=(y₀:ℂ):=by dsimp[y];simp only[zero_mul,sub_zero]
  obtain ⟨ρ,D,hρ,hD,hfamA,hfamB⟩:=analytic_composition_product_gevrey_two A y y₀ hA hy hy0
    Ω hΩ hcover L C B hC hB hLa hLb
  refine ⟨Q,ρ,D,hQ,hQ0,hQr,hρ,hD,?_,?_⟩
  · intro j z hz
    have hn:‖z‖<ρ:=by simpa only[Set.mem_prod,Metric.mem_ball,dist_zero_right,Prod.norm_def,max_lt_iff] using hz
    exact hfamA j z (by simpa only[Metric.mem_ball,dist_zero_right] using hn)
  · intro j δ u hδ hu
    exact hfamB j (δ,u) (by simpa only[Prod.norm_def,max_lt_iff] using And.intro hδ hu)

lemma finite_gevrey_two_sum_norm (a:ℕ→ℂ) (C B h:ℝ) (J:ℕ)
    (hC:0≤C) (hB:0<B) (hh:0<h)
    (ha:∀j,‖a j‖≤C*B^j*(j.factorial:ℝ)^2)
    (hbudget:2*B*((J:ℝ)+1)^2≤h):
    ‖∑j∈Finset.range (J+1),a j/(h:ℂ)^j‖≤2*C:=by
  let f:PowerSeries ℂ:=PowerSeries.mk a
  have hf:∀j,‖PowerSeries.coeff j f‖≤C*B^j*(j.factorial:ℝ)^2:=by
    intro j
    simpa only[f,PowerSeries.coeff_mk] using ha j
  have hz:‖((1/h:ℝ):ℂ)‖≤1/(2*B*((J:ℝ)+1)^2):=by
    rw[Complex.norm_of_nonneg (by positivity:0≤1/h)]
    exact one_div_le_one_div_of_le (by positivity) hbudget
  have ht:=complexTruncatedSeriesPolynomial_gevreyTwo_norm_bound f C B hC hB hf J ((1/h:ℝ):ℂ) hz
  convert ht using 1
  congr 1
  unfold complexTruncatedSeriesPolynomial
  apply Finset.sum_congr rfl
  intro j hj
  simp only[f,PowerSeries.coeff_mk,div_eq_mul_inv,one_mul,Complex.ofReal_inv,inv_pow]
end WP.Analysis

namespace WP.Analysis
open Set Filter
open scoped Topology

def CriticalGaussianCoordinateData.centeredFiniteMarkedModel (d:CriticalGaussianCoordinateData)
    (Q:ℂ→ℂ) (p:ℕ) (L:ℕ→ℂ→ℂ) (h:ℝ) (J:ℕ) (δ w:ℂ):ℂ:=
  let u:ℂ:=-Complex.I*w/(Real.sqrt h:ℂ)
  Complex.exp ((h:ℂ)*d.kernel.centeredPhase d.L d.q (δ,u))*
    (∑j∈Finset.range (J+1),d.preMorseAmplitude Q p L j (δ,u)/(h:ℂ)^j)/
      HigherOrder.finiteMarkedFactor L h J ((y₀:ℂ)-δ)

lemma CriticalGaussianCoordinateData.centered_finite_model_norm_bound_at
    (d:CriticalGaussianCoordinateData) (Q:ℂ→ℂ) (p:ℕ) (L:ℕ→ℂ→ℂ)
    (h B Da E:ℝ) (J:ℕ) (δ w:ℂ) (hh:0<h) (hB:0<B) (hDa:0≤Da)
    (hbudget:2*B*((J:ℝ)+1)^2≤h)
    (hden:1/2≤‖HigherOrder.finiteMarkedFactor L h J ((y₀:ℂ)-δ)‖)
    (hphase:‖Complex.exp ((h:ℂ)*d.kernel.centeredPhase d.L d.q
        (δ,-Complex.I*w/(Real.sqrt h:ℂ)))‖≤Real.exp (E*‖w‖^2))
    (hamp:∀j:ℕ,‖d.preMorseAmplitude Q p L j (δ,-Complex.I*w/(Real.sqrt h:ℂ))‖≤
      Da*B^j*(j.factorial:ℝ)^2):
    ‖d.centeredFiniteMarkedModel Q p L h J δ w‖≤4*Da*Real.exp (E*‖w‖^2):=by
  have hs:=finite_gevrey_two_sum_norm
    (fun j=>d.preMorseAmplitude Q p L j (δ,-Complex.I*w/(Real.sqrt h:ℂ))) Da B h J hDa hB hh hamp hbudget
  have hdp:0<‖HigherOrder.finiteMarkedFactor L h J ((y₀:ℂ)-δ)‖:=by linarith
  unfold CriticalGaussianCoordinateData.centeredFiniteMarkedModel
  dsimp only
  rw[norm_div,norm_mul]
  apply (div_le_iff₀ hdp).mpr
  have hm:=mul_le_mul hphase hs (norm_nonneg _) (Real.exp_pos _).le
  have hl:=mul_le_mul_of_nonneg_left hden (show 0≤4*Da*Real.exp (E*‖w‖^2) by positivity)
  nlinarith

lemma CriticalGaussianCoordinateData.centered_finite_model_uniform_bound
    (d:CriticalGaussianCoordinateData) (p:ℕ) (Ω:Set ℂ) (L:ℕ→ℂ→ℂ) (C B:ℝ)
    (hΩ:IsOpen Ω) (hcover:(y₀:ℂ)∈Ω) (hC:0<C) (hB:0<B)
    (hLa:∀j,AnalyticOnNhd ℂ (L j) Ω)
    (hLb:∀j z,z∈Ω→‖L j z‖≤C*B^j*(j.factorial:ℝ)^2):
    ∃(Q:ℂ→ℂ)(ρ D E:ℝ),AnalyticAt ℂ Q 0 ∧ Q 0=1 ∧
      (∀ᶠδ:ℝ in 𝓝 0,0<δ→Q (δ:ℂ)=(WP.Theta (y₀-δ):ℂ)) ∧
      0<ρ ∧ 0<D ∧ 0<E ∧ ∀δ:ℂ,‖δ‖<ρ→∀h:ℝ,0<h→∀J:ℕ,
      2*B*((J:ℝ)+1)^2≤h→
      1/2≤‖HigherOrder.finiteMarkedFactor L h J ((y₀:ℂ)-δ)‖→
      AnalyticOnNhd ℂ (d.centeredFiniteMarkedModel Q p L h J δ) (Metric.ball 0 (ρ*Real.sqrt h)) ∧
        ∀w:ℂ,‖w‖<ρ*Real.sqrt h→‖d.centeredFiniteMarkedModel Q p L h J δ w‖≤D*Real.exp (E*‖w‖^2):=by
  obtain ⟨Q,Ra,Da,hQa,hQ0,hQr,hRa,hDa,hAa,hAb⟩:=
    d.pre_morse_amplitude_family p Ω L C B hΩ hcover hC hB hLa hLb
  obtain ⟨Rp,E,hRp,hE,hphase⟩:=d.centered_exponential_bound
  let F:ℂ × ℂ→ℂ:=d.kernel.centeredPhase d.L d.q
  have hFa:AnalyticAt ℂ F (0,0):=d.kernel.centeredPhase_analytic d.L d.q d.L_analytic d.q_analytic d.q_zero
  obtain ⟨Rf,hRf,hFball⟩:=hFa.exists_ball_analyticOnNhd
  let ρ:ℝ:=min Rp (min Ra Rf)
  have hρ:0<ρ:=lt_min hRp (lt_min hRa hRf)
  have hρp:ρ≤Rp:=min_le_left _ _
  have hρa:ρ≤Ra:=(min_le_right _ _).trans (min_le_left _ _)
  have hρf:ρ≤Rf:=(min_le_right _ _).trans (min_le_right _ _)
  refine ⟨Q,ρ,4*Da,E,hQa,hQ0,hQr,hρ,by positivity,hE,?_⟩
  intro δ hδ h hh J hbudget hden
  have hs:0<Real.sqrt h:=Real.sqrt_pos.mpr hh
  let T:ℂ→ℂ × ℂ:=fun w=>(δ,-Complex.I*w/(Real.sqrt h:ℂ))
  have hTa:∀w:ℂ,AnalyticAt ℂ T w:=by intro w;dsimp[T];fun_prop
  have hTu(w:ℂ)(hw:‖w‖<ρ*Real.sqrt h):‖-Complex.I*w/(Real.sqrt h:ℂ)‖<ρ:=by
    rw[norm_div,norm_mul,norm_neg,Complex.norm_I,one_mul,Complex.norm_of_nonneg hs.le]
    exact (div_lt_iff₀ hs).mpr hw
  have hTprod(w:ℂ)(hw:‖w‖<ρ*Real.sqrt h):T w∈Metric.ball 0 Ra ×ˢ Metric.ball 0 Ra:=by
    have hu:=hTu w hw
    exact ⟨by simpa only[Metric.mem_ball,dist_zero_right,T] using hδ.trans_le hρa,
      by simpa only[Metric.mem_ball,dist_zero_right,T] using hu.trans_le hρa⟩
  have hFT(w:ℂ)(hw:‖w‖<ρ*Real.sqrt h):AnalyticAt ℂ (fun v:ℂ=>F (T v)) w:=by
    have hp:‖T w‖<Rf:=by
      change max ‖δ‖ ‖-Complex.I*w/(Real.sqrt h:ℂ)‖<Rf
      exact max_lt (hδ.trans_le hρf) ((hTu w hw).trans_le hρf)
    have ht:AnalyticAt ℂ F (T w):=hFball _ (by
      change dist (T w) 0<Rf
      simpa only[dist_zero_right] using hp)
    exact ht.comp (hTa w)
  refine ⟨?_,?_⟩
  · intro w hw
    have hw':‖w‖<ρ*Real.sqrt h:=by simpa only[Metric.mem_ball,dist_zero_right] using hw
    have hExp:AnalyticAt ℂ (fun v:ℂ=>Complex.exp ((h:ℂ)*F (T v))) w:=
      (analyticAt_const.mul (hFT w hw')).cexp
    have hSum:AnalyticAt ℂ (fun v:ℂ=>∑j∈Finset.range (J+1),d.preMorseAmplitude Q p L j (T v)/(h:ℂ)^j) w:=by
      apply Finset.analyticAt_fun_sum
      intro j hj
      exact ((hAa j _ (hTprod w hw')).comp (hTa w)).div_const
    exact (hExp.mul hSum).div_const
  · intro w hw
    apply d.centered_finite_model_norm_bound_at Q p L h B Da E J δ w hh hB hDa.le hbudget hden
    · exact hphase δ (hδ.trans_le hρp) h hh w
        (hw.trans_le (mul_le_mul_of_nonneg_right hρp hs.le))
    · intro j
      exact hAb j δ _ (hδ.trans_le hρa) ((hTu w hw).trans_le hρa)
end WP.Analysis

namespace WP.Analysis
open Set Filter
open scoped Topology
lemma CriticalGaussianCoordinateData.real_tilt_parameters (d:CriticalGaussianCoordinateData) (P:PsiTheory):
    ∃R:ℝ,0<R ∧ R<y₀ ∧ ∀δ∈Ioo (0:ℝ) R,∀h:ℝ,0<h→∀w:ℝ,|w|<R*Real.sqrt h→
      let u:ℂ:=-Complex.I*(w:ℂ)/(Real.sqrt h:ℂ)
      let x:ℝ:=XR (y₀-δ)*Real.exp (w/Real.sqrt (h*euler Psi (XR (y₀-δ))))
      let ε:ℝ:=y₀-inverseY x
      x∈Ioo (0:ℝ) xCritical ∧ δ/2≤ε ∧ ε≤2*δ ∧
        (δ:ℂ)*d.q ((δ:ℂ),u)=(ε:ℂ):=by
  obtain ⟨Rl,C,hRl,hRly,hC,hlens⟩:=d.standardized_lens_and_phase_bound P
  have hq0:‖d.q (0,0)-1‖<(1/2:ℝ):=by rw[d.q_zero,sub_self,norm_zero];norm_num
  have hqnear:∀ᶠz:ℂ × ℂ in 𝓝 (0,0),‖d.q z-1‖<(1/2:ℝ):=
    (d.q_analytic.continuousAt.sub continuous_const.continuousAt).norm.tendsto.eventually
      (eventually_lt_nhds hq0)
  obtain ⟨Rq,hRq,hqball⟩:=Metric.eventually_nhds_iff.mp hqnear
  let R:ℝ:=min Rl Rq
  have hR:0<R:=lt_min hRl hRq
  have hRl':R≤Rl:=min_le_left _ _
  have hRq':R≤Rq:=min_le_right _ _
  have hRy:R<y₀:=hRl'.trans_lt hRly
  refine ⟨R,hR,hRy,?_⟩
  intro δ hδ h hh w hw
  dsimp only
  let u:ℂ:=-Complex.I*(w:ℂ)/(Real.sqrt h:ℂ)
  let x:ℝ:=XR (y₀-δ)*Real.exp (w/Real.sqrt (h*euler Psi (XR (y₀-δ))))
  let ε:ℝ:=y₀-inverseY x
  have hs:0<Real.sqrt h:=Real.sqrt_pos.mpr hh
  have hu:‖u‖<R:=by
    dsimp[u]
    rw[norm_div,norm_mul,norm_neg,Complex.norm_I,one_mul,Complex.norm_real,Real.norm_eq_abs,
      Complex.norm_of_nonneg hs.le]
    exact (div_lt_iff₀ hs).mpr hw
  have hδnorm:‖(δ:ℂ)‖<R:=by rw[Complex.norm_of_nonneg hδ.1.le];exact hδ.2
  have hqclose:‖d.q ((δ:ℂ),u)-1‖<(1/2:ℝ):=by
    apply hqball
    simpa only[dist_eq_norm,Prod.mk_sub_mk,sub_zero,Prod.norm_def,max_lt_iff] using
      And.intro (hδnorm.trans_le hRq') (hu.trans_le hRq')
  have hY:y₀-δ∈Ico (0:ℝ) y₀:=⟨by linarith[hδ.2],by linarith[hδ.1]⟩
  have hYp:0<y₀-δ:=by linarith[hδ.2]
  have hxbase:0<XR (y₀-δ):=by
    have ht:=XR_strictMonoOn (show (0:ℝ)∈Iic y₀ from y₀_pos.le)
      (show y₀-δ∈Iic y₀ from hY.2.le) hYp
    simpa only[XR_zero] using ht
  have hxp:0<x:=mul_pos hxbase (Real.exp_pos _)
  have hwc:‖(w:ℂ)‖<Rl*Real.sqrt h:=by
    rw[Complex.norm_real,Real.norm_eq_abs]
    exact hw.trans_le (mul_le_mul_of_nonneg_right hRl' hs.le)
  have ht:=hlens δ ⟨hδ.1,hδ.2.trans_le hRl'⟩ h hh (w:ℂ) hwc
  dsimp only at ht
  have hxcast:((XR (y₀-δ):ℝ):ℂ)*Complex.exp ((w:ℂ)/(Real.sqrt (h*euler Psi (XR (y₀-δ))):ℂ))=(x:ℂ):=by
    rw[←Complex.ofReal_div,←Complex.ofReal_exp,←Complex.ofReal_mul]
  rw[hxcast] at ht
  have hxx:x<xCritical:=by simpa only[Complex.norm_of_nonneg hxp.le] using ht.1
  have hxi:x∈Ico (0:ℝ) xCritical:=⟨hxp.le,hxx⟩
  have hInv:PositiveConvolution.planarInverse P (x:ℂ)=(y₀:ℂ)-(δ:ℂ)*d.q ((δ:ℂ),u):=ht.2.1
  rw[PositiveConvolution.planarInverse_ofReal P x hxi] at hInv
  have he:(δ:ℂ)*d.q ((δ:ℂ),u)=(ε:ℂ):=by
    dsimp only[ε]
    push_cast
    linear_combination hInv
  have hqn:d.q ((δ:ℂ),u)=((ε/δ:ℝ):ℂ):=by
    rw[Complex.ofReal_div]
    apply (eq_div_iff (by exact_mod_cast hδ.1.ne':(δ:ℂ)≠0)).mpr
    simpa only[mul_comm] using he
  rw[hqn,←Complex.ofReal_one,←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs] at hqclose
  have hratio:=abs_lt.mp hqclose
  have hlo:(1/2:ℝ)*δ<ε:=(lt_div_iff₀ hδ.1).mp (by linarith[hratio.1]:1/2<ε/δ)
  have hhi:ε<(3/2:ℝ)*δ:=(div_lt_iff₀ hδ.1).mp (by linarith[hratio.2]:ε/δ<3/2)
  refine ⟨⟨hxp,hxx⟩,?_,?_,he⟩ <;>linarith
end WP.Analysis

namespace WP.Analysis
open Set Filter
open scoped Topology
lemma CriticalGaussianCoordinateData.centered_phase_real_decay (d:CriticalGaussianCoordinateData):
    ∃ρ:ℝ,0<ρ ∧ ∀δ:ℂ,‖δ‖<ρ→∀u:ℝ,|u|<ρ→
      (d.kernel.centeredPhase d.L d.q (δ,(u:ℂ))).re≤-u^2/4:=by
  let F:ℂ × ℂ→ℂ:=d.kernel.centeredPhase d.L d.q
  have hF:AnalyticAt ℂ F (0,0):=
    d.kernel.centeredPhase_analytic d.L d.q d.L_analytic d.q_analytic d.q_zero
  have hns:∀ᶠδ:ℝ in 𝓝 0,0<δ→
      (δ:ℂ)^2*d.L (δ:ℂ)=((Real.sqrt (euler Psi (XR (y₀-δ))))⁻¹:ℝ):=by
    filter_upwards[d.physical_normalization] with δ hδ hpos
    exact (hδ hpos).1
  have hsq:=d.kernel.normalization_square d.L d.L_analytic hns
  have hj:=d.kernel.centeredPhase_jets d.L d.q d.L_analytic d.q_analytic d.q_zero d.q_axis d.q_fold hsq
  have haxis:∀ᶠδ:ℂ in 𝓝 0,F (δ,0)=0:=by
    filter_upwards[hj] with δ hδ
    exact hδ.1
  have hmap:Tendsto (fun δ:ℂ=>(δ,(0:ℂ))) (𝓝 0) (𝓝 ((0,0):ℂ × ℂ)):=
    (show ContinuousAt (fun δ:ℂ=>(δ,(0:ℂ))) 0 by fun_prop).tendsto
  have hderiv:∀ᶠδ:ℂ in 𝓝 0,deriv (fun u:ℂ=>F (δ,u)) 0=0:=by
    filter_upwards[hj,hmap.eventually hF.eventually_analyticAt] with δ hδ hFa
    rw[←sndPartial_eq_deriv F (δ,0) hFa]
    exact hδ.2.1
  obtain ⟨G,hG,hG0,hfactor⟩:=exists_analytic_parameter_square_factor_with_value F hF haxis hderiv
  have hF2:iteratedDeriv 2 (fun u:ℂ=>F (0,u)) 0=-1:=by
    rw[←sndPartial_two_eq_iteratedDeriv F (0,0) hF]
    exact hj.self_of_nhds.2.2
  have hGzero:G (0,0)=-(1/2:ℂ):=by
    change G 0=_
    rw[hG0,hF2]
    ring
  have hnear:∀ᶠz:ℂ × ℂ in 𝓝 (0,0),‖G z+(1/2:ℂ)‖<(1/4:ℝ):=by
    have hc:ContinuousAt (fun z:ℂ × ℂ=>‖G z+(1/2:ℂ)‖) (0,0):=
      (hG.continuousAt.add continuous_const.continuousAt).norm
    have hz:‖G (0,0)+(1/2:ℂ)‖<(1/4:ℝ):=by
      rw[hGzero,neg_add_cancel,norm_zero]
      norm_num
    exact hc.tendsto.eventually (eventually_lt_nhds hz)
  obtain ⟨ρ,hρ,hball⟩:=Metric.eventually_nhds_iff.mp (hfactor.and hnear)
  refine ⟨ρ,hρ,?_⟩
  intro δ hδ u hu
  have hp:dist ((δ,(u:ℂ)):ℂ × ℂ) (0,0)<ρ:=by
    simpa only[dist_eq_norm,Prod.mk_sub_mk,sub_zero,Prod.norm_def,max_lt_iff,
      Complex.norm_real,Real.norm_eq_abs] using And.intro hδ hu
  obtain ⟨hf,hg⟩:=hball hp
  have hre:(G (δ,(u:ℂ))).re≤-(1/4:ℝ):=by
    have ht:=Complex.re_le_norm (G (δ,(u:ℂ))+(1/2:ℂ))
    norm_num [Complex.add_re] at ht
    linarith
  change (F (δ,(u:ℂ))).re≤_
  rw[hf]
  simp only[←Complex.ofReal_pow,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  nlinarith[sq_nonneg u,mul_le_mul_of_nonneg_left hre (sq_nonneg u)]

lemma CriticalGaussianCoordinateData.centered_real_exponential_decay (d:CriticalGaussianCoordinateData):
    ∃ρ:ℝ,0<ρ ∧ ∀δ:ℂ,‖δ‖<ρ→∀h:ℝ,0<h→∀t:ℝ,|t|<ρ*Real.sqrt h→
      ‖Complex.exp ((h:ℂ)*d.kernel.centeredPhase d.L d.q
        (δ,((t/Real.sqrt h:ℝ):ℂ)))‖≤Real.exp (-t^2/4):=by
  obtain ⟨ρ,hρ,hdecay⟩:=d.centered_phase_real_decay
  refine ⟨ρ,hρ,?_⟩
  intro δ hδ h hh t ht
  have hs:0<Real.sqrt h:=Real.sqrt_pos.mpr hh
  have hu:|t/Real.sqrt h|<ρ:=by
    rw[abs_div,abs_of_pos hs]
    exact (div_lt_iff₀ hs).mpr ht
  rw[Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  simp only[Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  have he:h*(-(t/Real.sqrt h)^2/4)=-t^2/4:=by
    rw[div_pow,Real.sq_sqrt hh.le]
    field_simp
  exact (mul_le_mul_of_nonneg_left (hdecay δ hδ _ hu) hh.le).trans_eq he
end WP.Analysis

namespace WP.Analysis
open Set Filter
open scoped Topology
lemma CriticalKernelUnits.jointAmplitude_physical_at (k:CriticalKernelUnits)
    (Q:ℂ→ℂ)(p:ℕ)(q:ℂ × ℂ→ℂ)(δ ε:ℝ)(u:ℂ)
    (hδ:0<δ)(hε:0<ε)(hq:(δ:ℂ)*q ((δ:ℂ),u)=(ε:ℂ))
    (hphysδ:((Real.rpow (r (y₀-δ)) ((p:ℝ)/2)*Real.sqrt (WP.A (y₀-δ)*Theta (y₀-δ)):ℝ):ℂ)=
      ((Real.rpow δ ((p:ℝ)/2):ℝ):ℂ)*k.amplitudeUnit Q p (δ:ℂ))
    (hphysε:((Real.rpow (r (y₀-ε)) ((p:ℝ)/2)*Real.sqrt (WP.A (y₀-ε)*Theta (y₀-ε)):ℝ):ℂ)=
      ((Real.rpow ε ((p:ℝ)/2):ℝ):ℂ)*k.amplitudeUnit Q p (ε:ℂ)):
    k.jointAmplitude Q p q ((δ:ℂ),u)=
      (((Real.rpow (r (y₀-ε)) ((p:ℝ)/2)*Real.sqrt (WP.A (y₀-ε)*Theta (y₀-ε)))/
        (Real.rpow (r (y₀-δ)) ((p:ℝ)/2)*Real.sqrt (WP.A (y₀-δ)*Theta (y₀-δ))):ℝ):ℂ):=by
  have hdn:(δ:ℂ)≠0:=by exact_mod_cast hδ.ne'
  have hqval:q ((δ:ℂ),u)=((ε/δ:ℝ):ℂ):=by
    rw[Complex.ofReal_div]
    apply (eq_div_iff hdn).mpr
    simpa only[mul_comm] using hq
  have hpow:Complex.exp (((p:ℂ)/2)*Complex.log ((ε/δ:ℝ):ℂ))=
      ((Real.rpow (ε/δ) ((p:ℝ)/2):ℝ):ℂ):=by
    rw[←Complex.ofReal_log (div_pos hε hδ).le,Real.rpow_eq_pow,
      Real.rpow_def_of_pos (div_pos hε hδ)]
    push_cast
    congr 1
    ring
  unfold CriticalKernelUnits.jointAmplitude
  dsimp only
  rw[hq,hqval,hpow,Real.rpow_eq_pow,Real.div_rpow hε.le hδ.le]
  simp only[Complex.ofReal_div]
  rw[hphysε,hphysδ]
  simp only[Real.rpow_eq_pow]
  have hpd:((δ^((p:ℝ)/2):ℝ):ℂ)≠0:=by
    exact_mod_cast (Real.rpow_pos_of_pos hδ ((p:ℝ)/2)).ne'
  field_simp [hpd]

lemma CriticalKernelUnits.centeredPhase_physical_at (k:CriticalKernelUnits)
    (L:ℂ→ℂ)(q:ℂ × ℂ→ℂ)(δ ε:ℝ)(u:ℂ)(hδ:0<δ)
    (hq:(δ:ℂ)*q ((δ:ℂ),u)=(ε:ℂ))
    (hphase:((extractionS (XR (y₀-ε))-extractionS (XR (y₀-δ)):ℝ):ℂ)=
      -(5/2:ℂ)*Complex.log ((ε:ℂ)/(δ:ℂ))-k.logZUnit (ε:ℂ)+k.logZUnit (δ:ℂ)):
    k.centeredPhase L q ((δ:ℂ),u)=
      ((extractionS (XR (y₀-ε))-extractionS (XR (y₀-δ)):ℝ):ℂ)-
        Complex.I*k.psiUnit (δ:ℂ)*L (δ:ℂ)*u:=by
  have hqval:q ((δ:ℂ),u)=(ε:ℂ)/(δ:ℂ):=by
    apply (eq_div_iff (by exact_mod_cast hδ.ne' : (δ:ℂ)≠0)).mpr
    simpa only[mul_comm] using hq
  unfold CriticalKernelUnits.centeredPhase
  dsimp only
  rw[hq,hqval,←hphase]
end WP.Analysis
