import WPFormalization.Analysis.HarmonicDamped
import WPFormalization.Analysis.HarmonicCentral
/-! A quantitative Fourier difference estimate and the uniform relative ratio
for two bounded displacements from the same sum mean. This does not assert
a relative Gaussian approximation for each individual probability. -/
noncomputable section
namespace WP.Analysis
open MeasureTheory Filter Set Complex
open scoped Topology
lemma harmonicFourier_weighted_l1_rate : ∃D:ℝ,0<D ∧∀Y∈Icc (0:ℝ) y₀,∀h:ℕ,2≤h→
    Integrable (fun t:ℝ=>|t| *‖scaledHarmonicFourier Y h t-harmonicGaussianKernel Y t‖) volume ∧
    (∫t:ℝ,|t| *‖scaledHarmonicFourier Y h t-harmonicGaussianKernel Y t‖)≤D/Real.sqrt (h:ℝ) := by
  obtain ⟨δ,C,β,γ,ρ,hδ,hC,hβ,hγ,hρ,hρ1,hpoint⟩:=harmonicFourier_damped_envelope
  obtain ⟨G,hG,hGeo⟩:=geometric_weight_uniform_rate ρ hρ hρ1
  let I₄:ℝ:=∫t:ℝ,|t|^4*Real.exp (-β*t^2)
  let I₂:ℝ:=∫t:ℝ,|t|^2*Real.exp (-γ*t^2)
  have hI₄:0≤I₄:=integral_nonneg (fun t=>by positivity)
  have hI₂:0≤I₂:=integral_nonneg (fun t=>by positivity)
  let D:ℝ:=C*I₄+G+I₂/δ+1
  refine ⟨D,by dsimp[D];positivity,?_⟩
  intro Y hY h hh
  have hhpos:0<h:=by omega
  let r:=Real.sqrt (h:ℝ)
  have hr:0<r:=Real.sqrt_pos.mpr (by exact_mod_cast hhpos)
  have hI:= (abs_pow_gaussian_integrable β hβ 4).const_mul (C/r)
  have hO:=geometric_weight_integrable ρ h
  have hT:=gaussian_tail_weight_integrable δ γ hγ h
  have hF:= (hI.add hO).add hT
  have hBound (t:ℝ):|t| *‖scaledHarmonicFourier Y h t-harmonicGaussianKernel Y t‖≤
      (C/r)*(|t|^4*Real.exp (-β*t^2))+|t| *geometricOuterEnvelope ρ h t+|t| *gaussianOuterTail δ γ h t := by
    have he:=mul_le_mul_of_nonneg_left (hpoint Y hY h hh t) (abs_nonneg t)
    convert he using 1 <;> dsimp[r] <;> ring
  have hMeas:AEStronglyMeasurable (fun t:ℝ=>|t| *‖scaledHarmonicFourier Y h t-harmonicGaussianKernel Y t‖) volume:=
    continuous_abs.aestronglyMeasurable.mul (((scaledHarmonicFourier_integrable Y hY h).aestronglyMeasurable.sub
      (harmonicGaussianKernel_integrable Y hY).aestronglyMeasurable).norm)
  have hSmall:Integrable (fun t:ℝ=>|t| *‖scaledHarmonicFourier Y h t-harmonicGaussianKernel Y t‖) volume:=by
    apply hF.mono' hMeas
    apply ae_of_all
    intro t
    rw[Real.norm_eq_abs,abs_of_nonneg (by positivity)]
    exact hBound t
  refine ⟨hSmall,?_⟩
  calc _≤∫t:ℝ,(C/r)*(|t|^4*Real.exp (-β*t^2))+|t| *geometricOuterEnvelope ρ h t+|t| *gaussianOuterTail δ γ h t :=
          integral_mono hSmall hF hBound
       _=(C/r)*I₄+(∫t:ℝ,|t| *geometricOuterEnvelope ρ h t)+(∫t:ℝ,|t| *gaussianOuterTail δ γ h t):=by
          have h1:=integral_add hI hO
          have h2:=integral_add (hI.add hO) hT
          simp only [Pi.add_apply] at h1 h2
          rw[h2,h1,integral_const_mul]
       _≤(C/r)*I₄+G/r+(1/(δ*r))*I₂ :=
          add_le_add (add_le_add le_rfl (hGeo h hhpos)) (gaussian_tail_weight_bound δ γ hδ hγ h hhpos)
       _=(C*I₄+G+I₂/δ)/r:=by ring
       _≤D/r:=div_le_div_of_nonneg_right (by dsimp[D];linarith) hr.le
end WP.Analysis
namespace WP.Analysis
open MeasureTheory Filter Set Complex
open scoped Topology
lemma harmonicFourier_phase_difference_error : ∃D:ℝ,0<D ∧∀Y∈Icc (0:ℝ) y₀,∀h:ℕ,2≤h→∀p q:ℝ,
    ‖∫t:ℝ,(Complex.exp (-(p:ℂ)*(t:ℂ)*Complex.I)-Complex.exp (-(q:ℂ)*(t:ℂ)*Complex.I))*
      (scaledHarmonicFourier Y h t-harmonicGaussianKernel Y t)‖≤D*|p-q|/Real.sqrt (h:ℝ) := by
  obtain ⟨D,hD,hrate⟩:=harmonicFourier_weighted_l1_rate
  refine ⟨D,hD,?_⟩
  intro Y hY h hh p q
  have hdiff:Integrable (fun t=>scaledHarmonicFourier Y h t-harmonicGaussianKernel Y t) volume:=
    (scaledHarmonicFourier_integrable Y hY h).sub (harmonicGaussianKernel_integrable Y hY)
  have hIp:=real_fourier_phase_mul_integrable p _ hdiff
  have hIq:=real_fourier_phase_mul_integrable q _ hdiff
  have hI:Integrable (fun t:ℝ=>(Complex.exp (-(p:ℂ)*(t:ℂ)*Complex.I)-Complex.exp (-(q:ℂ)*(t:ℂ)*Complex.I))*
      (scaledHarmonicFourier Y h t-harmonicGaussianKernel Y t)) volume := by
    convert hIp.sub hIq using 1
    ext t
    simp only [Pi.sub_apply]
    ring
  have hB:=hrate Y hY h hh
  calc _≤∫t:ℝ,‖(Complex.exp (-(p:ℂ)*(t:ℂ)*Complex.I)-Complex.exp (-(q:ℂ)*(t:ℂ)*Complex.I))*
          (scaledHarmonicFourier Y h t-harmonicGaussianKernel Y t)‖:=norm_integral_le_integral_norm _
       _≤∫t:ℝ,|p-q| *(|t| *‖scaledHarmonicFourier Y h t-harmonicGaussianKernel Y t‖):=by
          apply integral_mono hI.norm (hB.1.const_mul _)
          intro t
          dsimp only
          rw[norm_mul]
          calc _≤(|p-q| *|t|)*‖scaledHarmonicFourier Y h t-harmonicGaussianKernel Y t‖:=
                   mul_le_mul_of_nonneg_right (phase_difference_bound p q t) (norm_nonneg _)
               _=_:=by ring
       _=|p-q| *(∫t:ℝ,|t| *‖scaledHarmonicFourier Y h t-harmonicGaussianKernel Y t‖):=integral_const_mul _ _
       _≤|p-q| *(D/Real.sqrt (h:ℝ)):=mul_le_mul_of_nonneg_left hB.2 (abs_nonneg _)
       _=_:=by ring
end WP.Analysis
namespace WP.Analysis
open MeasureTheory Filter Set Complex
open scoped Topology
lemma harmonicSumMass_scaled_error_integral (Y:ℝ)(hY:Y∈Icc 0 y₀)(h m:ℕ)(hh:0<h):
    let r:=Real.sqrt (h:ℝ)
    let q:=((m:ℝ)-3*(h:ℝ)/2)/r
    ((r:ℂ)*(harmonicSumMass Y h m:ℂ))-
      ((Real.exp (-q^2/(2*harmonicVariance Y))/Real.sqrt (2*Real.pi*harmonicVariance Y):ℝ):ℂ) =
    ((2*Real.pi:ℝ):ℂ)⁻¹ * ∫t:ℝ,Complex.exp (-(q:ℂ)*(t:ℂ)*Complex.I)*
      (scaledHarmonicFourier Y h t-harmonicGaussianKernel Y t) := by
  dsimp only
  let q:=((m:ℝ)-3*(h:ℝ)/2)/Real.sqrt (h:ℝ)
  have hM:=harmonicSumMass_scaled_fourier Y hY h m hh
  have hG:=gaussian_fourier_normalized (harmonicVariance Y) q (harmonicVariance_pos Y hY)
  have hI:=real_fourier_phase_mul_integrable q _ (scaledHarmonicFourier_integrable Y hY h)
  have hJ:=real_fourier_phase_mul_integrable q _ (harmonicGaussianKernel_integrable Y hY)
  have hSub: (∫t:ℝ,Complex.exp (-(q:ℂ)*(t:ℂ)*Complex.I)*
      (scaledHarmonicFourier Y h t-harmonicGaussianKernel Y t))=
      (∫t:ℝ,Complex.exp (-(q:ℂ)*(t:ℂ)*Complex.I)*scaledHarmonicFourier Y h t)-
      (∫t:ℝ,Complex.exp (-(q:ℂ)*(t:ℂ)*Complex.I)*harmonicGaussianKernel Y t):=by
    rw[←integral_sub hI hJ]
    apply integral_congr_ae
    exact ae_of_all _ (fun t=>by simp only[Pi.sub_apply];ring)
  rw[hM,←hG,hSub,mul_sub]
  rfl

lemma harmonicSumMass_scaled_difference_error : ∃D:ℝ,0<D ∧∀Y∈Icc (0:ℝ) y₀,∀h:ℕ,2≤h→∀m n:ℕ,
    let r:=Real.sqrt (h:ℝ)
    let qm:=((m:ℝ)-3*(h:ℝ)/2)/r
    let qn:=((n:ℝ)-3*(h:ℝ)/2)/r
    |r*(harmonicSumMass Y h m-harmonicSumMass Y h n)-
      (Real.exp (-qm^2/(2*harmonicVariance Y))/Real.sqrt (2*Real.pi*harmonicVariance Y)-
       Real.exp (-qn^2/(2*harmonicVariance Y))/Real.sqrt (2*Real.pi*harmonicVariance Y))|≤
      D*|(m:ℝ)-n|/(h:ℝ) := by
  obtain ⟨D,hD,herror⟩:=harmonicFourier_phase_difference_error
  refine ⟨D/(2*Real.pi),by positivity,?_⟩
  intro Y hY h hh m n
  dsimp only
  have hhpos:0<h:=by omega
  let r:=Real.sqrt (h:ℝ)
  let qm:=((m:ℝ)-3*(h:ℝ)/2)/r
  let qn:=((n:ℝ)-3*(h:ℝ)/2)/r
  let gm:=Real.exp (-qm^2/(2*harmonicVariance Y))/Real.sqrt (2*Real.pi*harmonicVariance Y)
  let gn:=Real.exp (-qn^2/(2*harmonicVariance Y))/Real.sqrt (2*Real.pi*harmonicVariance Y)
  let E:=fun t:ℝ=>scaledHarmonicFourier Y h t-harmonicGaussianKernel Y t
  have hr:0<r:=Real.sqrt_pos.mpr (by exact_mod_cast hhpos)
  have hrs:r^2=(h:ℝ):=Real.sq_sqrt (by positivity)
  have hdiff:Integrable E volume:=(scaledHarmonicFourier_integrable Y hY h).sub (harmonicGaussianKernel_integrable Y hY)
  have hIm:=real_fourier_phase_mul_integrable qm E hdiff
  have hIn:=real_fourier_phase_mul_integrable qn E hdiff
  have hSub:(∫t:ℝ,(Complex.exp (-(qm:ℂ)*(t:ℂ)*Complex.I)-Complex.exp (-(qn:ℂ)*(t:ℂ)*Complex.I))*E t)=
      (∫t:ℝ,Complex.exp (-(qm:ℂ)*(t:ℂ)*Complex.I)*E t)-
      (∫t:ℝ,Complex.exp (-(qn:ℂ)*(t:ℂ)*Complex.I)*E t):=by
    rw[←integral_sub hIm hIn]
    apply integral_congr_ae
    exact ae_of_all _ (fun t=>by simp only[Pi.sub_apply];ring)
  have hMm:=harmonicSumMass_scaled_error_integral Y hY h m hhpos
  have hMn:=harmonicSumMass_scaled_error_integral Y hY h n hhpos
  change (r:ℂ)*(harmonicSumMass Y h m:ℂ)-(gm:ℂ)=
    ((2*Real.pi:ℝ):ℂ)⁻¹*(∫t:ℝ,Complex.exp (-(qm:ℂ)*(t:ℂ)*Complex.I)*E t) at hMm
  change (r:ℂ)*(harmonicSumMass Y h n:ℂ)-(gn:ℂ)=
    ((2*Real.pi:ℝ):ℂ)⁻¹*(∫t:ℝ,Complex.exp (-(qn:ℂ)*(t:ℂ)*Complex.I)*E t) at hMn
  have he:((r*(harmonicSumMass Y h m-harmonicSumMass Y h n)-(gm-gn):ℝ):ℂ)=
    ((2*Real.pi:ℝ):ℂ)⁻¹*(∫t:ℝ,(Complex.exp (-(qm:ℂ)*(t:ℂ)*Complex.I)-Complex.exp (-(qn:ℂ)*(t:ℂ)*Complex.I))*E t):=by
    rw[hSub,mul_sub]
    calc _=((r:ℂ)*(harmonicSumMass Y h m:ℂ)-(gm:ℂ))-
          ((r:ℂ)*(harmonicSumMass Y h n:ℂ)-(gn:ℂ)):=by push_cast;ring
         _=_:=by rw[hMm,hMn];ring
  have hNorm:=congrArg norm he
  rw[Complex.norm_real,Real.norm_eq_abs,norm_mul,norm_inv,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos (show 0<2*Real.pi by positivity)] at hNorm
  have hErr:=herror Y hY h hh qm qn
  have hq:qm-qn=((m:ℝ)-n)/r:=by dsimp[qm,qn];ring
  change |r*(harmonicSumMass Y h m-harmonicSumMass Y h n)-(gm-gn)|≤_
  rw[hNorm]
  calc _≤(2*Real.pi)⁻¹*(D*|qm-qn|/r):=mul_le_mul_of_nonneg_left hErr (by positivity)
       _=(D/(2*Real.pi))*|(m:ℝ)-n|/(h:ℝ):=by
         rw[hq,abs_div,abs_of_pos hr,←hrs]
         field_simp
         <;>ring
end WP.Analysis

noncomputable section
namespace WP.Analysis
open MeasureTheory Filter Set
lemma abs_exp_neg_sub_one_le (x:ℝ)(hx:0≤x):|Real.exp (-x)-1|≤x := by
  have he:Real.exp (-x)≤1:=Real.exp_le_one_iff.mpr (by linarith)
  rw[abs_of_nonpos (by linarith:Real.exp (-x)-1≤0)]
  linarith [Real.add_one_le_exp (-x)]
lemma bounded_gaussian_difference (c v L r H d e:ℝ)(hc:0<c)(hcv:c≤v)(hL:0≤L)
    (hr:0<r)(hrs:r^2=H)(hd:|d|≤L)(he:|e|≤L):
    |Real.exp (-(d/r)^2/(2*v))/Real.sqrt (2*Real.pi*v)-
     Real.exp (-(e/r)^2/(2*v))/Real.sqrt (2*Real.pi*v)|≤
      (L^2/(c*Real.sqrt (2*Real.pi*c)))/H := by
  have hv:0<v:=lt_of_lt_of_le hc hcv
  have hH:0<H:=by nlinarith
  have hd2:d^2≤L^2:=by nlinarith [sq_abs d,abs_nonneg d]
  have he2:e^2≤L^2:=by nlinarith [sq_abs e,abs_nonneg e]
  let x:=d^2/(2*H*v)
  let y:=e^2/(2*H*v)
  have hx:0≤x:=by dsimp[x];positivity
  have hy:0≤y:=by dsimp[y];positivity
  have hE:|Real.exp (-x)-Real.exp (-y)|≤x+y:=by
    have htri:=abs_sub_le (Real.exp (-x)) 1 (Real.exp (-y))
    rw[abs_sub_comm 1] at htri
    exact htri.trans (add_le_add (abs_exp_neg_sub_one_le x hx) (abs_exp_neg_sub_one_le y hy))
  have hxy:x+y≤L^2/(H*c):=by
    calc _=(d^2+e^2)/(2*H*v):=by dsimp[x,y];ring
         _≤(2*L^2)/(2*H*v):=div_le_div_of_nonneg_right (by linarith) (by positivity)
         _=L^2/(H*v):=by ring
         _≤L^2/(H*c):=div_le_div_of_nonneg_left (sq_nonneg L) (by positivity)
            (mul_le_mul_of_nonneg_left hcv hH.le)
  have hS:0<Real.sqrt (2*Real.pi*v):=Real.sqrt_pos.mpr (by positivity)
  have hSc:0<Real.sqrt (2*Real.pi*c):=Real.sqrt_pos.mpr (by positivity)
  have hSV:Real.sqrt (2*Real.pi*c)≤Real.sqrt (2*Real.pi*v):=Real.sqrt_le_sqrt (by gcongr)
  have hdq:-(d/r)^2/(2*v) = -x := by dsimp[x];rw[div_pow,hrs];ring
  have heq:-(e/r)^2/(2*v) = -y := by dsimp[y];rw[div_pow,hrs];ring
  rw[hdq,heq,←sub_div,abs_div,abs_of_pos hS]
  calc _≤(x+y)/Real.sqrt (2*Real.pi*v):=div_le_div_of_nonneg_right hE hS.le
       _≤(L^2/(H*c))/Real.sqrt (2*Real.pi*v):=div_le_div_of_nonneg_right hxy hS.le
       _≤(L^2/(H*c))/Real.sqrt (2*Real.pi*c):=div_le_div_of_nonneg_left (by positivity) hSc hSV
       _=_:=by ring
end WP.Analysis
namespace WP.Analysis
open MeasureTheory Filter Set Complex
open scoped Topology
lemma harmonicSumMass_bounded_displacement_ratio (L:ℝ)(hL:0≤L):
    ∃C:ℝ,0<C ∧∃h₀:ℕ,∀h≥h₀,∀Y∈Icc (0:ℝ) y₀,∀m n:ℕ,
    |(m:ℝ)-3*(h:ℝ)/2|≤L→|(n:ℝ)-3*(h:ℝ)/2|≤L→
    |harmonicSumMass Y h m/harmonicSumMass Y h n-1|≤C/(h:ℝ) := by
  obtain ⟨D,hD,herror⟩:=harmonicSumMass_scaled_difference_error
  obtain ⟨c,B,s,hc,hB,hs,hvar⟩:=harmonic_uniform_bounds
  obtain ⟨κ,hκ,h₀,hLow⟩:=harmonicSumMass_central_lower L hL
  let G:ℝ:=L^2/(c*Real.sqrt (2*Real.pi*c))
  let K:ℝ:=2*L*D+G
  have hG:0≤G:=by dsimp[G];positivity
  have hK:0≤K:=by dsimp[K];positivity
  let C:ℝ:=(K+1)/κ
  refine ⟨C,by dsimp[C];positivity,max 2 h₀,?_⟩
  intro h hhh Y hY m n hm hn
  have hh:2≤h:=(le_max_left _ _).trans hhh
  have hhpos:0<h:=by omega
  have hH:0<(h:ℝ):=by exact_mod_cast hhpos
  let r:=Real.sqrt (h:ℝ)
  let dm:ℝ:=(m:ℝ)-3*(h:ℝ)/2
  let dn:ℝ:=(n:ℝ)-3*(h:ℝ)/2
  let gm:ℝ:=Real.exp (-(dm/r)^2/(2*harmonicVariance Y))/Real.sqrt (2*Real.pi*harmonicVariance Y)
  let gn:ℝ:=Real.exp (-(dn/r)^2/(2*harmonicVariance Y))/Real.sqrt (2*Real.pi*harmonicVariance Y)
  have hr:0<r:=Real.sqrt_pos.mpr hH
  have hrs:r^2=(h:ℝ):=Real.sq_sqrt hH.le
  have hr1:1≤r:=by
    have hreal:(2:ℝ)≤h:=by exact_mod_cast hh
    nlinarith
  have hmn:|(m:ℝ)-n|≤2*L:=by
    calc _=|dm-dn|:=by congr 1;dsimp[dm,dn];ring
         _≤|dm|+|dn|:=by simpa using abs_sub_le dm 0 dn
         _≤2*L:=by linarith
  have hE:=herror Y hY h hh m n
  change |r*(harmonicSumMass Y h m-harmonicSumMass Y h n)-(gm-gn)|≤D*|(m:ℝ)-n|/(h:ℝ) at hE
  have hE':|r*(harmonicSumMass Y h m-harmonicSumMass Y h n)-(gm-gn)|≤(2*L*D)/(h:ℝ):=
    hE.trans (div_le_div_of_nonneg_right (by nlinarith [mul_le_mul_of_nonneg_left hmn hD.le]) hH.le)
  have hG':|gm-gn|≤G/(h:ℝ):=bounded_gaussian_difference c (harmonicVariance Y) L r (h:ℝ) dm dn hc
    (hvar Y hY).2.2.1 hL hr hrs hm hn
  have hDiff:r*|harmonicSumMass Y h m-harmonicSumMass Y h n|≤K/(h:ℝ):=by
    have htri:=abs_add_le (r*(harmonicSumMass Y h m-harmonicSumMass Y h n)-(gm-gn)) (gm-gn)
    rw[show r*(harmonicSumMass Y h m-harmonicSumMass Y h n)-(gm-gn)+(gm-gn)=
      r*(harmonicSumMass Y h m-harmonicSumMass Y h n) by ring,abs_mul,abs_of_pos hr] at htri
    calc _≤_:=htri
         _≤(2*L*D)/(h:ℝ)+G/(h:ℝ):=add_le_add hE' hG'
         _=K/(h:ℝ):=by dsimp[K];ring
  have hnCentral:|(n:ℝ)-3*(h:ℝ)/2|≤L*r:=hn.trans (by nlinarith)
  have hLower:=hLow h ((le_max_right _ _).trans hhh) hhpos Y hY n hnCentral
  have hp:0<harmonicSumMass Y h n:=lt_of_lt_of_le (div_pos hκ hr) hLower
  have hScaled:κ≤r*harmonicSumMass Y h n:=by
    have he:=(div_le_iff₀ hr).mp hLower
    nlinarith
  calc _=|harmonicSumMass Y h m-harmonicSumMass Y h n|/harmonicSumMass Y h n:=by
          rw[div_sub_one hp.ne',abs_div,abs_of_pos hp]
       _=(r*|harmonicSumMass Y h m-harmonicSumMass Y h n|)/(r*harmonicSumMass Y h n):=by field_simp
       _≤(K/(h:ℝ))/(r*harmonicSumMass Y h n):=div_le_div_of_nonneg_right hDiff (by positivity)
       _≤(K/(h:ℝ))/κ:=div_le_div_of_nonneg_left (by positivity) hκ hScaled
       _=(K/κ)/(h:ℝ):=by ring
       _≤C/(h:ℝ):=div_le_div_of_nonneg_right (div_le_div_of_nonneg_right (by linarith:K≤K+1) hκ.le) hH.le
end WP.Analysis
