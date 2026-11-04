import WPFormalization.Analysis.GaussianLatticeFourierTransfer
import WPFormalization.Analysis.GaussianTaylorRemainder
/-! A central uniform error and the two integrable tails control L1 error.
The ordinary Gaussian tail has an explicit exponential bound. -/
noncomputable section
namespace WP.Analysis
open MeasureTheory Set Complex

lemma l1_error_from_core_and_tails (f g:ℝ→ℂ)(hf:Integrable f)(hg:Integrable g)
    (T E F G:ℝ)(hT:0≤T)(hcore:∀t:ℝ,|t|≤T→‖f t-g t‖≤E)
    (hft:(∫t:ℝ in {t:ℝ|T≤|t|},‖f t‖)≤F)
    (hgt:(∫t:ℝ in {t:ℝ|T≤|t|},‖g t‖)≤G):
    (∫t:ℝ,‖f t-g t‖)≤2*T*E+F+G:=by
  let A:Set ℝ:=Icc (-T) T
  let B:Set ℝ:={t:ℝ|T≤|t|}
  have hA:MeasurableSet A:=measurableSet_Icc
  have hB:MeasurableSet B:=(isClosed_le continuous_const continuous_abs).measurableSet
  have hcomp:Aᶜ⊆B:=by
    intro t ht
    change T≤|t|
    by_contra hh
    apply ht
    exact abs_le.mp (le_of_lt (lt_of_not_ge hh))
  have hfc:IntegrableOn (fun t=>‖f t-g t‖) A:=(hf.sub hg).norm.integrableOn
  have hfin:IntegrableOn (fun t=>‖f t‖+‖g t‖) Aᶜ:=(hf.norm.add hg.norm).integrableOn
  have hcoreint:(∫t:ℝ in A,‖f t-g t‖)≤2*T*E:=by
    have hconst:IntegrableOn (fun _:ℝ=>E) A:=continuous_const.integrableOn_Icc
    have hm:=setIntegral_mono_on hfc hconst hA (fun t ht=>hcore t (abs_le.mpr ht))
    have hval:(∫t:ℝ in A,E)=2*T*E:=by
      dsimp only[A]
      rw[integral_Icc_eq_integral_Ioc,←intervalIntegral.integral_of_le (by linarith:-T≤T),intervalIntegral.integral_const]
      simp only[smul_eq_mul]
      ring
    exact hm.trans_eq hval
  have htailint:(∫t:ℝ in Aᶜ,‖f t-g t‖)≤F+G:=by
    have hm:=setIntegral_mono_on (hf.sub hg).norm.integrableOn hfin hA.compl
      (fun t _=>norm_sub_le (f t) (g t))
    rw[integral_add hf.norm.integrableOn hg.norm.integrableOn] at hm
    have hfi:(∫t:ℝ in Aᶜ,‖f t‖)≤∫t:ℝ in B,‖f t‖:=
      setIntegral_mono_set hf.norm.integrableOn (ae_of_all _ (fun t=>norm_nonneg (f t)))
        (ae_of_all _ (fun t ht=>hcomp ht))
    have hgi:(∫t:ℝ in Aᶜ,‖g t‖)≤∫t:ℝ in B,‖g t‖:=
      setIntegral_mono_set hg.norm.integrableOn (ae_of_all _ (fun t=>norm_nonneg (g t)))
        (ae_of_all _ (fun t ht=>hcomp ht))
    exact hm.trans (add_le_add (hfi.trans hft) (hgi.trans hgt))
  have hsplit:(∫t:ℝ in A,‖f t-g t‖)+(∫t:ℝ in Aᶜ,‖f t-g t‖)=∫t:ℝ,‖f t-g t‖:=by
    simpa only[Pi.sub_apply] using integral_add_compl hA (hf.sub hg).norm
  linarith


lemma gaussian_characteristic_norm (t:ℝ):
    ‖Complex.exp (-(t:ℂ)^2/2)‖=Real.exp (-t^2/2):=by
  rw[Complex.norm_exp]
  congr 1
  simp [pow_two]
  <;>ring

lemma gaussian_characteristic_integrable:Integrable (fun t:ℝ=>Complex.exp (-(t:ℂ)^2/2)):=by
  apply (integrable_exp_neg_mul_sq (by norm_num:(0:ℝ)<1/2)).mono'
  · exact (by fun_prop:Continuous (fun t:ℝ=>Complex.exp (-(t:ℂ)^2/2))).aestronglyMeasurable
  · exact ae_of_all _ (fun t=>by rw[gaussian_characteristic_norm];apply le_of_eq;congr 1;ring)

lemma gaussian_characteristic_uniform_tail (T:ℝ)(hT:0≤T):
    (∫t:ℝ in {t:ℝ|T≤|t|},‖Complex.exp (-(t:ℂ)^2/2)‖)≤
      Real.sqrt (8*Real.pi)*Real.exp (-T^2/4):=by
  let E:ℝ:=Real.exp (-T^2/4)
  have hpoint:∀t:ℝ,T≤|t|→Real.exp (-t^2/2)≤E*Real.exp (-(1/4:ℝ)*t^2):=by
    intro t ht
    rw[←Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hs:T^2≤t^2:=by nlinarith[sq_abs t]
    nlinarith
  have hg:Integrable (fun t:ℝ=>E*Real.exp (-(1/4:ℝ)*t^2)):=
    (integrable_exp_neg_mul_sq (by norm_num:(0:ℝ)<1/4)).const_mul E
  have hi:Integrable (fun t:ℝ=>Real.exp (-t^2/2)):=by
    convert (integrable_exp_neg_mul_sq (by norm_num:(0:ℝ)<1/2)) using 1
    funext t
    congr 1
    ring
  have hset:MeasurableSet {t:ℝ|T≤|t|}:=(isClosed_le continuous_const continuous_abs).measurableSet
  have hm:=setIntegral_mono_on hi.integrableOn hg.integrableOn hset (fun t ht=>hpoint t ht)
  have htotal:(∫t:ℝ in {t:ℝ|T≤|t|},E*Real.exp (-(1/4:ℝ)*t^2))≤∫t:ℝ,E*Real.exp (-(1/4:ℝ)*t^2):=
    setIntegral_le_integral hg (ae_of_all _ (fun t=>by dsimp[E];positivity))
  have hbound:(∫t:ℝ,Real.exp (-(1/4:ℝ)*t^2))≤Real.sqrt (8*Real.pi):=by
    have hb:=gaussian_even_moment_factorial_bound (1/4) (by norm_num) 0
    have heq:(2*Real.pi/(1/4):ℝ)=8*Real.pi:=by ring
    simpa only[Nat.mul_zero,pow_zero,Nat.factorial_zero,Nat.cast_one,one_mul,heq] using hb
  have he:(∫t:ℝ in {t:ℝ|T≤|t|},‖Complex.exp (-(t:ℂ)^2/2)‖)=
      ∫t:ℝ in {t:ℝ|T≤|t|},Real.exp (-t^2/2):=by
    congr 1
    funext t
    exact gaussian_characteristic_norm t
  rw[he]
  apply (hm.trans htotal).trans
  rw[integral_const_mul]
  convert mul_le_mul_of_nonneg_left hbound (Real.exp_pos (-T^2/4)).le using 1 <;>ring
end WP.Analysis
