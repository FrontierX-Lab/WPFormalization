import WPFormalization.Volumes.StrongOptimalModel
import WPFormalization.Analysis.ScaledFourierTail
import WPFormalization.Analysis.GaussianTaylorRemainder
/-! The true finite marked model has a Gaussian standardized-circle tail
near the origin. The actual variance is uniformly at most four times the
cusp weight after one fixed shrink. The genuine full-model-circle bound
then gives a Gaussian point bound, and a proved integral estimate controls
the whole standardized tail for every real center. The amplitude data,
native order budget and base-factor lower bound are precisely the data
already supplied by StrongOptimalModel. No true-generating-function
comparison on a fixed model circle is assumed. -/
noncomputable section
namespace WP.Analysis
open Set Filter MeasureTheory
open scoped Topology
lemma eulerPsi_origin_upper:
    ∃r:ℝ,0<r ∧ r<xCritical ∧ ∀x∈Icc (0:ℝ) r,euler Psi x≤4*x:=by
  have ha:=Psi_analyticAt_interior 0 ⟨le_rfl,xCritical_pos_parameter⟩
  have h0:deriv Psi 0<(4:ℝ):=by rw[Psi_deriv_zero_value];norm_num
  have hnear:∀ᶠx:ℝ in 𝓝 0,deriv Psi x<4:=
    ha.deriv.continuousAt.tendsto.eventually (eventually_lt_nhds h0)
  obtain ⟨R,hR,hball⟩:=Metric.eventually_nhds_iff.mp hnear
  let r:ℝ:=min (R/2) (xCritical/2)
  have hr:0<r:=lt_min (by positivity) (div_pos xCritical_pos_parameter (by norm_num))
  refine ⟨r,hr,(min_le_right _ _).trans_lt (by linarith[xCritical_pos_parameter]),?_⟩
  intro x hx
  have hxb:dist x 0<R:=by
    rw[Real.dist_eq,sub_zero,abs_of_nonneg hx.1]
    have hxr:x≤R/2:=hx.2.trans (min_le_left _ _)
    linarith
  have hd:deriv Psi x≤4:=(hball hxb).le
  change x*deriv Psi x≤4*x
  nlinarith[mul_le_mul_of_nonneg_left hd hx.1]

lemma scaled_circle_gaussian_bound (f:ℂ→ℂ)(A h x v μ:ℝ)
    (hA:0≤A)(hh:0<h)(hx:0<x)(hv:0<v)(hvx:v≤4*x)
    (hcircle:∀θ:ℝ,|θ|≤Real.pi→‖f (Complex.exp ((θ:ℂ)*Complex.I))‖≤
      A*Real.exp (-(h*x/2)*(1-Real.cos θ))):
    ∀t:ℝ,‖scaledCenteredFourier f μ (Real.sqrt (h*v)) t‖≤
      A*Real.exp (-t^2/(4*Real.pi^2)):=by
  intro t
  let σ:ℝ:=Real.sqrt (h*v)
  have hσ:0<σ:=Real.sqrt_pos.mpr (mul_pos hh hv)
  rw[scaledCenteredFourier_norm]
  by_cases ht:t∈Icc (-(Real.pi*σ)) (Real.pi*σ)
  · rw[Set.indicator_of_mem ht]
    let θ:ℝ:=t/σ
    have hθ:|θ|≤Real.pi:=by
      rw[abs_le]
      constructor
      · exact (le_div_iff₀ hσ).mpr (by nlinarith[ht.1])
      · exact (div_le_iff₀ hσ).mpr (by nlinarith[ht.2])
    have hn:=hcircle θ hθ
    apply hn.trans
    apply mul_le_mul_of_nonneg_left _ hA
    apply Real.exp_le_exp.mpr
    have hσsq:σ^2=h*v:=Real.sq_sqrt (mul_pos hh hv).le
    have hθsq:(h*v)*θ^2=t^2:=by
      dsimp[θ]
      rw[div_pow,←hσsq]
      field_simp
    have htx:t^2≤4*h*x*θ^2:=by
      have ht:=mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hvx hh.le) (sq_nonneg θ)
      nlinarith[hθsq]
    have hpi:0<Real.pi^2:=by positivity
    have hdiv:t^2/(4*Real.pi^2)≤h*x/Real.pi^2*θ^2:=by
      apply (div_le_div_of_nonneg_right htx (by positivity:0≤4*Real.pi^2)).trans_eq
      field_simp
      <;>ring
    have hcos:(2/Real.pi^2)*θ^2≤1-Real.cos θ:=by
      linarith[Real.cos_le_one_sub_mul_cos_sq hθ]
    have hphase:h*x/Real.pi^2*θ^2≤h*x/2*(1-Real.cos θ):=by
      have ht:=mul_le_mul_of_nonneg_left hcos (by positivity:0≤h*x/2)
      convert ht using 1 <;>ring
    have ht:=hdiv.trans hphase
    convert (neg_le_neg ht) using 1 <;>ring
  · rw[Set.indicator_of_notMem ht]
    positivity

lemma gaussian_dominated_norm_tail (f:ℝ→ℂ)(A c:ℝ)(hA:0≤A)(hc:0<c)
    (hf:Integrable f)(hbound:∀t:ℝ,‖f t‖≤A*Real.exp (-c*t^2))
    (T:ℝ)(hT:0≤T):
    (∫t:ℝ in {t:ℝ|T≤|t|},‖f t‖)≤
      A*Real.sqrt (4*Real.pi/c)*Real.exp (-(c/2)*T^2):=by
  let E:ℝ:=A*Real.exp (-(c/2)*T^2)
  have hE:0≤E:=by dsimp[E];positivity
  have hg:Integrable (fun t:ℝ=>E*Real.exp (-(c/2)*t^2)):=
    (integrable_exp_neg_mul_sq (by positivity:0<c/2)).const_mul E
  have hp:∀t:ℝ,T≤|t|→‖f t‖≤E*Real.exp (-(c/2)*t^2):=by
    intro t ht
    apply (hbound t).trans
    dsimp only[E]
    rw[mul_assoc,←Real.exp_add]
    apply mul_le_mul_of_nonneg_left _ hA
    apply Real.exp_le_exp.mpr
    have hsq:T^2≤t^2:=by nlinarith[sq_abs t,abs_nonneg t]
    nlinarith
  have hs:MeasurableSet {t:ℝ|T≤|t|}:=(isClosed_le continuous_const continuous_abs).measurableSet
  have hm:=setIntegral_mono_on hf.norm.integrableOn hg.integrableOn hs hp
  have ht:(∫t:ℝ in {t:ℝ|T≤|t|},E*Real.exp (-(c/2)*t^2))≤∫t:ℝ,E*Real.exp (-(c/2)*t^2):=
    setIntegral_le_integral hg (ae_of_all _ (fun t=>by positivity))
  have hb:(∫t:ℝ,Real.exp (-(c/2)*t^2))≤Real.sqrt (4*Real.pi/c):=by
    have hn:=gaussian_even_moment_factorial_bound (c/2) (by positivity) 0
    have he:(2*Real.pi/(c/2):ℝ)=4*Real.pi/c:=by ring
    simpa only[Nat.mul_zero,pow_zero,Nat.factorial_zero,Nat.cast_one,one_mul,he] using hn
  apply (hm.trans ht).trans
  rw[integral_const_mul]
  have he:=mul_le_mul_of_nonneg_left hb hE
  convert he using 1 <;>dsimp[E] <;>ring
end WP.Analysis

namespace WP.HigherOrder
open Set Filter MeasureTheory
open scoped Topology
lemma finiteModelCirclePGF_continuous (P:PsiTheory)(g p J:ℕ)
    (S Bc:ℂ→ℂ)(L:ℕ→ℂ→ℂ)(ρ x:ℝ)(hx:0≤x)(hxr:x<ρ)
    (ha:∀z:ℂ,‖z‖≤ρ→AnalyticAt ℂ (normalizedFiniteMarkedModel P g p S Bc L J) z):
    ContinuousOn (fun z:ℂ=>normalizedFiniteMarkedModel P g p S Bc L J ((x:ℂ)*z)/
      normalizedFiniteMarkedModel P g p S Bc L J (x:ℂ)) (Metric.sphere 0 1):=by
  intro z hz
  have hzn:‖z‖=1:=by simpa only[Metric.mem_sphere,dist_zero_right] using hz
  have hn:‖(x:ℂ)*z‖≤ρ:=by
    rw[norm_mul,Complex.norm_of_nonneg hx,hzn,mul_one]
    exact hxr.le
  have ht:ContinuousAt (fun z:ℂ=>(x:ℂ)*z) z:=by fun_prop
  exact (((ha _ hn).continuousAt.comp ht).div_const _).continuousWithinAt

lemma origin_finite_model_standardized_tail_at (P:PsiTheory)(g p J:ℕ)
    (S Bc:ℂ→ℂ)(L:ℕ→ℂ→ℂ)(B D ρ x μ T:ℝ)
    (hB:0<B)(hD:0<D)(hρx:ρ<xCritical)(hx:x∈Ioo (0:ℝ) ρ)
    (hh:0<(complexity g p:ℝ))(hvx:euler Psi x≤4*x)(hT:0≤T)
    (hbudget:2*B*((J:ℝ)+1)^2≤(complexity g p:ℝ))
    (hAb:∀j z,‖z‖≤ρ→‖originMarkedAmplitude P p j Bc L z‖≤D*B^j*(j.factorial:ℝ)^2)
    (hBc:‖Bc (x:ℂ)-1‖≤1/2)
    (hP:1/2≤‖finiteMarkedFactor L (complexity g p:ℝ) J (PositiveConvolution.planarInverse P (x:ℂ))‖)
    (hphase:∀θ:ℝ,(S ((x:ℂ)*Complex.exp ((θ:ℂ)*Complex.I))-S (x:ℂ)).re≤-(x/2)*(1-Real.cos θ))
    (ha:∀z:ℂ,‖z‖≤ρ→AnalyticAt ℂ (normalizedFiniteMarkedModel P g p S Bc L J) z):
    let f:ℂ→ℂ:=fun z=>normalizedFiniteMarkedModel P g p S Bc L J ((x:ℂ)*z)/
      normalizedFiniteMarkedModel P g p S Bc L J (x:ℂ)
    let σ:ℝ:=Real.sqrt ((complexity g p:ℝ)*euler Psi x)
    (∫t:ℝ in {t:ℝ|T≤|t|},‖Analysis.scaledCenteredFourier f μ σ t‖)≤
      8*D*Real.sqrt (16*Real.pi^3)*Real.exp (-(1/(8*Real.pi^2))*T^2):=by
  dsimp only
  let f:ℂ→ℂ:=fun z=>normalizedFiniteMarkedModel P g p S Bc L J ((x:ℂ)*z)/
    normalizedFiniteMarkedModel P g p S Bc L J (x:ℂ)
  let σ:ℝ:=Real.sqrt ((complexity g p:ℝ)*euler Psi x)
  have hv:0<euler Psi x:=mul_pos hx.1 (Analysis.Psi_deriv_pos_interior x ⟨hx.1.le,hx.2.trans hρx⟩)
  have hc:(0:ℝ)<1/(4*Real.pi^2):=by positivity
  have hcircle:=origin_model_circle_decay_at P g p J S Bc L B D ρ x hB hD hx hh hbudget hAb hBc hP hphase
  have hbound:∀t:ℝ,‖Analysis.scaledCenteredFourier f μ σ t‖≤
      (8*D)*Real.exp (-(1/(4*Real.pi^2))*t^2):=by
    intro t
    have hb:=Analysis.scaled_circle_gaussian_bound f (8*D) (complexity g p:ℝ) x (euler Psi x) μ
      (by positivity) hh hx.1 hv hvx (fun θ hθ=>hcircle.2 θ) t
    convert hb using 1
    congr 2
    ring
  have hf:Integrable (Analysis.scaledCenteredFourier f μ σ):=
    Analysis.scaledCenteredFourier_integrable f (finiteModelCirclePGF_continuous P g p J S Bc L ρ x hx.1.le hx.2 ha) μ σ
  have ht:=Analysis.gaussian_dominated_norm_tail (Analysis.scaledCenteredFourier f μ σ)
    (8*D) (1/(4*Real.pi^2)) (by positivity) hc hf hbound T hT
  have hconst:(4*Real.pi/(1/(4*Real.pi^2)):ℝ)=16*Real.pi^3:=by
    field_simp
    <;>ring
  have hcoef:((1/(4*Real.pi^2))/2:ℝ)=1/(8*Real.pi^2):=by ring
  rw[hconst,hcoef] at ht
  exact ht
end WP.HigherOrder
