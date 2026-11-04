import WPFormalization.Analysis.PoissonStirlingLog
import WPFormalization.Analysis.GevreyOneExp
import WPFormalization.Analysis.GevreyOneInverse
/-! Exact Poisson normalization, original Bernoulli formal exponential and inverse,
with uniform Gevrey-one errors for k above a fixed positive multiple of h.
The real extension uses the genuine Gamma expression, not an interpolation
of any genus-indexed generating function. -/
noncomputable section
namespace WP.Analysis
open WP.HigherOrder PowerSeries

def poissonNormalizer (x:ℝ):ℝ:=Real.exp (poissonLogNormalizer x)

lemma poissonNormalizer_gevrey_one:
    GevreyOneAsymptotic poissonNormalizer poissonStirlingSeries:=by
  exact GevreyOneAsymptotic.exp_zero poissonLogNormalizer poissonStirlingLog
    poissonLogNormalizer_gevrey_one poissonStirlingLog_constant

lemma poissonNormalizer_inv_gevrey_one:
    GevreyOneAsymptotic (fun x=>(poissonNormalizer x)⁻¹) (poissonStirlingSeries⁻¹):=by
  exact GevreyOneAsymptotic.inv_unit poissonNormalizer poissonStirlingSeries
    poissonNormalizer_gevrey_one poissonStirlingSeries_constant

lemma poissonNormalizer_nat (k:ℕ)(hk:1≤k):
    poissonNormalizer k=Real.sqrt (2*Real.pi*k)*poissonCenter k:=by
  have hk0:(0:ℝ)<k:=by exact_mod_cast (show 0<k by omega)
  have hg:0<Real.Gamma (k:ℝ):=Real.Gamma_pos_of_pos hk0
  have hfac:(k.factorial:ℝ)=(k:ℝ)*Real.Gamma k:=by
    rw[←Real.Gamma_nat_eq_factorial,Real.Gamma_add_one hk0.ne']
  have hs:0<Real.sqrt (2*Real.pi*k):=Real.sqrt_pos.2 (by positivity)
  have hc:0<poissonCenter k:=by unfold poissonCenter;positivity
  have hlog:Real.log (Real.sqrt (2*Real.pi*k)*poissonCenter k)=poissonLogNormalizer k:=by
    rw[Real.log_mul hs.ne' hc.ne',Real.log_sqrt (by positivity)]
    unfold poissonCenter poissonLogNormalizer
    rw[Real.log_div (by positivity) (by positivity),Real.log_mul (Real.exp_pos _).ne' (pow_pos hk0 _).ne',
      Real.log_exp,Real.log_pow,hfac,Real.log_mul hk0.ne' hg.ne',
      Real.log_mul (by positivity:2*Real.pi≠0) hk0.ne']
    ring
  rw[poissonNormalizer,←hlog,Real.exp_log (mul_pos hs hc)]
end WP.Analysis

namespace WP.Analysis
open WP.HigherOrder
lemma GevreyOneAsymptotic.uniform_above_linear_scale (F:ℝ→ℝ)(f:Series)
    (hF:GevreyOneAsymptotic F f) (a:ℝ)(ha:0<a):
    ∃C B c H:ℝ,0<C ∧ 0<B ∧ 0<c ∧ 0<H ∧ ∀K:ℕ,∀h x:ℝ,
      H≤h→a*h≤x→(K:ℝ)≤c*h→
      |F x-inversePowerTruncation f K x|≤C*B^(K+1)*((K+1).factorial:ℝ)/h^(K+1):=by
  obtain ⟨C,B,c,H,hC,hB,hc,hH,herr⟩:=hF
  refine ⟨C,B/a,c*a,H/a,hC,div_pos hB ha,mul_pos hc ha,div_pos hH ha,?_⟩
  intro K h x hh hax hK
  have hh0:0<h:=(div_pos hH ha).trans_le hh
  have hHx:H≤x:=((div_le_iff₀ ha).mp hh).trans (by simpa only[mul_comm] using hax)
  have hKx:(K:ℝ)≤c*x:=by nlinarith
  apply (herr K x hHx hKx).trans
  calc
    _ ≤ C*B^(K+1)*((K+1).factorial:ℝ)/(a*h)^(K+1):=
      div_le_div_of_nonneg_left (by positivity) (pow_pos (mul_pos ha hh0) _) (pow_le_pow_left₀ (by positivity) hax _)
    _ = _:=by rw[mul_pow,div_pow];field_simp

lemma poissonNormalizer_uniform_error (a:ℝ)(ha:0<a):
    ∃C B c H:ℝ,0<C ∧ 0<B ∧ 0<c ∧ 0<H ∧ ∀k K:ℕ,∀h:ℝ,
      H≤h→a*h≤(k:ℝ)→(K:ℝ)≤c*h→
      |Real.sqrt (2*Real.pi*k)*poissonCenter k-
        ∑j∈Finset.range (K+1),PowerSeries.coeff j poissonStirlingSeries/(k:ℝ)^j|≤
          C*B^(K+1)*((K+1).factorial:ℝ)/h^(K+1):=by
  obtain ⟨C,B,c,H,hC,hB,hc,hH,herr⟩:=GevreyOneAsymptotic.uniform_above_linear_scale
    poissonNormalizer poissonStirlingSeries poissonNormalizer_gevrey_one a ha
  refine ⟨C,B,c,H,hC,hB,hc,hH,?_⟩
  intro k K h hh hax hK
  have hk:1≤k:=by
    have hh0:0<h:=hH.trans_le hh
    have hk0:(0:ℝ)<k:=(mul_pos ha hh0).trans_le hax
    exact_mod_cast (show 0<k by exact_mod_cast hk0)
  simpa only[inversePowerTruncation,poissonNormalizer_nat k hk] using herr K h k hh hax hK

lemma poissonNormalizer_inv_uniform_error (a:ℝ)(ha:0<a):
    ∃C B c H:ℝ,0<C ∧ 0<B ∧ 0<c ∧ 0<H ∧ ∀k K:ℕ,∀h:ℝ,
      H≤h→a*h≤(k:ℝ)→(K:ℝ)≤c*h→
      |(Real.sqrt (2*Real.pi*k)*poissonCenter k)⁻¹-
        ∑j∈Finset.range (K+1),PowerSeries.coeff j (poissonStirlingSeries⁻¹)/(k:ℝ)^j|≤
          C*B^(K+1)*((K+1).factorial:ℝ)/h^(K+1):=by
  obtain ⟨C,B,c,H,hC,hB,hc,hH,herr⟩:=GevreyOneAsymptotic.uniform_above_linear_scale
    (fun x=>(poissonNormalizer x)⁻¹) (poissonStirlingSeries⁻¹) poissonNormalizer_inv_gevrey_one a ha
  refine ⟨C,B,c,H,hC,hB,hc,hH,?_⟩
  intro k K h hh hax hK
  have hk:1≤k:=by
    have hh0:0<h:=hH.trans_le hh
    have hk0:(0:ℝ)<k:=(mul_pos ha hh0).trans_le hax
    exact_mod_cast (show 0<k by exact_mod_cast hk0)
  simpa only[inversePowerTruncation,poissonNormalizer_nat k hk] using herr K h k hh hax hK
end WP.Analysis
