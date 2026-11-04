import WPFormalization.Analysis.PoissonNormalizer
noncomputable section
namespace WP.Analysis
lemma poisson_gaussian_normalization_identity (a Bc:ℂ)(h ν v:ℝ)(k:ℕ)
    (hh:0<h)(hν:0<ν)(hv:0<v)(hk:h*ν=(k:ℝ))(hBc:Bc≠0):
    a*(Real.sqrt (2*Real.pi*h*v):ℂ)/Bc=
      (a/((WP.poissonCenter k:ℂ)*(Bc*(Real.sqrt (ν/v):ℂ))))*(poissonNormalizer k:ℂ):=by
  have hk0:0<(k:ℝ):=by rw[←hk];positivity
  have hk1:1≤k:=by exact_mod_cast (show 0<(k:ℝ) from hk0)
  have hkpos:0<(k:ℝ):=by rw[←hk];positivity
  have hpc:0<WP.poissonCenter k:=by unfold WP.poissonCenter;positivity
  have hpc0:(WP.poissonCenter k:ℂ)≠0:=by exact_mod_cast hpc.ne'
  have hs:0<Real.sqrt (ν/v):=by positivity
  have hs0:(Real.sqrt (ν/v):ℂ)≠0:=by exact_mod_cast hs.ne'
  have hroot:Real.sqrt (2*Real.pi*h*v)*Real.sqrt (ν/v)=Real.sqrt (2*Real.pi*k):=by
    rw[←Real.sqrt_mul (by positivity:0≤2*Real.pi*h*v)]
    congr 1
    rw[←hk]
    field_simp
    <;>ring
  have hrC:(Real.sqrt (2*Real.pi*h*v):ℂ)*(Real.sqrt (ν/v):ℂ)=
      (Real.sqrt (2*Real.pi*k):ℂ):=by exact_mod_cast hroot
  rw[poissonNormalizer_nat k hk1,Complex.ofReal_mul,←hrC]
  field_simp
  <;>ring
end WP.Analysis

namespace WP.Analysis
lemma poisson_gaussian_coefficient_normalization (S:ℂ→ℂ)(F:ℂ→ℂ)(x h ν v:ℝ)(k:ℕ)
    (Bc op E0:ℂ)(hh:0<h)(hx:0<x)(hν:0<ν)(hv:0<v)(hk:h*ν=(k:ℝ))(hBc:Bc≠0)
    (hE0:E0=Bc*(Real.sqrt (ν/v):ℂ))
    (hcoeff:WP.coeff F k=Complex.exp ((h:ℂ)*S (x:ℂ))*(x:ℂ)⁻¹^k*(WP.poissonCenter k:ℂ)*op):
    Complex.exp (-((h:ℂ)*S (x:ℂ)))*(x:ℂ)^k*WP.coeff F k*
      (Real.sqrt (2*Real.pi*h*v):ℂ)/Bc=(op/E0)*(poissonNormalizer k:ℂ):=by
  have hx0:(x:ℂ)≠0:=by exact_mod_cast hx.ne'
  have hkpos:0<(k:ℝ):=by rw[←hk];positivity
  have hpc:0<WP.poissonCenter k:=by unfold WP.poissonCenter;positivity
  have hpc0:(WP.poissonCenter k:ℂ)≠0:=by exact_mod_cast hpc.ne'
  have hs:0<Real.sqrt (ν/v):=by positivity
  have hs0:(Real.sqrt (ν/v):ℂ)≠0:=by exact_mod_cast hs.ne'
  have ha:Complex.exp (-((h:ℂ)*S (x:ℂ)))*(x:ℂ)^k*WP.coeff F k=(WP.poissonCenter k:ℂ)*op:=by
    rw[hcoeff]
    calc _=(Complex.exp (-((h:ℂ)*S (x:ℂ)))*Complex.exp ((h:ℂ)*S (x:ℂ)))*
        ((x:ℂ)^k*((x:ℂ)⁻¹)^k)*((WP.poissonCenter k:ℂ)*op):=by ring
         _= _:=by rw[←Complex.exp_add,neg_add_cancel,Complex.exp_zero,←mul_pow,mul_inv_cancel₀ hx0,one_pow];ring
  rw[ha,poisson_gaussian_normalization_identity ((WP.poissonCenter k:ℂ)*op) Bc h ν v k hh hν hv hk hBc,hE0]
  field_simp
end WP.Analysis
