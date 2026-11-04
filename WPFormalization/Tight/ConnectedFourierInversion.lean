import WPFormalization.Tight.ConnectedFourierDomination
import WPFormalization.Analysis.SourceScaledFourier
import WPFormalization.Analysis.GaussianLatticeFourierTransfer
/-! Exact Fourier inversion of the actual tight insertion coefficients. -/
set_option maxHeartbeats 1500000
set_option maxRecDepth 10000
noncomputable section
namespace WP.TightConnected
open Set MeasureTheory TightMoments

def tightMass (P:PsiTheory)(g p:ℕ)(L:Fin p→ℝ)(k:ℕ)(x:ℝ) : ℝ :=
  realCoeff (momentTightG P g p L) k*x^k/(momentTightG P g p L (x:ℂ)).re

def tightPGF (P:PsiTheory)(g p:ℕ)(L:Fin p→ℝ)(x:ℝ)(w:ℂ):ℂ:=
  momentTightG P g p L ((x:ℂ)*w)/momentTightG P g p L (x:ℂ)

lemma tightPGF_analytic_disk (P:PsiTheory)(g p:ℕ)(L:Fin p→ℝ)(x:ℝ)(hx:x∈Ioo (0:ℝ) xCritical):
    AnalyticOnNhd ℂ (tightPGF P g p L x) (Metric.ball 0 (xCritical/x)):=by
  intro w hw
  have hn:‖w‖<xCritical/x:=by simpa only[Metric.mem_ball,dist_zero_right] using hw
  have hz:‖(x:ℂ)*w‖<xCritical:=by
    rw[norm_mul,Complex.norm_of_nonneg hx.1.le]
    exact (mul_comm x ‖w‖ ▸ (lt_div_iff₀ hx.1).mp hn)
  exact ((momentTightG_analyticAt P g p L _ hz).comp
    (by fun_prop:AnalyticAt ℂ (fun w:ℂ=>(x:ℂ)*w) w)).div_const

lemma tightPGF_coeff (P:PsiTheory)(g p:ℕ)(hp:1≤p)(hs:Stable g p)(L:Fin p→ℝ)
    (x:ℝ)(hx:x∈Ioo (0:ℝ) xCritical)(k:ℕ):
    coeff (tightPGF P g p L x) k=(tightMass P g p L k x:ℂ):=by
  let f:=momentTightG P g p L
  have hc:coeff (tightPGF P g p L x) k=(x:ℂ)^k*coeff f k/f (x:ℂ):=by
    unfold tightPGF coeff
    rw[iteratedDeriv_div_const,Analysis.iteratedDeriv_comp_mul_left,mul_zero]
    dsimp[f]
    ring
  have hr:coeff f k=(realCoeff f k:ℂ):=by
    apply Complex.ext
    · rfl
    · simpa only[Complex.ofReal_im] using
        (momentTightG_real_nonnegative_coefficients P g p hp hs L k).2
  have hf:f (x:ℂ)=((momentTightG P g p L (x:ℂ)).re:ℂ):=by
    apply Complex.ext
    · rfl
    · simpa only [Complex.ofReal_im] using
        momentTightG_ofReal_im_zero P g p L x ⟨hx.1.le,hx.2⟩
  rw[hc,hr,hf]
  unfold tightMass
  push_cast
  ring

lemma tightPGF_signedCoeff (P:PsiTheory)(g p:ℕ)(hp:1≤p)(hs:Stable g p)(L:Fin p→ℝ)
    (x:ℝ)(hx:x∈Ioo (0:ℝ) xCritical)(k:ℤ):
    Analysis.signedTaylorCoeff (tightPGF P g p L x) k=
      ((if 0≤k then tightMass P g p L k.toNat x else 0:ℝ):ℂ):=by
  unfold Analysis.signedTaylorCoeff
  split_ifs with hk
  · rw[tightPGF_coeff P g p hp hs L x hx]
  · rfl

def scaledTightFourier (P:PsiTheory)(g p:ℕ)(L:Fin p→ℝ)(x:ℝ)(t:ℝ):ℂ:=
  Analysis.scaledCenteredFourier (tightPGF P g p L x)
    ((complexity g p:ℝ)*Psi x) (Real.sqrt ((complexity g p:ℝ)*euler Psi x)) t

lemma scaledTightFourier_integrable (P:PsiTheory)(g p:ℕ)(L:Fin p→ℝ)(x:ℝ)
    (hx:x∈Ioo (0:ℝ) xCritical):Integrable (scaledTightFourier P g p L x):=by
  apply Analysis.scaledCenteredFourier_integrable
  apply ((tightPGF_analytic_disk P g p L x hx).continuousOn).mono
  intro z hz
  have hn:‖z‖=1:=by simpa only[Metric.mem_sphere,dist_zero_right] using hz
  have hr:1<xCritical/x:=(one_lt_div hx.1).mpr hx.2
  simpa only[Metric.mem_ball,dist_zero_right,hn] using hr

lemma tightMass_scaled_fourier (P:PsiTheory)(g p:ℕ)(hp:1≤p)(hs:Stable g p)(L:Fin p→ℝ)
    (hh:0<complexity g p)(x:ℝ)(hx:x∈Ioo (0:ℝ) xCritical)(k:ℤ):
    let μ:ℝ:=(complexity g p:ℝ)*Psi x
    let σ:=Real.sqrt ((complexity g p:ℝ)*euler Psi x)
    ((σ*(if 0≤k then tightMass P g p L k.toNat x else 0):ℝ):ℂ)=
      ((2*Real.pi:ℝ):ℂ)⁻¹*∫t:ℝ,
        Complex.exp (-((((k:ℝ)-μ)/σ:ℝ):ℂ)*(t:ℂ)*Complex.I)*scaledTightFourier P g p L x t:=by
  dsimp only
  have hv:0<euler Psi x:=mul_pos hx.1 (Analysis.Psi_deriv_pos_interior x ⟨hx.1.le,hx.2⟩)
  have hhr:0<(complexity g p:ℝ):=by exact_mod_cast hh
  have hσ:0<Real.sqrt ((complexity g p:ℝ)*euler Psi x):=Real.sqrt_pos.mpr (mul_pos hhr hv)
  have he:=Analysis.signedTaylorCoeff_scaled_fourier (tightPGF P g p L x) (xCritical/x)
    ((one_lt_div hx.1).mpr hx.2) (tightPGF_analytic_disk P g p L x hx).differentiableOn
    ((complexity g p:ℝ)*Psi x) (Real.sqrt ((complexity g p:ℝ)*euler Psi x)) hσ k
  rw[tightPGF_signedCoeff P g p hp hs L x hx k,←Complex.ofReal_mul] at he
  exact he

lemma tightMass_error_of_characteristic_l1 (P:PsiTheory)(g p:ℕ)(hp:1≤p)(hs:Stable g p)(L:Fin p→ℝ)
    (hh:0<complexity g p)(x:ℝ)(hx:x∈Ioo (0:ℝ) xCritical)(E:ℝ)
    (hE:(∫t:ℝ,‖scaledTightFourier P g p L x t-Complex.exp (-(t:ℂ)^2/2)‖)≤E)
    (k:ℤ):
    let μ:ℝ:=(complexity g p:ℝ)*Psi x
    let σ:=Real.sqrt ((complexity g p:ℝ)*euler Psi x)
    |σ*(if 0≤k then tightMass P g p L k.toNat x else 0)-
      Real.exp (-((k:ℝ)-μ)^2/(2*σ^2))/Real.sqrt (2*Real.pi)|≤E/(2*Real.pi):=by
  dsimp only
  have ht:=Analysis.gaussian_lattice_error_of_fourier_l1
    (scaledTightFourier P g p L x) (scaledTightFourier_integrable P g p L x hx)
    (((k:ℝ)-(complexity g p:ℝ)*Psi x)/Real.sqrt ((complexity g p:ℝ)*euler Psi x))
    (Real.sqrt ((complexity g p:ℝ)*euler Psi x)*(if 0≤k then tightMass P g p L k.toNat x else 0)) E
    (tightMass_scaled_fourier P g p hp hs L hh x hx k) hE
  convert ht using 1
  congr 3
  ring
lemma scaledTightFourier_eq_centered (P:PsiTheory)(g p:ℕ)(L:Fin p→ℝ)(x t:ℝ)
    (ht:|t|≤Real.pi*Real.sqrt ((complexity g p:ℝ)*euler Psi x)) :
    scaledTightFourier P g p L x t =
      centeredTightGenerating P g p L x ((complexity g p:ℝ)*Psi x)
        (Real.sqrt ((complexity g p:ℝ)*euler Psi x)) ((t:ℂ)*Complex.I) := by
  have hmem:t∈Icc (-(Real.pi*Real.sqrt ((complexity g p:ℝ)*euler Psi x)))
      (Real.pi*Real.sqrt ((complexity g p:ℝ)*euler Psi x)):=abs_le.mp ht
  unfold scaledTightFourier Analysis.scaledCenteredFourier centeredTightGenerating tightPGF
  rw[Set.indicator_of_mem hmem,Complex.ofReal_div]
  have he : -(((complexity g p:ℝ)*Psi x:ℝ):ℂ)*
      ((t:ℂ)/(Real.sqrt ((complexity g p:ℝ)*euler Psi x):ℂ))*Complex.I=
      -(((complexity g p:ℝ)*Psi x:ℝ):ℂ)*((t:ℂ)*Complex.I)/
        (Real.sqrt ((complexity g p:ℝ)*euler Psi x):ℂ) := by ring
  have ha : (t:ℂ)/(Real.sqrt ((complexity g p:ℝ)*euler Psi x):ℂ)*Complex.I=
      ((t:ℂ)*Complex.I)/(Real.sqrt ((complexity g p:ℝ)*euler Psi x):ℂ) := by ring
  simp only [he,ha]

end WP.TightConnected
