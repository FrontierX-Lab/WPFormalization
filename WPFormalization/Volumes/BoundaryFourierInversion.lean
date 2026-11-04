import WPFormalization.Volumes.BoundaryCenteredGenerating
import WPFormalization.Volumes.BoundaryCoefficientIdentification
import WPFormalization.Analysis.SourceScaledFourier
import WPFormalization.Analysis.GaussianLatticeFourierTransfer
/-! Exact Fourier inversion of the genuine boundary insertion coefficients. -/
noncomputable section
namespace WP.BoundaryConvolution
open Set MeasureTheory

def boundaryMass (P:PsiTheory)(g p:ℕ)(L:Fin p→ℝ)(k:ℕ)(x:ℝ) : ℝ :=
  realCoeff (boundaryG P g p L) k*x^k/(boundaryG P g p L (x:ℂ)).re

def boundaryPGF (P:PsiTheory)(g p:ℕ)(L:Fin p→ℝ)(x:ℝ)(w:ℂ):ℂ:=
  boundaryG P g p L ((x:ℂ)*w)/boundaryG P g p L (x:ℂ)

lemma boundaryPGF_analytic_disk (P:PsiTheory)(g p:ℕ)(L:Fin p→ℝ)(x:ℝ)(hx:x∈Ioo (0:ℝ) xCritical):
    AnalyticOnNhd ℂ (boundaryPGF P g p L x) (Metric.ball 0 (xCritical/x)):=by
  intro w hw
  have hn:‖w‖<xCritical/x:=by simpa only[Metric.mem_ball,dist_zero_right] using hw
  have hz:‖(x:ℂ)*w‖<xCritical:=by
    rw[norm_mul,Complex.norm_of_nonneg hx.1.le]
    exact (mul_comm x ‖w‖ ▸ (lt_div_iff₀ hx.1).mp hn)
  exact ((boundaryG_analyticAt P g p L _ hz).comp
    (by fun_prop:AnalyticAt ℂ (fun w:ℂ=>(x:ℂ)*w) w)).div_const

lemma boundaryPGF_coeff (P:PsiTheory)(g p:ℕ)(hp:1≤p)(hs:Stable g p)(L:Fin p→ℝ)
    (x:ℝ)(hx:x∈Ioo (0:ℝ) xCritical)(k:ℕ):
    coeff (boundaryPGF P g p L x) k=(boundaryMass P g p L k x:ℂ):=by
  let f:=boundaryG P g p L
  have hc:coeff (boundaryPGF P g p L x) k=(x:ℂ)^k*coeff f k/f (x:ℂ):=by
    unfold boundaryPGF coeff
    rw[iteratedDeriv_div_const,Analysis.iteratedDeriv_comp_mul_left,mul_zero]
    dsimp[f]
    ring
  have hr:coeff f k=(realCoeff f k:ℂ):=by
    apply Complex.ext
    · rfl
    · simpa only[Complex.ofReal_im] using
        (boundaryG_real_nonnegative_coefficients P g p L k).2
  have hf:f (x:ℂ)=((boundaryG P g p L (x:ℂ)).re:ℂ):=by
    apply Complex.ext
    · rfl
    · simpa only [Complex.ofReal_im] using
        boundaryG_ofReal_im_zero P g p L x ⟨hx.1.le,hx.2⟩
  rw[hc,hr,hf]
  unfold boundaryMass
  push_cast
  ring

lemma boundaryPGF_signedCoeff (P:PsiTheory)(g p:ℕ)(hp:1≤p)(hs:Stable g p)(L:Fin p→ℝ)
    (x:ℝ)(hx:x∈Ioo (0:ℝ) xCritical)(k:ℤ):
    Analysis.signedTaylorCoeff (boundaryPGF P g p L x) k=
      ((if 0≤k then boundaryMass P g p L k.toNat x else 0:ℝ):ℂ):=by
  unfold Analysis.signedTaylorCoeff
  split_ifs with hk
  · rw[boundaryPGF_coeff P g p hp hs L x hx]
  · rfl

def scaledBoundaryFourier (P:PsiTheory)(g p:ℕ)(L:Fin p→ℝ)(x:ℝ)(t:ℝ):ℂ:=
  Analysis.scaledCenteredFourier (boundaryPGF P g p L x)
    ((complexity g p:ℝ)*Psi x) (Real.sqrt ((complexity g p:ℝ)*euler Psi x)) t

lemma scaledBoundaryFourier_integrable (P:PsiTheory)(g p:ℕ)(L:Fin p→ℝ)(x:ℝ)
    (hx:x∈Ioo (0:ℝ) xCritical):Integrable (scaledBoundaryFourier P g p L x):=by
  apply Analysis.scaledCenteredFourier_integrable
  apply ((boundaryPGF_analytic_disk P g p L x hx).continuousOn).mono
  intro z hz
  have hn:‖z‖=1:=by simpa only[Metric.mem_sphere,dist_zero_right] using hz
  have hr:1<xCritical/x:=(one_lt_div hx.1).mpr hx.2
  simpa only[Metric.mem_ball,dist_zero_right,hn] using hr

lemma boundaryMass_scaled_fourier (P:PsiTheory)(g p:ℕ)(hp:1≤p)(hs:Stable g p)(L:Fin p→ℝ)
    (hh:0<complexity g p)(x:ℝ)(hx:x∈Ioo (0:ℝ) xCritical)(k:ℤ):
    let μ:ℝ:=(complexity g p:ℝ)*Psi x
    let σ:=Real.sqrt ((complexity g p:ℝ)*euler Psi x)
    ((σ*(if 0≤k then boundaryMass P g p L k.toNat x else 0):ℝ):ℂ)=
      ((2*Real.pi:ℝ):ℂ)⁻¹*∫t:ℝ,
        Complex.exp (-((((k:ℝ)-μ)/σ:ℝ):ℂ)*(t:ℂ)*Complex.I)*scaledBoundaryFourier P g p L x t:=by
  dsimp only
  have hv:0<euler Psi x:=mul_pos hx.1 (Analysis.Psi_deriv_pos_interior x ⟨hx.1.le,hx.2⟩)
  have hhr:0<(complexity g p:ℝ):=by exact_mod_cast hh
  have hσ:0<Real.sqrt ((complexity g p:ℝ)*euler Psi x):=Real.sqrt_pos.mpr (mul_pos hhr hv)
  have he:=Analysis.signedTaylorCoeff_scaled_fourier (boundaryPGF P g p L x) (xCritical/x)
    ((one_lt_div hx.1).mpr hx.2) (boundaryPGF_analytic_disk P g p L x hx).differentiableOn
    ((complexity g p:ℝ)*Psi x) (Real.sqrt ((complexity g p:ℝ)*euler Psi x)) hσ k
  rw[boundaryPGF_signedCoeff P g p hp hs L x hx k,←Complex.ofReal_mul] at he
  exact he

lemma boundaryMass_error_of_characteristic_l1 (P:PsiTheory)(g p:ℕ)(hp:1≤p)(hs:Stable g p)(L:Fin p→ℝ)
    (hh:0<complexity g p)(x:ℝ)(hx:x∈Ioo (0:ℝ) xCritical)(E:ℝ)
    (hE:(∫t:ℝ,‖scaledBoundaryFourier P g p L x t-Complex.exp (-(t:ℂ)^2/2)‖)≤E)
    (k:ℤ):
    let μ:ℝ:=(complexity g p:ℝ)*Psi x
    let σ:=Real.sqrt ((complexity g p:ℝ)*euler Psi x)
    |σ*(if 0≤k then boundaryMass P g p L k.toNat x else 0)-
      Real.exp (-((k:ℝ)-μ)^2/(2*σ^2))/Real.sqrt (2*Real.pi)|≤E/(2*Real.pi):=by
  dsimp only
  have ht:=Analysis.gaussian_lattice_error_of_fourier_l1
    (scaledBoundaryFourier P g p L x) (scaledBoundaryFourier_integrable P g p L x hx)
    (((k:ℝ)-(complexity g p:ℝ)*Psi x)/Real.sqrt ((complexity g p:ℝ)*euler Psi x))
    (Real.sqrt ((complexity g p:ℝ)*euler Psi x)*(if 0≤k then boundaryMass P g p L k.toNat x else 0)) E
    (boundaryMass_scaled_fourier P g p hp hs L hh x hx k) hE
  convert ht using 1
  congr 3
  ring
lemma scaledBoundaryFourier_eq_centered (P:PsiTheory)(g p:ℕ)(L:Fin p→ℝ)(x t:ℝ)
    (ht:|t|≤Real.pi*Real.sqrt ((complexity g p:ℝ)*euler Psi x)) :
    scaledBoundaryFourier P g p L x t =
      centeredBoundaryGenerating P g p L x ((complexity g p:ℝ)*Psi x)
        (Real.sqrt ((complexity g p:ℝ)*euler Psi x)) ((t:ℂ)*Complex.I) := by
  have hmem:t∈Icc (-(Real.pi*Real.sqrt ((complexity g p:ℝ)*euler Psi x)))
      (Real.pi*Real.sqrt ((complexity g p:ℝ)*euler Psi x)):=abs_le.mp ht
  unfold scaledBoundaryFourier Analysis.scaledCenteredFourier centeredBoundaryGenerating boundaryPGF
  rw[Set.indicator_of_mem hmem,Complex.ofReal_div]
  congr 2 <;>ring

end WP.BoundaryConvolution
