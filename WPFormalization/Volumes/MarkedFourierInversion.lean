import WPFormalization.Analysis.SignedCoefficientFourier
import WPFormalization.Analysis.GaussianLatticeFourierTransfer
import WPFormalization.Volumes.MarkedGeneratingPositivity
import WPFormalization.Analysis.CoefficientScaling
/-! The genuine marked probability generating function, its integer-index
Fourier inversion, and the exact transfer from a characteristic L1 error
to the Gaussian lattice error. The L1 estimate remains a separate proof
obligation; no quantitative local limit is claimed by these identities. -/
noncomputable section
namespace WP
open Set MeasureTheory

def markedPGF (P:PsiTheory)(g p:ℕ)(x:ℝ)(w:ℂ):ℂ:=
  iteratedDeriv p (Phi P g) ((x:ℂ)*w)/iteratedDeriv p (Phi P g) (x:ℂ)

lemma markedPGF_analytic_disk (P:PsiTheory)(g p:ℕ)(x:ℝ)(hx:x∈Ioo (0:ℝ) xCritical):
    AnalyticOnNhd ℂ (markedPGF P g p x) (Metric.ball 0 (xCritical/x)):=by
  intro w hw
  have hn:‖w‖<xCritical/x:=by simpa only[Metric.mem_ball,dist_zero_right] using hw
  have hz:‖(x:ℂ)*w‖<xCritical:=by
    rw[norm_mul,Complex.norm_of_nonneg hx.1.le]
    exact (mul_comm x ‖w‖ ▸ (lt_div_iff₀ hx.1).mp hn)
  exact ((marked_generating_analytic_disk P g p _ (by simpa only[Metric.mem_ball,dist_zero_right] using hz)).comp
    (by fun_prop:AnalyticAt ℂ (fun w:ℂ=>(x:ℂ)*w) w)).div_const

lemma markedPGF_coeff (P:PsiTheory)(g p:ℕ)(hp:1≤p)(hs:Stable g p)
    (x:ℝ)(hx:x∈Ioo (0:ℝ) xCritical)(k:ℕ):
    coeff (markedPGF P g p x) k=(cuspMass P g p k x:ℂ):=by
  let f:=iteratedDeriv p (Phi P g)
  have hc:coeff (markedPGF P g p x) k=(x:ℂ)^k*coeff f k/f (x:ℂ):=by
    unfold markedPGF coeff
    rw[iteratedDeriv_div_const,Analysis.iteratedDeriv_comp_mul_left,mul_zero]
    dsimp[f]
    ring
  have hr:coeff f k=(realCoeff f k:ℂ):=by
    apply Complex.ext
    · rfl
    · simpa only[Complex.ofReal_im] using
        (marked_generating_nonnegative_coefficients P g p hp hs k).2
  have hf:f (x:ℂ)=(markedF P g p x:ℂ):=by
    have he:=PositiveConvolution.Phi_iteratedDeriv_ofReal P g p hs x ⟨hx.1.le,hx.2⟩
    apply Complex.ext
    · rfl
    · simpa only[Complex.ofReal_im] using congrArg Complex.im he
  rw[hc,hr,hf]
  unfold cuspMass
  push_cast
  ring

lemma markedPGF_signedCoeff (P:PsiTheory)(g p:ℕ)(hp:1≤p)(hs:Stable g p)
    (x:ℝ)(hx:x∈Ioo (0:ℝ) xCritical)(k:ℤ):
    Analysis.signedTaylorCoeff (markedPGF P g p x) k=
      ((if 0≤k then cuspMass P g p k.toNat x else 0:ℝ):ℂ):=by
  unfold Analysis.signedTaylorCoeff
  split_ifs with hk
  · rw[markedPGF_coeff P g p hp hs x hx]
  · rfl

def scaledMarkedFourier (P:PsiTheory)(g p:ℕ)(x:ℝ)(t:ℝ):ℂ:=
  Analysis.scaledCenteredFourier (markedPGF P g p x)
    ((complexity g p:ℝ)*Psi x) (Real.sqrt ((complexity g p:ℝ)*euler Psi x)) t

lemma scaledMarkedFourier_integrable (P:PsiTheory)(g p:ℕ)(x:ℝ)
    (hx:x∈Ioo (0:ℝ) xCritical):Integrable (scaledMarkedFourier P g p x):=by
  apply Analysis.scaledCenteredFourier_integrable
  apply ((markedPGF_analytic_disk P g p x hx).continuousOn).mono
  intro z hz
  have hn:‖z‖=1:=by simpa only[Metric.mem_sphere,dist_zero_right] using hz
  have hr:1<xCritical/x:=(one_lt_div hx.1).mpr hx.2
  simpa only[Metric.mem_ball,dist_zero_right,hn] using hr

lemma cuspMass_scaled_fourier (P:PsiTheory)(g p:ℕ)(hp:1≤p)(hs:Stable g p)
    (hh:0<complexity g p)(x:ℝ)(hx:x∈Ioo (0:ℝ) xCritical)(k:ℤ):
    let μ:ℝ:=(complexity g p:ℝ)*Psi x
    let σ:=Real.sqrt ((complexity g p:ℝ)*euler Psi x)
    ((σ*(if 0≤k then cuspMass P g p k.toNat x else 0):ℝ):ℂ)=
      ((2*Real.pi:ℝ):ℂ)⁻¹*∫t:ℝ,
        Complex.exp (-((((k:ℝ)-μ)/σ:ℝ):ℂ)*(t:ℂ)*Complex.I)*scaledMarkedFourier P g p x t:=by
  dsimp only
  have hv:0<euler Psi x:=mul_pos hx.1 (Analysis.Psi_deriv_pos_interior x ⟨hx.1.le,hx.2⟩)
  have hhr:0<(complexity g p:ℝ):=by exact_mod_cast hh
  have hσ:0<Real.sqrt ((complexity g p:ℝ)*euler Psi x):=Real.sqrt_pos.mpr (mul_pos hhr hv)
  have he:=Analysis.signedTaylorCoeff_scaled_fourier (markedPGF P g p x) (xCritical/x)
    ((one_lt_div hx.1).mpr hx.2) (markedPGF_analytic_disk P g p x hx).differentiableOn
    ((complexity g p:ℝ)*Psi x) (Real.sqrt ((complexity g p:ℝ)*euler Psi x)) hσ k
  rw[markedPGF_signedCoeff P g p hp hs x hx k,←Complex.ofReal_mul] at he
  exact he

lemma cuspMass_error_of_characteristic_l1 (P:PsiTheory)(g p:ℕ)(hp:1≤p)(hs:Stable g p)
    (hh:0<complexity g p)(x:ℝ)(hx:x∈Ioo (0:ℝ) xCritical)(E:ℝ)
    (hE:(∫t:ℝ,‖scaledMarkedFourier P g p x t-Complex.exp (-(t:ℂ)^2/2)‖)≤E)
    (k:ℤ):
    let μ:ℝ:=(complexity g p:ℝ)*Psi x
    let σ:=Real.sqrt ((complexity g p:ℝ)*euler Psi x)
    |σ*(if 0≤k then cuspMass P g p k.toNat x else 0)-
      Real.exp (-((k:ℝ)-μ)^2/(2*σ^2))/Real.sqrt (2*Real.pi)|≤E/(2*Real.pi):=by
  dsimp only
  have ht:=Analysis.gaussian_lattice_error_of_fourier_l1
    (scaledMarkedFourier P g p x) (scaledMarkedFourier_integrable P g p x hx)
    (((k:ℝ)-(complexity g p:ℝ)*Psi x)/Real.sqrt ((complexity g p:ℝ)*euler Psi x))
    (Real.sqrt ((complexity g p:ℝ)*euler Psi x)*(if 0≤k then cuspMass P g p k.toNat x else 0)) E
    (cuspMass_scaled_fourier P g p hp hs hh x hx k) hE
  convert ht using 1
  congr 3
  ring
end WP
