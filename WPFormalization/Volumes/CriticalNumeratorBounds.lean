import WPFormalization.Volumes.UniformCriticalMorseDomain
import WPFormalization.Volumes.CriticalRawCoefficientMatching
/-! The prescribed even numerator coefficients have uniform critical Gevrey-two bounds, derived from the actual same-family Morse amplitudes. -/
noncomputable section
open Set Filter
open scoped Topology
namespace WP.Analysis
lemma CriticalGaussianCoordinateData.original_numerator_uniform_gevrey_two_bound
    (d:CriticalGaussianCoordinateData) (P:PsiTheory) (p:ℕ) (hp:1≤p)
    (Q:ℂ→ℂ) (Ω:Set ℂ) (f:ℕ→ℂ→ℂ) (C B:ℝ)
    (hQ:AnalyticAt ℂ Q 0) (hQ0:Q 0=1)
    (hQphys:∀ᶠδ:ℝ in 𝓝 0,0<δ→Q (δ:ℂ)=(WP.Theta (y₀-δ):ℂ))
    (hΩ:IsOpen Ω) (hcover:∀Y∈Icc (0:ℝ) y₀,(Y:ℂ)∈Ω) (hC:0<C) (hB:0<B)
    (hf:∀j,AnalyticOnNhd ℂ (f j) Ω)
    (hrest:∀j Y,Y∈Icc (0:ℝ) y₀→f j (Y:ℂ)=(HigherOrder.markedCoefficient P p j Y:ℂ))
    (hbound:∀j z,z∈Ω→‖f j z‖≤C*B^j*(j.factorial:ℝ)^2) :
    ∃R Cn Bn:ℝ,0<R ∧ R<y₀ ∧ 0<Cn ∧ 0<Bn ∧
      ∀δ∈Ioo (0:ℝ) R,∀j:ℕ,
        |PowerSeries.coeff j (extractionEvenNumerator P p (XR (y₀-δ)))|≤Cn*Bn^j*(j.factorial:ℝ)^2 := by
  obtain ⟨W,ρ,R0,S,D,Cw,hρ,hR0,hS,hD,hCw,hρR,hρS,hdata⟩:=
    d.uniform_morse_model_domain Q p f Ω C B hQ hQ0 hΩ (hcover _ ⟨y₀_pos.le,le_rfl⟩) hC hB hf hbound
  obtain ⟨Rm,hRm,hRmy,hraw⟩:=d.original_raw_coefficients_eq_critical_model P p hp Q f Ω hΩ
    (hcover _ ⟨y₀_pos.le,le_rfl⟩) hQ hQ0 hQphys hf hrest
  let R:ℝ:=min ρ Rm/2
  let Bn:ℝ:=2*max B (2/R0^2)
  have hR:0<R:=half_pos (lt_min hρ hRm)
  have hRρ:R<ρ:=(half_lt_self (lt_min hρ hRm)).trans_le (min_le_left _ _)
  have hRRm:R<Rm:=(half_lt_self (lt_min hρ hRm)).trans_le (min_le_right _ _)
  have hBn:0<Bn:=mul_pos (by norm_num) (hB.trans_le (le_max_left _ _))
  refine ⟨R,D,Bn,hR,hRRm.trans hRmy,hD,hBn,?_⟩
  intro δ hδ j
  have hn:‖(δ:ℂ)‖<ρ:=by rw[Complex.norm_of_nonneg hδ.1.le];exact hδ.2.trans hRρ
  obtain ⟨hφ,hU,hmap,hphase,ha,hb,htrans,hbnd,hend⟩:=hdata (δ:ℂ) hn
  have hc:=gaussian_model_coefficients_gevrey_two
    (fun s u=>d.modelAmplitude Q p f s ((δ:ℂ),u)) D B R0 hD.le hB.le hR0 hb
    (fun s u hu=>hbnd s u (Metric.sphere_subset_closedBall hu)) j
  rw[←(hraw δ ⟨hδ.1,hδ.2.trans hRRm⟩ j).1] at hc
  simpa only[extractionEvenNumerator,PowerSeries.coeff_mk,Complex.norm_real,Real.norm_eq_abs] using hc
end WP.Analysis
