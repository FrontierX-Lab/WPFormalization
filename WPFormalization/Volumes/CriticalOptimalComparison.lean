import WPFormalization.Volumes.CriticalTrueComparison
import WPFormalization.Analysis.SlitGevreyWindow
/-! Exponentially accurate actual critical central comparison.
The given canonical family and optimal order choice are retained exactly.
The upstream same-choice source supplies its native order budget, finite
factor lower bound and actual whole-physical-interval real error. The local
proof derives the true complex comparison on T=tau*h^(1/4), so T^2 is of
order sqrt(h). This comparison does not by itself identify the Gaussian
coefficient recipe or prove the final extraction theorem. -/
noncomputable section
namespace WP.Analysis
open Set Filter
open scoped Topology
lemma CriticalGaussianCoordinateData.critical_optimal_comparison_of_parameter_data
    (d:CriticalGaussianCoordinateData)(P:PsiTheory)(p:ℕ)(hp:1≤p)
    (Ω:Set ℂ)(L:ℕ→ℂ→ℂ)(C B κ a H0:ℝ)
    (hΩ:IsOpen Ω)(hcover:∀Y∈Icc (0:ℝ) y₀,(Y:ℂ)∈Ω)
    (hC:0<C)(hB:0<B)(ha:0<a)(hH0:0<H0)
    (hLa:∀j,AnalyticOnNhd ℂ (L j) Ω)
    (hLr:∀j Y,Y∈Icc (0:ℝ) y₀→L j (Y:ℂ)=(HigherOrder.markedCoefficient P p j Y:ℂ))
    (hLb:∀j z,z∈Ω→‖L j z‖≤C*B^j*(j.factorial:ℝ)^2)
    (hmodels:∀g:ℕ,H0≤(complexity g p:ℝ)→
      let h:ℝ:=complexity g p
      let J:=⌊κ*Real.sqrt h⌋₊
      2*B*((J:ℝ)+1)^2≤h ∧
      (∀Y∈Icc (0:ℝ) y₀,1/2≤‖HigherOrder.finiteMarkedFactor L h J (Y:ℂ)‖) ∧
      (∀Y∈Ico (0:ℝ) y₀,|(Real.pi*markedF P g p (XR Y)/markedModel g p Y)/
        HigherOrder.realFiniteMarkedFactor P p h J Y-1|≤2*C*Real.exp (-a*Real.sqrt h))):
    ∃(Q:ℂ→ℂ)(R τ b C0 H:ℝ),AnalyticAt ℂ Q 0 ∧ Q 0=1 ∧
      (∀ᶠδ:ℝ in 𝓝 0,0<δ→Q (δ:ℂ)=(WP.Theta (y₀-δ):ℂ)) ∧
      0<R ∧ R<y₀ ∧ 0<τ ∧ 0<b ∧ 0<C0 ∧ 0<H ∧ H0≤H ∧
      ∀g:ℕ,H≤(complexity g p:ℝ)→∀δ∈Ioo (0:ℝ) R,
      ∀k:ℕ,(k:ℝ)=(complexity g p:ℝ)*Psi (XR (y₀-δ))→
      ∀w:ℂ,‖w‖≤τ*Real.sqrt (Real.sqrt (complexity g p:ℝ))→
      let h:ℝ:=complexity g p
      let J:=⌊κ*Real.sqrt h⌋₊
      let x:ℝ:=XR (y₀-δ)
      let σ:ℝ:=Real.sqrt (h*euler Psi x)
      ‖centeredMarkedGenerating P g p k x σ w-
        d.centeredFiniteMarkedModel Q p L h J (δ:ℂ) w‖≤C0*Real.exp (-b*Real.sqrt h):=by
  obtain ⟨Q,R,D,E,hQa,hQ0,hQphys,hR,hRy,hD,hE,hcomp⟩:=
    d.actual_centered_complex_comparison P p hp Ω L C B hΩ hcover hC hB hLa hLr hLb
  obtain ⟨τ,b,C0,H1,hτ,hb,hC0,hH1,hwindow⟩:=
    slit_gevrey_two_window_constants R D E C a hR hD hE hC ha
  let H:ℝ:=max H0 (max H1 1)
  have hH:0<H:=hH0.trans_le (le_max_left _ _)
  refine ⟨Q,R,τ,b,C0,H,hQa,hQ0,hQphys,hR,hRy,hτ,hb,hC0,hH,le_max_left _ _,?_⟩
  intro g hg δ hδ k hk w hw
  dsimp only
  let h:ℝ:=complexity g p
  let J:=⌊κ*Real.sqrt h⌋₊
  let r:ℝ:=τ*Real.sqrt (Real.sqrt h)
  have hg0:H0≤h:=(le_max_left _ _).trans hg
  have hg1:H1≤h:=((le_max_left _ _).trans (le_max_right _ _)).trans hg
  have hh1:1≤h:=((le_max_right _ _).trans (le_max_right _ _)).trans hg
  have hs:Stable g p:=by
    have hn:1≤complexity g p:=by exact_mod_cast (show (1:ℝ)≤(complexity g p:ℝ) from hh1)
    unfold Stable complexity at *
    omega
  have hm:=hmodels g hg0
  have hn:=hwindow h hg1
  have hε:0<2*C*Real.exp (-a*Real.sqrt h):=by positivity
  have hr:0<r:=mul_pos hτ (Real.sqrt_pos.mpr (Real.sqrt_pos.mpr hn.1))
  have hw':‖w‖≤3*r/2:=by change ‖w‖≤_ at hw;linarith
  have ht:=hcomp δ hδ g k J hs hn.1 hk hm.1 hm.2.1
    (2*C*Real.exp (-a*Real.sqrt h)) hε hn.2.1 hm.2.2 r hr hn.2.2.1 w hw'
  exact ht.trans hn.2.2.2
end WP.Analysis
