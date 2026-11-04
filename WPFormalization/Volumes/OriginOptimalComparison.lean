import WPFormalization.Volumes.OriginTrueComparison
import WPFormalization.Analysis.OriginSlitWindow
/-! The true marked generating function and its same fixed finite origin
model are exponentially close in the small-density middle regime.
The original L/kappa/J and actual S/Bc are retained. Source inputs are the
proved conclusions of StrongOptimalModel. The lower frequency threshold
places T=tau*h^(1/4) inside the actual rho*sqrt(h*x) analytic disk.
This does not claim the separate tiny-k coefficient normalization or the
final Gaussian/Poisson coefficient identification. -/
noncomputable section
namespace WP.HigherOrder
open Set Filter
open scoped Topology
lemma origin_optimal_comparison_of_source (P:PsiTheory)(p:ℕ)(hp:1≤p)
    (Ω:Set ℂ)(L:ℕ→ℂ→ℂ)(S Bc:ℂ→ℂ)(ρs κ a Cerr H0 κlo:ℝ)
    (hρs:0<ρs)(hρsx:ρs<xCritical)(ha:0<a)(hCerr:0<Cerr)(hH0:0<H0)(hκlo:0<κlo)
    (hS:AnalyticAt ℂ S 0)(hSd:deriv S 0=2)(hBc:AnalyticAt ℂ Bc 0)(hBc0:Bc 0≠0)
    (hSr:∀ᶠt:ℝ in 𝓝 0,0≤t→S (t:ℂ)=(extractionS t:ℂ))
    (hBr:∀ᶠt:ℝ in 𝓝 0,0≤t→Bc (t:ℂ)=(extractionB p t:ℂ))
    (hmap:∀z:ℂ,‖z‖≤ρs→PositiveConvolution.planarInverse P z∈Ω)
    (hmodels:∀g:ℕ,H0≤(complexity g p:ℝ)→
      let h:ℝ:=complexity g p
      let J:=⌊κ*Real.sqrt h⌋₊
      (∀z∈Ω,1/2≤‖finiteMarkedFactor L h J z‖ ∧ ‖finiteMarkedFactor L h J z‖≤2) ∧
      (∀z:ℂ,‖z‖≤ρs→AnalyticAt ℂ (normalizedFiniteMarkedModel P g p S Bc L J) z) ∧
      (∀y∈Icc (0:ℝ) ρs,normalizedFiniteMarkedModel P g p S Bc L J (y:ℂ)≠0 ∧
        ‖normalizedMarkedGenerating P g p (y:ℂ)/normalizedFiniteMarkedModel P g p S Bc L J (y:ℂ)-1‖≤
          Cerr*Real.exp (-a*Real.sqrt h))):
    ∃η τ b C0 H:ℝ,0<η ∧ η<ρs ∧ 0<τ ∧ 0<b ∧ 0<C0 ∧ 0<H ∧ H0≤H ∧
      ∀g:ℕ,H≤(complexity g p:ℝ)→∀x∈Ioo (0:ℝ) η,∀k:ℕ,
      (k:ℝ)=(complexity g p:ℝ)*Psi x→κlo*Real.sqrt (complexity g p:ℝ)≤(k:ℝ)→
      ∀w:ℂ,‖w‖≤τ*Real.sqrt (Real.sqrt (complexity g p:ℝ))→
      let h:ℝ:=complexity g p
      let J:=⌊κ*Real.sqrt h⌋₊
      let σ:ℝ:=Real.sqrt (h*euler Psi x)
      ‖centeredMarkedGenerating P g p k x σ w-centeredOriginFiniteModel P g p J S Bc L x w‖≤
        C0*Real.exp (-b*Real.sqrt h):=by
  obtain ⟨η,ρ,D,E,K,hη,hηs,hρ,hD,hE,hK,hmean,hcomp⟩:=
    origin_actual_centered_complex_comparison_of_source P p hp Ω L S Bc ρs hρs hρsx
      hS hSd hBc hBc0 hSr hBr hmap
  obtain ⟨τ,b,C0,H1,hτ,hb,hC0,hH1,hwindow⟩:=
    Analysis.origin_slit_gevrey_two_window_constants ρ D E Cerr a K κlo hρ hD hE hCerr ha hK hκlo
  let H:ℝ:=max H0 (max H1 1)
  have hH:0<H:=hH0.trans_le (le_max_left _ _)
  refine ⟨η,τ,b,C0,H,hη,hηs,hτ,hb,hC0,hH,le_max_left _ _,?_⟩
  intro g hg x hx k hk hlow w hw
  dsimp only
  let h:ℝ:=complexity g p
  let J:=⌊κ*Real.sqrt h⌋₊
  let r:ℝ:=τ*Real.sqrt (Real.sqrt h)
  have hg0:H0≤h:=(le_max_left _ _).trans hg
  have hg1:H1≤h:=((le_max_left _ _).trans (le_max_right _ _)).trans hg
  have hh1:1≤h:=((le_max_right _ _).trans (le_max_right _ _)).trans hg
  have hn:=hwindow h hg1
  have hm:=hmodels g hg0
  have hs:Stable g p:=by
    have hhN:1≤complexity g p:=by exact_mod_cast (show (1:ℝ)≤(complexity g p:ℝ) from hh1)
    unfold Stable complexity at *
    omega
  have hhigh:(k:ℝ)≤K*h*x:=by
    have ht:=mul_le_mul_of_nonneg_left (hmean x hx) hn.1.le
    nlinarith[hk]
  have h16:16*r<ρ*Real.sqrt (h*x):=hn.2.2.2 x k hx.1 hlow hhigh
  have hr:0<r:=mul_pos hτ (Real.sqrt_pos.mpr (Real.sqrt_pos.mpr hn.1))
  have hw':‖w‖≤3*r/2:=by
    have ht:‖w‖≤r:=hw
    linarith
  have hε:0<Cerr*Real.exp (-a*Real.sqrt h):=by positivity
  have ht:=hcomp g k J hs hn.1 hm.1 hm.2.1 (Cerr*Real.exp (-a*Real.sqrt h)) hε hn.2.1
    hm.2.2 x hx hk r hr h16 w hw'
  exact ht.trans hn.2.2.1
end WP.HigherOrder
