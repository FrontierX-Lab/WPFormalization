import WPFormalization.Volumes.CompactTrueComparison
import WPFormalization.Analysis.SlitGevreyWindow
import WPFormalization.Volumes.StrongOptimalModel
/-! Same-family actual compact central comparison on the quarter-power
window. Both the parameter-data client and the P-only producer retain the
canonical family, B, kappa and J; all source hypotheses are instantiated
from proved results. This is one extraction-support branch, not the full
canonical expansion theorem. -/
noncomputable section
namespace WP.Analysis
open Set Filter
open scoped Topology
lemma compact_optimal_comparison_of_parameter_data (P:PsiTheory)(p:ℕ)(hp:1≤p)
    (a b:ℝ)(ha:0<a)(hab:a≤b)(hbc:b<xCritical)
    (Ωf:Set ℂ)(f:ℕ→ℂ→ℂ)(C B κ rate H0:ℝ)
    (hΩf:IsOpen Ωf)(hcover:∀Y∈Icc (0:ℝ) y₀,(Y:ℂ)∈Ωf)
    (hC:0<C)(hB:0<B)(hrate:0<rate)(hH0:0<H0)
    (hFa:∀j,AnalyticOnNhd ℂ (f j) Ωf)
    (hfr:∀j Y,Y∈Icc (0:ℝ) y₀→f j (Y:ℂ)=(HigherOrder.markedCoefficient P p j Y:ℂ))
    (hfb:∀j z,z∈Ωf→‖f j z‖≤C*B^j*(j.factorial:ℝ)^2)
    (hmodels:∀g:ℕ,H0≤(complexity g p:ℝ)→
      let h:ℝ:=complexity g p
      let J:=⌊κ*Real.sqrt h⌋₊
      2*B*((J:ℝ)+1)^2≤h ∧
      (∀Y∈Icc (0:ℝ) y₀,1/2≤‖HigherOrder.finiteMarkedFactor f h J (Y:ℂ)‖) ∧
      (∀Y∈Ico (0:ℝ) y₀,|(Real.pi*markedF P g p (XR Y)/markedModel g p Y)/
        HigherOrder.realFiniteMarkedFactor P p h J Y-1|≤2*C*Real.exp (-rate*Real.sqrt h))):
    ∃(S l Bc:ℂ→ℂ)(τ decay C0 H:ℝ),0<τ ∧ 0<decay ∧ 0<C0 ∧ 0<H ∧ H0≤H ∧
      (∀x∈Icc a b,AnalyticAt ℂ S (x:ℂ) ∧ AnalyticAt ℂ l (x:ℂ) ∧
        (∀ᶠt:ℝ in 𝓝 x,S (t:ℂ)=(extractionS t:ℂ)) ∧
        complexEuler S (x:ℂ)=(WP.Psi x:ℂ) ∧
        ((complexEuler^[2]) S) (x:ℂ)=(WP.euler WP.Psi x:ℂ) ∧
        l (x:ℂ)=((Real.sqrt (WP.euler WP.Psi x))⁻¹:ℝ) ∧
        ∀ᶠq:ℂ in 𝓝 (x:ℂ),(l q)^2*((complexEuler^[2]) S) q=1) ∧
      (∀x∈Ico (0:ℝ) xCritical,AnalyticAt ℂ Bc (x:ℂ) ∧ Bc (x:ℂ)=(extractionB p x:ℂ)) ∧
      ∀g:ℕ,H≤(complexity g p:ℝ)→∀x∈Icc a b,∀k:ℕ,
      (k:ℝ)=(complexity g p:ℝ)*Psi x→
      ∀w:ℂ,‖w‖≤τ*Real.sqrt (Real.sqrt (complexity g p:ℝ))→
      let h:ℝ:=complexity g p
      let J:=⌊κ*Real.sqrt h⌋₊
      let σ:ℝ:=Real.sqrt (h*euler Psi x)
      ‖centeredMarkedGenerating P g p k x σ w-compactCenteredFiniteModel P Bc S l f h J (x:ℂ) w‖≤
        C0*Real.exp (-decay*Real.sqrt h):=by
  obtain ⟨S,l,Bc,R,D,hR,hD,hData,hBc,hcomp⟩:=
    actual_compact_centered_comparison_of_fixed_coefficients P p hp a b ha hab hbc Ωf f C B
      hΩf hcover hC hB hFa hfr hfb
  obtain ⟨τ,decay,C0,H1,hτ,hdec,hC0,hH1,hwindow⟩:=
    slit_gevrey_two_window_constants R D 1 C rate hR hD (by norm_num) hC hrate
  let H:ℝ:=max H0 (max H1 1)
  have hH:0<H:=hH0.trans_le (le_max_left _ _)
  refine ⟨S,l,Bc,τ,decay,C0,H,hτ,hdec,hC0,hH,le_max_left _ _,hData,hBc,?_⟩
  intro g hg x hx k hk w hw
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
  have hε:0<2*C*Real.exp (-rate*Real.sqrt h):=by positivity
  have hr:0<r:=mul_pos hτ (Real.sqrt_pos.mpr (Real.sqrt_pos.mpr hn.1))
  have hw':‖w‖≤3*r/2:=by change ‖w‖≤_ at hw;linarith
  have ht:=hcomp x hx g k J hs hn.1 hk hm.1 hm.2.1
    (2*C*Real.exp (-rate*Real.sqrt h)) hε hn.2.1 hm.2.2 r hr hn.2.2.1 w hw'
  apply ht.trans
  simpa only[one_mul] using hn.2.2.2
end WP.Analysis

namespace WP.Analysis
open Set Filter
open scoped Topology
lemma actual_compact_optimal_comparison (P:PsiTheory)(p:ℕ)(hp:1≤p)
    (a b:ℝ)(ha:0<a)(hab:a≤b)(hbc:b<xCritical):
    ∃(Ωf:Set ℂ)(f:ℕ→ℂ→ℂ)(C B κ:ℝ)(S l Bc:ℂ→ℂ)(τ decay C0 H:ℝ),
      IsOpen Ωf ∧ (∀Y∈Icc (0:ℝ) y₀,(Y:ℂ)∈Ωf) ∧ 0<C ∧ 0<B ∧ 0<κ ∧
      (∀j,AnalyticOnNhd ℂ (f j) Ωf) ∧
      (∀j Y,Y∈Icc (0:ℝ) y₀→f j (Y:ℂ)=(HigherOrder.markedCoefficient P p j Y:ℂ)) ∧
      (∀j z,z∈Ωf→‖f j z‖≤C*B^j*(j.factorial:ℝ)^2) ∧
      0<τ ∧ 0<decay ∧ 0<C0 ∧ 0<H ∧
      (∀x∈Icc a b,AnalyticAt ℂ S (x:ℂ) ∧ AnalyticAt ℂ l (x:ℂ) ∧
        (∀ᶠt:ℝ in 𝓝 x,S (t:ℂ)=(extractionS t:ℂ)) ∧
        complexEuler S (x:ℂ)=(WP.Psi x:ℂ) ∧
        ((complexEuler^[2]) S) (x:ℂ)=(WP.euler WP.Psi x:ℂ) ∧
        l (x:ℂ)=((Real.sqrt (WP.euler WP.Psi x))⁻¹:ℝ) ∧
        ∀ᶠq:ℂ in 𝓝 (x:ℂ),(l q)^2*((complexEuler^[2]) S) q=1) ∧
      (∀x∈Ico (0:ℝ) xCritical,AnalyticAt ℂ Bc (x:ℂ) ∧ Bc (x:ℂ)=(extractionB p x:ℂ)) ∧
      ∀g:ℕ,H≤(complexity g p:ℝ)→
      let h:ℝ:=complexity g p
      let J:=⌊κ*Real.sqrt h⌋₊
      2*B*((J:ℝ)+1)^2≤h ∧
      ∀x∈Icc a b,∀k:ℕ,(k:ℝ)=h*Psi x→
      ∀w:ℂ,‖w‖≤τ*Real.sqrt (Real.sqrt h)→
      let σ:ℝ:=Real.sqrt (h*euler Psi x)
      ‖centeredMarkedGenerating P g p k x σ w-compactCenteredFiniteModel P Bc S l f h J (x:ℂ) w‖≤
        C0*Real.exp (-decay*Real.sqrt h):=by
  obtain ⟨Ωf,f,C,B,κ,rate,H0,S0,Bc0,ρ,D,Cs,d,Csmall,DM,E,
    hΩf,hcover,hC,hB,hκ,hrate,hH0,hρ,hρx,hD,hCs,hd,hCsmall,hDM,hE,
    hFa,hf0,hfr,hfb,hSa,hS0,hSd,hBc0,htrace,hlocal,hAa,hAb,hcircle,hmodels⟩:=
    HigherOrder.actual_strong_optimal_origin_model_data P p hp
  obtain ⟨S,l,Bc,τ,decay,C0,H,hτ,hdecay,hC0,hH,hH0H,hData,hBc,hcomp⟩:=
    compact_optimal_comparison_of_parameter_data P p hp a b ha hab hbc Ωf f C B κ rate H0
      hΩf hcover hC hB hrate hH0 hFa hfr hfb (by
        intro g hg
        have hm:=hmodels g hg
        refine ⟨hm.1,?_,hm.2.2.1⟩
        intro Y hY
        exact (hm.2.1 _ (hcover Y hY)).2.1)
  refine ⟨Ωf,f,C,B,κ,S,l,Bc,τ,decay,C0,H,hΩf,hcover,hC,hB,hκ,hFa,hfr,hfb,
    hτ,hdecay,hC0,hH,hData,hBc,?_⟩
  intro g hg
  refine ⟨(hmodels g (hH0H.trans hg)).1,?_⟩
  exact hcomp g hg
end WP.Analysis
