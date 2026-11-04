import WPFormalization.Volumes.UniformLeadingGaussianCharts
import WPFormalization.Volumes.MarkedGaussianChartCore
/-! A uniform central Gaussian error for the actual marked characteristic
function. All analytic chart data are supplied by the proved global
construction, and the actual real relative error comes from Theorem 8.2.
The growing-cutoff domain and cubic smallness conditions remain explicit. -/
noncomputable section
namespace WP
open Set Complex
set_option autoImplicit false

lemma marked_characteristic_gaussian_core_bound (P:PsiTheory)(p:ℕ)(hp:1≤p):
    ∃ρ C D E H:ℝ,0<ρ ∧ 0<C ∧ 0<D ∧ 0<E ∧ 0<H ∧
      ∀g:ℕ,Stable g p→H≤(complexity g p:ℝ)→∀x∈Ioo (0:ℝ) xCritical,
        let h:ℝ:=complexity g p
        let m:ℝ:=min h (h*Psi x)
        0 < m→∀T:ℝ,1≤T→32*T≤ρ*Real.sqrt m→4*C*T^3/(ρ*Real.sqrt m)≤1→
          ∀t:ℝ,|t|≤T→
            ‖scaledMarkedFourier P g p x t-Complex.exp (-(t:ℂ)^2/2)‖≤
              4*D*Real.sqrt (E/h)*Real.exp (256*C*T^2)+
                (8*C*D*T^3+4*D*T)/(ρ*Real.sqrt m):=by
  obtain ⟨ρ,C,D,hρ,hC,hD,hcharts⟩:=uniform_actual_leading_gaussian_charts P p hp
  obtain ⟨E,H,hE,hH,hEH,hrel⟩:=marked_leading_relative_error P p hp
  refine ⟨ρ,C,D,E,H,hρ,hC,hD,hE,hH,?_⟩
  intro g hs hg x hx
  dsimp only
  let h:ℝ:=complexity g p
  let m:ℝ:=min h (h*Psi x)
  intro hm T hT hwindow hsmall t ht
  have hh:0<h:=hH.trans_le hg
  obtain ⟨hchart,hperiod⟩:=hcharts g hs hh x hx hm
  rcases hchart with ⟨L,A,hLa,hL0,hL1,hL2,hLb,hAa,hA0,hAb,htrace⟩
  have htrace':∀u:ℝ,|u|<ρ*Real.sqrt m→
      x*Real.exp (u/Real.sqrt (h*euler Psi x))∈Ioo (0:ℝ) xCritical ∧
      Complex.exp (L (u:ℂ))*A (u:ℂ)=
        ((Real.exp (-(h*Psi x)*u/Real.sqrt (h*euler Psi x))*
          markedModel g p (inverseY (x*Real.exp (u/Real.sqrt (h*euler Psi x))))/
          markedModel g p (inverseY x):ℝ):ℂ):=by
    intro u hu
    have hr:=htrace u hu
    dsimp only at hr
    refine ⟨hr.1,hr.2.trans ?_⟩
    rw[show -((h*Psi x:ℝ):ℂ)*(u:ℂ)/(Real.sqrt (h*euler Psi x):ℂ)=
      ((-(h*Psi x)*u/Real.sqrt (h*euler Psi x):ℝ):ℂ) by push_cast;ring,
      ←Complex.ofReal_exp]
    push_cast
    ring
  have htp:|t|≤Real.pi*Real.sqrt (h*euler Psi x):=by
    have hT0:0≤T:=by linarith only[hT]
    have hTr:T≤ρ*Real.sqrt m:=by linarith only[hwindow,hT0]
    exact ht.trans (hTr.trans hperiod)
  rw[scaledMarkedFourier_eq_real_centered P g p x t htp]
  exact marked_gaussian_chart_core_error P g p hp hs E hE hh (hEH.trans hg) (hrel g hg)
    x (h*Psi x) (Real.sqrt (h*euler Psi x)) ρ C D m T ⟨hx.1.le,hx.2⟩
    hρ hC hD hm hT hwindow hsmall L A hLa hAa hL0 hL1 hL2 hA0 hLb hAb htrace' t ht
end WP
