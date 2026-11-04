import WPFormalization.Analysis.SlitGevreyWindow
/-! The actual quarter-power window in the small-density middle range.
A fixed lower frequency k>=kappaLow*sqrt(h) and upper mean k<=K*h*x
place the entire slit-transfer disk inside rho*sqrt(h*x). The same
window absorbs its model growth into the Gevrey-two exponential error.
This is a proved numerical lemma, with all constants before h/x/k. -/
noncomputable section
namespace WP.Analysis
open Set Filter
open scoped Topology
lemma origin_slit_gevrey_two_window_constants (ρ D E Cerr a K κlo:ℝ)
    (hρ:0<ρ)(hD:0<D)(hE:0<E)(hCerr:0<Cerr)(ha:0<a)(hK:0<K)(hκlo:0<κlo):
    ∃τ b C0 H:ℝ,0<τ ∧ 0<b ∧ 0<C0 ∧ 0<H ∧ ∀h:ℝ,H≤h→
      0<h ∧ Cerr*Real.exp (-a*Real.sqrt h)≤1/2 ∧
      (4*Real.sqrt (Cerr*Real.exp (-a*Real.sqrt h))*
        (D*Real.exp (E*(16*(τ*Real.sqrt (Real.sqrt h)))^2))≤C0*Real.exp (-b*Real.sqrt h)) ∧
      ∀x k:ℝ,0<x→κlo*Real.sqrt h≤k→k≤K*h*x→
        16*(τ*Real.sqrt (Real.sqrt h))<ρ*Real.sqrt (h*x):=by
  obtain ⟨τ0,b,C0,H,hτ0,hb,hC0,hH,hwindow⟩:=
    slit_gevrey_two_window_constants 1 D E (Cerr/2) a zero_lt_one hD hE (by positivity) ha
  have hCC:2*(Cerr/2)=Cerr:=by ring
  simp only[hCC] at hwindow
  let R0:ℝ:=ρ*Real.sqrt (κlo/K)
  have hR0:0<R0:=mul_pos hρ (Real.sqrt_pos.mpr (div_pos hκlo hK))
  let τ:ℝ:=min τ0 (R0/32)
  have hτ:0<τ:=lt_min hτ0 (by positivity)
  have hτ0':τ≤τ0:=min_le_left _ _
  have hτR:τ≤R0/32:=min_le_right _ _
  have hτRstrict:16*τ<R0:=by linarith
  refine ⟨τ,b,C0,H,hτ,hb,hC0,hH,?_⟩
  intro h hh
  have hn:=hwindow h hh
  have hq:0<Real.sqrt (Real.sqrt h):=Real.sqrt_pos.mpr (Real.sqrt_pos.mpr hn.1)
  refine ⟨hn.1,hn.2.1,?_,?_⟩
  · apply le_trans _ hn.2.2.2
    apply mul_le_mul_of_nonneg_left _ (by positivity:0≤4*Real.sqrt (Cerr*Real.exp (-a*Real.sqrt h)))
    apply mul_le_mul_of_nonneg_left _ hD.le
    apply Real.exp_le_exp.mpr
    apply mul_le_mul_of_nonneg_left _ hE.le
    apply pow_le_pow_left₀ (by positivity)
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hτ0' hq.le) (by norm_num:(0:ℝ)≤16)
  · intro x k hx hlow hhigh
    have hscale0:(κlo/K)*Real.sqrt h≤h*x:=by
      have he:(κlo/K)*Real.sqrt h=(κlo*Real.sqrt h)/K:=by ring
      rw[he]
      apply (div_le_iff₀ hK).mpr
      nlinarith[hlow,hhigh]
    have hscale:Real.sqrt (κlo/K)*Real.sqrt (Real.sqrt h)≤Real.sqrt (h*x):=by
      rw[←Real.sqrt_mul (div_pos hκlo hK).le]
      exact Real.sqrt_le_sqrt hscale0
    calc
      _<R0*Real.sqrt (Real.sqrt h):=by nlinarith[mul_lt_mul_of_pos_right hτRstrict hq]
      _=ρ*(Real.sqrt (κlo/K)*Real.sqrt (Real.sqrt h)):=by dsimp[R0];ring
      _≤ρ*Real.sqrt (h*x):=mul_le_mul_of_nonneg_left hscale hρ.le
end WP.Analysis
