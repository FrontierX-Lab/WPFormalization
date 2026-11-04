import WPFormalization.Volumes.BoundaryFourierDomination
import WPFormalization.Volumes.UniformFourierTail
/-! Genuine boundary insertion Fourier tails, with constants independent of all lengths. -/
set_option maxHeartbeats 1500000
noncomputable section
namespace WP.BoundaryConvolution
open Set MeasureTheory
lemma boundary_generating_fourier_tail_scaled (P:PsiTheory):
    ∃c C:ℝ,0<c ∧ 0<C ∧ ∀g p:ℕ,1≤p→Stable g p→32≤complexity g p→
      ∀L:Fin p→ℝ,∀x∈Ioo (0:ℝ) xCritical,∀T:ℝ,0≤T→T^2≤(complexity g p:ℝ)→
      let σ:=Real.sqrt ((complexity g p:ℝ)*euler Psi x)
      σ*(∫θ:ℝ in Ioc (-Real.pi) Real.pi ∩ {θ:ℝ | T≤σ*|θ|},
        ‖boundaryG P g p L ((x:ℂ)*Complex.exp ((θ:ℂ)*Complex.I))/
          boundaryG P g p L (x:ℂ)‖)≤C*Real.exp (-c*T^2):=by
  obtain ⟨c,hc,htail⟩:=PositiveConvolution.universalV_standardized_tail_power_bound P
  obtain ⟨C,hC,hfull⟩:=PositiveConvolution.universalV_character_integral_scaled_bound P (1/2) (by norm_num)
  refine ⟨c,C,hc,hC,?_⟩
  intro g p hp hs hlarge L x hx T hT0 hT
  let h:ℕ:=complexity g p
  let h₁:ℕ:=h/2
  let h₂:ℕ:=h-h₁
  let σ:=Real.sqrt ((h:ℝ)*euler Psi x)
  let q:ℝ→ℝ:=fun θ=>‖universalV P ((x:ℂ)*Complex.exp ((θ:ℂ)*Complex.I))/universalV P x‖
  let f:ℝ→ℝ:=fun θ=>‖boundaryG P g p L ((x:ℂ)*Complex.exp ((θ:ℂ)*Complex.I))/
      boundaryG P g p L (x:ℂ)‖
  let A:Set ℝ:=Ioc (-Real.pi) Real.pi ∩ {θ:ℝ | T≤σ*|θ|}
  have hh:0<(h:ℝ):=by exact_mod_cast (show 0<h by dsimp[h];omega)
  have hv:0<euler Psi x:=mul_pos hx.1 (Analysis.Psi_deriv_pos_interior x ⟨hx.1.le,hx.2⟩)
  have hσ:0<σ:=Real.sqrt_pos.mpr (mul_pos hh hv)
  have hσsq:σ^2=(h:ℝ)*euler Psi x:=Real.sq_sqrt (mul_pos hh hv).le
  have h₁lower:(h:ℝ)/4≤h₁:=by
    have hn:h≤4*h₁:=by dsimp[h₁];dsimp[h] at *;omega
    have hn' : (h:ℝ)≤4*(h₁:ℝ):=by exact_mod_cast hn
    linarith
  have h₂lower:(1/2:ℝ)*(h:ℝ)≤h₂:=by
    have hn:h≤2*h₂:=by dsimp[h₂,h₁];omega
    have hn':(h:ℝ)≤2*(h₂:ℝ):=by exact_mod_cast hn
    linarith
  have h₂16:16≤h₂:=by dsimp[h₂,h₁];dsimp[h] at *;omega
  have hsplit:h=h₁+h₂:=by dsimp[h₂];omega
  have hcontq:Continuous q:=by
    exact ((PositiveConvolution.universalV_circle_continuous P x hx).div_const _).norm
  have hcontf:Continuous f:=by
    apply Continuous.norm
    apply Continuous.div_const
    rw[continuous_iff_continuousAt]
    intro θ
    have hn:‖(x:ℂ)*Complex.exp ((θ:ℂ)*Complex.I)‖<xCritical:=by
      rw[norm_mul,Complex.norm_of_nonneg hx.1.le,Complex.norm_exp_ofReal_mul_I,mul_one]
      exact hx.2
    exact ContinuousAt.comp (f := fun θ:ℝ => (x:ℂ)*Complex.exp ((θ:ℂ)*Complex.I))
      (g := boundaryG P g p L) (x := θ)
      (boundaryG_analyticAt P g p L _ hn).continuousAt (by fun_prop)
  have hab:-Real.pi≤Real.pi:=by linarith[Real.pi_pos]
  have hIf:IntegrableOn f (Ioc (-Real.pi) Real.pi):=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp (hcontf.intervalIntegrable _ _)
  have hIq:IntegrableOn (fun θ=>q θ^h₂) (Ioc (-Real.pi) Real.pi):=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp ((hcontq.pow h₂).intervalIntegrable _ _)
  have hA:MeasurableSet A:=measurableSet_Ioc.inter (isClosed_le continuous_const (by fun_prop)).measurableSet
  have hAs:A⊆Ioc (-Real.pi) Real.pi:=inter_subset_left
  have hpoint:∀θ∈A,f θ≤Real.exp (-c*T^2)*q θ^h₂:=by
    intro θ hθ
    have hθcc:θ∈Icc (-Real.pi) Real.pi:=⟨hθ.1.1.le,hθ.1.2⟩
    have hts:T^2≤(h:ℝ)*euler Psi x*θ^2:=by
      have ht:=pow_le_pow_left₀ hT0 hθ.2 2
      rw[mul_pow,sq_abs,hσsq] at ht
      exact ht
    have ht:=htail (h:ℝ) h₁ hh h₁lower x hx θ hθcc T hT hts
    have hnorm:‖(x:ℂ)*Complex.exp ((θ:ℂ)*Complex.I)‖=x:=by
      rw[norm_mul,Complex.norm_of_nonneg hx.1.le,Complex.norm_exp_ofReal_mul_I,mul_one]
    have hGnorm : ‖boundaryG P g p L (x:ℂ)‖=(boundaryG P g p L (x:ℂ)).re := by
      rw [boundaryG_ofReal P g p hp hs L x ⟨hx.1.le,hx.2⟩,
        Complex.norm_real,Real.norm_eq_abs,Complex.ofReal_re]
      exact abs_of_pos (stringBoundaryAmplitude_pos P g p hp hs _
        (fun i => lengthTime_nonneg _) _ (inverseY_branch x ⟨hx.1.le,hx.2⟩).1)
    have hcirc:f θ≤q θ^h := by
      dsimp only [f,q,h]
      rw [norm_div,hGnorm]
      exact boundaryG_circle_domination P g p hp hs L x ⟨hx.1.le,hx.2⟩ _ hnorm.le
    have he:q θ^h=q θ^h₁*q θ^h₂:=by rw[←pow_add,←hsplit]
    rw[he] at hcirc
    exact hcirc.trans (mul_le_mul_of_nonneg_right ht (pow_nonneg (norm_nonneg _) _))
  have hInt:(∫θ:ℝ in A,f θ)≤Real.exp (-c*T^2)*(∫θ:ℝ in Ioc (-Real.pi) Real.pi,q θ^h₂):=by
    have hIe:IntegrableOn (fun θ=>Real.exp (-c*T^2)*q θ^h₂) (Ioc (-Real.pi) Real.pi):=
      hIq.const_mul (Real.exp (-c*T^2))
    have hi:=setIntegral_mono_on (hIf.mono_set hAs)
      (hIe.mono_set hAs) hA hpoint
    rw[integral_const_mul] at hi
    have hsInt:(∫θ:ℝ in A,q θ^h₂)≤∫θ:ℝ in Ioc (-Real.pi) Real.pi,q θ^h₂:=
      setIntegral_mono_set hIq (Filter.Eventually.of_forall (fun θ=>pow_nonneg (norm_nonneg _) _))
        (Filter.Eventually.of_forall (fun θ hθ=>hAs hθ))
    exact hi.trans (mul_le_mul_of_nonneg_left hsInt (Real.exp_pos _).le)
  have hI: (∫θ:ℝ in Ioc (-Real.pi) Real.pi,q θ^h₂)*σ≤C:=by
    have ht:=hfull h h₂ (by dsimp[h];omega) h₂16 h₂lower x hx
    rw[intervalIntegral.integral_of_le hab] at ht
    exact ht
  have hfinal:=mul_le_mul_of_nonneg_left hInt hσ.le
  calc
    _≤σ*(Real.exp (-c*T^2)*(∫θ:ℝ in Ioc (-Real.pi) Real.pi,q θ^h₂)):=hfinal
    _=Real.exp (-c*T^2)*((∫θ:ℝ in Ioc (-Real.pi) Real.pi,q θ^h₂)*σ):=by ring
    _≤Real.exp (-c*T^2)*C:=mul_le_mul_of_nonneg_left hI (Real.exp_pos _).le
    _=_:=by ring
end WP.BoundaryConvolution
