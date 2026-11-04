import WPFormalization.Analysis.CriticalBesselData
import WPFormalization.Analysis.KernelExpansion
import WPFormalization.Analysis.NormalizedKernelFamily

/-! The complete critical scaling limit, proved using real first roots and
joint linear error bounds. No full K zero distribution, canonical product,
uniform kernel moment bound, or implicit-function assumption is used. -/
noncomputable section
namespace WP.Analysis
open MeasureTheory Filter
open scoped Topology
lemma K_r_zero (Y : ℝ) (hY : Y ∈ Set.Ico 0 y₀) : K Y (r Y) = 0 := by
  let S := {z : ℝ | 0 < z ∧ K Y z = 0}
  have hs : S.Nonempty := by
    obtain ⟨z,hz,hroot⟩ := rootKernel_positive_zero Y hY.1
      (fun u hu => a_pos u ⟨hu.1,lt_of_le_of_lt hu.2 hY.2⟩)
    exact ⟨z,hz,hroot⟩
  have hb : BddBelow S := ⟨0,fun z hz => hz.1.le⟩
  have hc : Continuous (fun z : ℝ => K Y z) := (K_differentiable Y).continuous.comp Complex.continuous_ofReal
  have hclosed : IsClosed {z : ℝ | K Y z = 0} := isClosed_eq hc continuous_const
  have hsubset : closure S ⊆ {z : ℝ | K Y z = 0} := closure_minimal (fun z hz => hz.2) hclosed
  exact hsubset (csInf_mem_closure hs hb)
lemma r_le_of_K_zero (Y z : ℝ) (hz : 0 < z) (hroot : K Y z = 0) : r Y ≤ z := by
  exact csInf_le ⟨0,fun x hx => hx.1.le⟩ ⟨hz,hroot⟩
lemma r_le_twice_a_of_approx (Y : ℝ) (hY : Y ∈ Set.Ico 0 y₀)
    (c δ : ℝ) (hc : 0 < c) (hδ : 0 < δ)
    (hnear : ∀ z : ℂ, ‖z‖ < δ → ‖K Y z-deriv X Y+(c : ℂ)*z‖ ≤ (c/4)*‖z‖)
    (haSmall : 2*a Y/c < δ) : r Y ≤ 2*a Y/c := by
  let Z : ℝ := 2*a Y/c
  have haP := a_pos Y hY
  have hZ : 0 < Z := by dsimp [Z]; positivity
  have hNZ : ‖(Z : ℂ)‖ < δ := by simpa [abs_of_pos hZ] using haSmall
  have hnorm := hnear (Z : ℂ) hNZ
  have hline : |(K Y Z).re-a Y+c*Z| ≤ (c/4)*Z := by
    have h := (Complex.abs_re_le_norm (K Y Z-deriv X Y+(c : ℂ)*Z)).trans hnorm
    simpa [derivX_ofReal,Complex.add_re,Complex.sub_re,Complex.mul_re,abs_of_pos hZ] using h
  have hcz : c*Z = 2*a Y := by dsimp [Z]; field_simp
  have hKneg : (K Y Z).re < 0 := by
    have h := (abs_le.mp hline).2
    nlinarith
  have hK0 : 0 < (K Y 0).re := by simpa only [K_zero,derivX_ofReal,Complex.ofReal_re] using haP
  have hcK : Continuous (fun z : ℝ => (K Y z).re) :=
    Complex.continuous_re.comp ((K_differentiable Y).continuous.comp Complex.continuous_ofReal)
  obtain ⟨z,hz,hroot⟩ := intermediate_value_Icc' hZ.le hcK.continuousOn
    (show (0 : ℝ) ∈ Set.Icc (K Y Z).re (K Y 0).re from ⟨hKneg.le,hK0.le⟩)
  have hz0 : z ≠ 0 := by
    intro he
    rw [he] at hroot
    exact (ne_of_gt hK0) hroot
  have hzP : 0 < z := lt_of_le_of_ne hz.1 (Ne.symm hz0)
  have hrootC : K Y z = 0 := by
    apply Complex.ext
    · exact hroot
    · simpa only [K,rootKernel,Complex.zero_im] using rootKernel_real Y z
  exact (r_le_of_K_zero Y z hzP hrootC).trans hz.2

def criticalKernelSlope : ℝ := -(iteratedDeriv 2 X (y₀ : ℂ)).re/3
lemma criticalKernelSlope_pos : 0 < criticalKernelSlope :=
  div_pos (neg_pos.mpr iteratedDeriv_two_X_y₀_neg) (by norm_num)
lemma criticalKernelSlope_complex : iteratedDeriv 2 X (y₀ : ℂ)/3 = -(criticalKernelSlope : ℂ) := by
  have hi : (iteratedDeriv 2 X (y₀ : ℂ)).im = 0 := by simpa using iteratedDeriv_X_im_ofReal 2 y₀
  apply Complex.ext
  · simp [Complex.div_re,criticalKernelSlope]
    ring
  · simp [Complex.div_im,hi]
lemma a_continuous : Continuous a := by
  unfold a
  have hc : Continuous (deriv X) := by
    simpa only [iteratedDeriv_one] using (iteratedDeriv_X_differentiable 1).continuous
  exact Complex.continuous_re.comp (hc.comp Complex.continuous_ofReal)
lemma a_tendsto_zero_left : Tendsto a (𝓝[<] y₀) (𝓝 0) := by
  have h : Tendsto a (𝓝[<] y₀) (𝓝 (a y₀)) :=
    (a_continuous.continuousAt : ContinuousAt a y₀).mono_left nhdsWithin_le_nhds
  simpa only [a_y₀_zero] using h
lemma eventually_interior_left : ∀ᶠ Y in 𝓝[<] y₀, Y ∈ Set.Ico 0 y₀ := by
  have hp : ∀ᶠ Y : ℝ in 𝓝 y₀, 0 < Y := isOpen_Ioi.mem_nhds y₀_pos
  filter_upwards [hp.filter_mono nhdsWithin_le_nhds,self_mem_nhdsWithin] with Y hP hY
  exact ⟨hP.le,hY⟩
lemma eventually_complex_close_left (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ Y : ℝ in 𝓝[<] y₀, ‖(Y : ℂ)-(y₀ : ℂ)‖ < δ := by
  have h : ∀ᶠ Y : ℝ in 𝓝 y₀, ‖(Y : ℂ)-(y₀ : ℂ)‖ < δ := by
    filter_upwards [Metric.ball_mem_nhds y₀ hδ] with Y hY
    simpa [Metric.mem_ball,Real.dist_eq,← Complex.ofReal_sub] using hY
  exact h.filter_mono nhdsWithin_le_nhds
lemma r_upper_bound_left :
    ∀ᶠ Y in 𝓝[<] y₀, r Y ≤ 2*a Y/criticalKernelSlope := by
  have hc := criticalKernelSlope_pos
  obtain ⟨δ,hδ,happrox⟩ := K_first_order_uniform (y₀ : ℂ) (criticalKernelSlope/4) (by positivity)
  have hsmall : ∀ᶠ Y in 𝓝[<] y₀, a Y < δ*criticalKernelSlope/2 :=
    a_tendsto_zero_left.eventually (eventually_lt_nhds (by positivity : (0 : ℝ)<δ*criticalKernelSlope/2))
  filter_upwards [eventually_interior_left,eventually_complex_close_left δ hδ,hsmall] with Y hY hn ha
  apply r_le_twice_a_of_approx Y hY criticalKernelSlope δ hc hδ
  · intro z hz
    have h := happrox Y z hn hz
    rw [criticalKernelSlope_complex] at h
    simpa only [neg_mul,sub_neg_eq_add] using h
  · apply (div_lt_iff₀ hc).mpr
    linarith
lemma r_tendsto_zero_left : Tendsto r (𝓝[<] y₀) (𝓝 0) := by
  have hnonneg : ∀ᶠ Y in 𝓝[<] y₀, 0 ≤ r Y :=
    eventually_interior_left.mono (fun Y hY => (r_pos Y hY).le)
  have hu : Tendsto (fun Y => 2*a Y/criticalKernelSlope) (𝓝[<] y₀) (𝓝 0) := by
    simpa only [mul_zero,zero_div] using
      (tendsto_const_nhds.mul a_tendsto_zero_left).div_const criticalKernelSlope
  exact squeeze_zero' hnonneg r_upper_bound_left hu

lemma a_div_r_tendsto_left : Tendsto (fun Y => a Y/r Y) (𝓝[<] y₀) (𝓝 criticalKernelSlope) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨δ,hδ,happrox⟩ := K_first_order_uniform (y₀ : ℂ) (ε/2) (by positivity)
  have hrsmall : ∀ᶠ Y in 𝓝[<] y₀, r Y < δ :=
    r_tendsto_zero_left.eventually (eventually_lt_nhds hδ)
  filter_upwards [eventually_interior_left,eventually_complex_close_left δ hδ,hrsmall] with Y hY hn hr
  have hrP := r_pos Y hY
  have h := happrox Y (r Y) hn (by simpa only [Complex.norm_real,Real.norm_eq_abs,abs_of_pos hrP] using hr)
  rw [K_r_zero Y hY,criticalKernelSlope_complex,derivX_ofReal] at h
  have he : (0 : ℂ)-(a Y : ℂ)-(-(criticalKernelSlope : ℂ))*(r Y : ℂ) =
      -Complex.ofReal (a Y-criticalKernelSlope*r Y) := by push_cast; ring
  rw [he,norm_neg] at h
  have herr : |a Y-criticalKernelSlope*r Y| ≤ (ε/2)*r Y := by simpa only [Complex.norm_real,Real.norm_eq_abs,abs_of_pos hrP] using h
  have heq : a Y/r Y-criticalKernelSlope = (a Y-criticalKernelSlope*r Y)/r Y := by field_simp
  have hratio : |a Y/r Y-criticalKernelSlope| ≤ ε/2 := by
    rw [heq,abs_div,abs_of_pos hrP]
    exact (div_le_iff₀ hrP).mpr herr
  simpa only [Real.dist_eq] using lt_of_le_of_lt hratio (by linarith : ε/2 < ε)
lemma r_div_a_tendsto_left : Tendsto (fun Y => r Y/a Y) (𝓝[<] y₀) (𝓝 criticalKernelSlope⁻¹) := by
  simpa only [inv_div] using a_div_r_tendsto_left.inv₀ (ne_of_gt criticalKernelSlope_pos)
lemma critical_r_ratio :
    Tendsto (fun Y => r Y/(3*a Y/(-(iteratedDeriv 2 X (y₀ : ℂ)).re))) (𝓝[<] y₀) (𝓝 1) := by
  have he : (fun Y => r Y/(3*a Y/(-(iteratedDeriv 2 X (y₀ : ℂ)).re))) =
      fun Y => (r Y/a Y)*criticalKernelSlope := by
    funext Y
    dsimp [criticalKernelSlope]
    simp only [div_eq_mul_inv,mul_inv_rev,inv_inv]
    ring
  rw [he]
  simpa only [inv_mul_cancel₀ (ne_of_gt criticalKernelSlope_pos)] using
    r_div_a_tendsto_left.mul_const criticalKernelSlope

lemma critical_normalized_kernels_uniform (R : ℝ) (hR : 0 < R) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ Y in 𝓝[<] y₀, ∀ w : ℂ, ‖w‖ ≤ R →
      ‖barK Y w-(1-w)‖ ≤ ε ∧ ‖barH Y w-(1-3/5*w)‖ ≤ ε := by
  have hAr : ∀ᶠ Y in 𝓝[<] y₀, 0 < a Y ∧ 0 < r Y :=
    eventually_interior_left.mono (fun Y hY => ⟨a_pos Y hY,r_pos Y hY⟩)
  have hAK : ∀ e : ℝ, 0 < e → ∃ δ : ℝ, 0 < δ ∧ ∀ Y : ℝ, ∀ z : ℂ,
      |Y-y₀| < δ → ‖z‖ < δ → ‖K Y z-(a Y : ℂ)-(iteratedDeriv 2 X (y₀ : ℂ)/3)*z‖ ≤ e*‖z‖ := by
    intro e he
    obtain ⟨δ,hδ,h⟩ := K_first_order_uniform (y₀ : ℂ) e he
    refine ⟨δ,hδ,?_⟩
    intro Y z hY hz
    have hn : ‖(Y : ℂ)-(y₀ : ℂ)‖ < δ := by
      rw [← Complex.ofReal_sub]
      simpa only [Complex.norm_real,Real.norm_eq_abs] using hY
    simpa only [derivX_ofReal] using h Y z hn hz
  have hAH : ∀ e : ℝ, 0 < e → ∃ δ : ℝ, 0 < δ ∧ ∀ Y : ℝ, ∀ z : ℂ,
      |Y-y₀| < δ → ‖z‖ < δ → ‖H Y z-(a Y : ℂ)-(iteratedDeriv 2 X (y₀ : ℂ)/5)*z‖ ≤ e*‖z‖ := by
    intro e he
    obtain ⟨δ,hδ,h⟩ := H_first_order_uniform (y₀ : ℂ) e he
    refine ⟨δ,hδ,?_⟩
    intro Y z hY hz
    have hn : ‖(Y : ℂ)-(y₀ : ℂ)‖ < δ := by
      rw [← Complex.ofReal_sub]
      simpa only [Complex.norm_real,Real.norm_eq_abs] using hY
    simpa only [derivX_ofReal] using h Y z hn hz
  have hK := normalized_family_uniform (fun Y z => K Y z) a r y₀
    (iteratedDeriv 2 X (y₀ : ℂ)/3) criticalKernelSlope⁻¹ hAr r_tendsto_zero_left r_div_a_tendsto_left hAK R ε hR hε
  have hH := normalized_family_uniform (fun Y z => H Y z) a r y₀
    (iteratedDeriv 2 X (y₀ : ℂ)/5) criticalKernelSlope⁻¹ hAr r_tendsto_zero_left r_div_a_tendsto_left hAH R ε hR hε
  have hcN : (criticalKernelSlope : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt criticalKernelSlope_pos
  have hCK : (iteratedDeriv 2 X (y₀ : ℂ)/3)*((criticalKernelSlope⁻¹ : ℝ) : ℂ) = -1 := by
    rw [criticalKernelSlope_complex]
    push_cast
    rw [neg_mul,mul_inv_cancel₀ hcN]
  have hCH : (iteratedDeriv 2 X (y₀ : ℂ)/5)*((criticalKernelSlope⁻¹ : ℝ) : ℂ) = -(3/5 : ℂ) := by
    have he : iteratedDeriv 2 X (y₀ : ℂ)/5 = (3/5 : ℂ)*(iteratedDeriv 2 X (y₀ : ℂ)/3) := by ring
    rw [he,mul_assoc,hCK]
    ring
  filter_upwards [eventually_interior_left,hK,hH] with Y hY hK hH
  intro w hw
  constructor
  · simp only [barK,if_neg (ne_of_lt hY.2)]
    simpa only [hCK,neg_one_mul,← sub_eq_add_neg] using hK w hw
  · simp only [barH,if_neg (ne_of_lt hY.2)]
    simpa only [hCH,neg_mul,← sub_eq_add_neg] using hH w hw

end WP.Analysis

namespace WP
open Filter
open scoped Topology
/- Eq.2.6: ratio asymptotics and locally uniform convergence in complex w. -/
/- Blueprint label(s): eq:P10
Paper v3: 2.6 [PDF 17]
Status: VERIFIED (actual factorial series, alternating bounds and first real roots)
-/
@[blueprint "eq:P10"]
theorem critical_kernel_limits :
    Tendsto (fun Y => r Y / (3*a Y / (-(iteratedDeriv 2 X y₀).re))) (𝓝[<] y₀) (𝓝 1) ∧
    (∀ R : ℝ, 0 < R → ∀ ε : ℝ, 0 < ε →
      ∀ᶠ Y in 𝓝[<] y₀, ∀ w : ℂ, ‖w‖ ≤ R →
        ‖barK Y w - (1-w)‖ ≤ ε ∧ ‖barH Y w - (1-3/5*w)‖ ≤ ε) := by
  refine ⟨Analysis.critical_r_ratio,?_⟩
  intro R hR ε hε
  exact Analysis.critical_normalized_kernels_uniform R hR ε hε


end WP
