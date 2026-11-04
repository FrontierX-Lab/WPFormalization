import WPFormalization.Analysis.ChainProfileIntegral
import WPFormalization.Analysis.ChainRiemannSum

/-! The exact primitive identity (12.2), before discretizing cusp addition. -/
noncomputable section
namespace WP.Analysis
open Set Filter MeasureTheory
open scoped Topology

def chainPrimitiveY (Y : ℝ) : ℝ :=
  -(2+WP.density Y)*Real.log (2*WP.J Y)-Real.log (4*WP.Delta Y/Real.pi^2)

lemma chainPrimitiveY_eq_profile (Y : ℝ) (hY : Y ∈ Ico 0 y₀) :
    chainPrimitiveY Y = (1+WP.density Y/2)*chainClosedProfileY Y := by
  have hn : 2+WP.density Y ≠ 0 := by linarith [WP.density_nonneg Y hY]
  dsimp only [chainPrimitiveY,chainClosedProfileY]
  rw [WP.beta_density_identity Y hY]
  field_simp [hn]
  ring

lemma chainPrimitiveY_hasDerivAt (Y : ℝ) (hY : Y ∈ Ico 0 y₀) :
    HasDerivAt chainPrimitiveY
      (deriv WP.density Y*chainCuspLogProfile (WP.density Y)) Y := by
  have hpJ := WP.J_pos Y hY
  have hpD := WP.Delta_pos Y hY
  have hJ := (J_analyticAt_interior Y hY).differentiableAt.hasDerivAt
  have hl := (density_analyticAt_interior Y hY).differentiableAt.hasDerivAt
  have hlogJ := (hJ.const_mul 2).log (by positivity : 2*WP.J Y ≠ 0)
  have hlogD := (((chain_Delta_hasDerivAt Y hY).const_mul 4).div_const
    (Real.pi^2)).log (by positivity : 4*WP.Delta Y/Real.pi^2 ≠ 0)
  have hd := (((hasDerivAt_const Y (2 : ℝ)).add hl).neg.mul hlogJ).sub hlogD
  convert hd using 1
  · rfl
  · rw [chainCuspLogProfile,chain_densityY_density Y hY]
    have hrel := chain_J_Delta_derivative_identity Y hY
    have hdensity := density_J_formula_on_domain Y (stationaryParameterDomain_contains Y hY)
    have hJX := J_sub_XR_pos_interior Y hY
    simp only [Pi.neg_apply,Pi.add_apply]
    rw [hdensity]
    field_simp [hpJ.ne',hpD.ne',Real.pi_ne_zero,hJX.ne']
    linear_combination (WP.J Y)*hrel

lemma chainPrimitiveY_zero : chainPrimitiveY 0 = 0 := by
  rw [chainPrimitiveY_eq_profile 0 ⟨le_rfl,y₀_pos⟩,chainClosedProfileY_zero,mul_zero]

lemma chainProfile_primitive_parameter (Y : ℝ) (hY : Y ∈ Ico 0 y₀) :
    (∫ l in (0 : ℝ)..WP.density Y, chainCuspLogProfile l) =
      (1+WP.density Y/2)*WP.chainProfile (WP.beta Y) := by
  have hu : uIcc (0 : ℝ) Y = Icc 0 Y := uIcc_of_le hY.1
  have hsubset : Icc (0 : ℝ) Y ⊆ Ico 0 y₀ :=
    fun t ht => ⟨ht.1,lt_of_le_of_lt ht.2 hY.2⟩
  have hdensity : ∀ t ∈ uIcc (0 : ℝ) Y,
      HasDerivAt WP.density (deriv WP.density t) t := by
    intro t ht
    exact (density_analyticAt_interior t (hsubset (hu ▸ ht))).differentiableAt.hasDerivAt
  have hdcont : ContinuousOn (deriv WP.density) (uIcc (0 : ℝ) Y) :=
    fun t ht => (density_analyticAt_interior t (hsubset (hu ▸ ht))).deriv.continuousAt.continuousWithinAt
  have himg : WP.density '' uIcc (0 : ℝ) Y ⊆ Ici 0 := by
    rintro _ ⟨t,ht,rfl⟩
    exact WP.density_nonneg t (hsubset (hu ▸ ht))
  have hsub := intervalIntegral.integral_comp_mul_deriv' hdensity hdcont
    (chainCuspLogProfile_continuousOn.mono himg)
  have hcc : ContinuousOn (fun t : ℝ => chainCuspLogProfile (WP.density t))
      (uIcc (0 : ℝ) Y) := by
    apply chainCuspLogProfile_continuousOn.comp
      (fun t ht => (hdensity t ht).continuousAt.continuousWithinAt)
    exact fun t ht => WP.density_nonneg t (hsubset (hu ▸ ht))
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => chainPrimitiveY_hasDerivAt t (hsubset (hu ▸ ht)))
    ((hdcont.mul hcc).intervalIntegrable)
  have heq : (∫ t in (0 : ℝ)..Y, (chainCuspLogProfile ∘ WP.density) t*deriv WP.density t) =
      ∫ t in (0 : ℝ)..Y, deriv WP.density t*chainCuspLogProfile (WP.density t) := by
    apply intervalIntegral.integral_congr
    intro t _
    exact mul_comm _ _
  rw [heq,WP.density_zero_value,hFTC,chainPrimitiveY_zero,sub_zero,
    chainPrimitiveY_eq_profile Y hY,← chainProfile_closed_form_parameter Y hY] at hsub
  exact hsub.symm

lemma chainProfile_primitive (l : ℝ) (hl : 0 ≤ l) :
    (∫ v in (0 : ℝ)..l, chainCuspLogProfile v) =
      (1+l/2)*WP.chainProfile (l/(2+l)) := by
  have hs := densityY_spec l hl
  have he := chainProfile_primitive_parameter (WP.densityY l) hs.1
  rw [WP.beta_density_identity _ hs.1,hs.2] at he
  exact he

lemma chainProfile_primitive_genus (g : ℝ) (hg : 0 < g) (n : ℝ) (hn : 0 ≤ n) :
    g*(∫ v in (0 : ℝ)..n/g, chainCuspLogProfile v) =
      ((2*g+n)/2)*WP.chainProfile (n/(2*g+n)) := by
  rw [chainProfile_primitive (n/g) (div_nonneg hn hg.le)]
  have hden : 2+n/g ≠ 0 := by positivity
  have hsum : 2*g+n ≠ 0 := by positivity
  have ht : (n/g)/(2+n/g) = n/(2*g+n) := by field_simp
  rw [ht]
  have hc : g*(1+(n/g)/2) = (2*g+n)/2 := by field_simp <;> ring
  rw [← mul_assoc,hc]

lemma chain_actual_cusp_riemann_sum :
    ∃ C : ℝ, 0 < C ∧ ∀ g : ℕ, 1 ≤ g → ∀ n : ℕ,
      |(∑ j ∈ Finset.range n, chainCuspLogProfile ((j : ℝ)/g))-
        ((2*(g : ℝ)+n)/2)*WP.chainProfile ((n : ℝ)/(2*g+n))| ≤ C := by
  obtain ⟨C,hC,hb⟩ := chainCuspLogProfile_variation_bound
  refine ⟨C,hC,?_⟩
  intro g hg n
  have hgr : (0 : ℝ) < g := by exact_mod_cast (show 0 < g by omega)
  have he := chain_antitone_riemann_sum_abs chainCuspLogProfile
    chainCuspLogProfile_antitoneOn C hb (g : ℝ) hgr n
  rwa [chainProfile_primitive_genus (g : ℝ) hgr (n : ℝ) (Nat.cast_nonneg n)] at he

end WP.Analysis
