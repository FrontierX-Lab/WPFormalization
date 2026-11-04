import WPFormalization.RandomGeometry.PrimitivePlanarScale
import WPFormalization.Analysis.ChainParameterProfile

noncomputable section
namespace WP.RandomGeometry
open Set Filter
open scoped Topology ENNReal

/-- The actual inverse-density saddle, completed at infinite density. -/
def planarDensitySaddle (l : ℝ≥0∞) : ℝ :=
  if l = ∞ then xCritical else XR (densityY l.toReal)

@[simp] lemma planar_density_saddle_top : planarDensitySaddle ∞ = xCritical := by
  simp [planarDensitySaddle]

lemma planar_density_saddle_finite (l : ℝ≥0∞) (hl : l ≠ ∞) :
    planarDensitySaddle l = XR (densityY l.toReal) := by
  simp [planarDensitySaddle,hl]

@[simp] lemma planar_density_saddle_zero : planarDensitySaddle 0 = 0 := by
  have hy : densityY 0 = 0 := by
    simpa only [density_zero_value] using Analysis.chain_densityY_density 0 ⟨le_rfl,y₀_pos⟩
  simp [planarDensitySaddle,hy,XR_zero]

lemma planar_density_saddle_mem (l : ℝ≥0∞) :
    planarDensitySaddle l ∈ Icc (0:ℝ) xCritical := by
  by_cases hl : l = ∞
  · simp only [hl,planar_density_saddle_top,mem_Icc,le_refl,and_true]
    exact Analysis.xCritical_pos_parameter.le
  · rw [planar_density_saddle_finite l hl]
    have hy := (Analysis.densityY_spec l.toReal ENNReal.toReal_nonneg).1
    refine ⟨XR_nonneg_interior _ hy,?_⟩
    exact XR_strictMonoOn.monotoneOn hy.2.le (by simp) hy.2.le

lemma primitive_density_shift_identity (g n : ℕ) (hg : 1 ≤ g) (hn : 1 ≤ n) :
    2*((n-1:ℕ):ℝ)/(2*(g:ℝ)-1) =
      (((n:ℝ)/g)-1/(g:ℝ))*(2*(g:ℝ)/(2*(g:ℝ)-1)) := by
  have hgR : (1:ℝ) ≤ g := by exact_mod_cast hg
  have hg0 : (g:ℝ) ≠ 0 := by linarith
  rw [Nat.cast_sub hn,Nat.cast_one]
  field_simp

lemma primitive_saddle_mem_closed (g n : ℕ) (hg : 1 ≤ g) :
    primitiveSaddleX g n ∈ Icc (0:ℝ) xCritical := by
  have hgR : (1:ℝ) ≤ g := by exact_mod_cast hg
  have hd : 0 ≤ 2*((n-1:ℕ):ℝ)/(2*(g:ℝ)-1) :=
    div_nonneg (by positivity) (by linarith)
  have hy := (Analysis.densityY_spec _ hd).1
  exact ⟨XR_nonneg_interior _ hy,
    XR_strictMonoOn.monotoneOn hy.2.le (by simp) hy.2.le⟩

lemma primitive_density_shift_tendsto_finite (n : ℕ → ℕ)
    (hn : ∀ᶠ g in atTop,1 ≤ n g) (l : ℝ)
    (hl : Tendsto (fun g:ℕ => (n g:ℝ)/g) atTop (𝓝 l)) :
    Tendsto (fun g:ℕ => 2*((n g-1:ℕ):ℝ)/(2*(g:ℝ)-1)) atTop (𝓝 l) := by
  have ht := (hl.sub (tendsto_const_div_atTop_nhds_zero_nat (1:ℝ))).mul
    primitive_genus_scale_tendsto_one
  simp only [sub_zero,mul_one] at ht
  apply ht.congr'
  filter_upwards [hn,eventually_ge_atTop (1:ℕ)] with g hng hg
  exact (primitive_density_shift_identity g (n g) hg hng).symm

lemma primitive_density_shift_tendsto_top (n : ℕ → ℕ)
    (hn : ∀ᶠ g in atTop,1 ≤ n g)
    (hl : Tendsto (fun g:ℕ => (n g:ℝ)/g) atTop atTop) :
    Tendsto (fun g:ℕ => 2*((n g-1:ℕ):ℝ)/(2*(g:ℝ)-1)) atTop atTop := by
  have hd : Tendsto (fun g:ℕ => (n g:ℝ)/g-1/(g:ℝ)) atTop atTop := by
    apply tendsto_atTop_mono' atTop _ (tendsto_atTop_add_const_right _ (-1:ℝ) hl)
    filter_upwards [eventually_ge_atTop (1:ℕ)] with g hg
    have hgr : (1:ℝ) ≤ g := by exact_mod_cast hg
    have hi : 1/(g:ℝ) ≤ 1 := (div_le_one (by linarith : (0:ℝ)<g)).mpr hgr
    linarith
  have ht := primitive_genus_scale_tendsto_one.pos_mul_atTop (by norm_num : (0:ℝ)<1) hd
  apply ht.congr'
  filter_upwards [hn,eventually_ge_atTop (1:ℕ)] with g hng hg
  rw [primitive_density_shift_identity g (n g) hg hng,mul_comm]

theorem primitive_saddle_tendsto_density (n : ℕ → ℕ)
    (hn : ∀ᶠ g in atTop,1 ≤ n g) (l : ℝ≥0∞)
    (hl : Tendsto (fun g:ℕ => ENNReal.ofReal ((n g:ℝ)/g)) atTop (𝓝 l)) :
    Tendsto (fun g => primitiveSaddleX g (n g)) atTop (𝓝 (planarDensitySaddle l)) := by
  by_cases htop : l = ∞
  · subst l
    have hreal := ENNReal.tendsto_ofReal_nhds_top.mp hl
    have hd := Analysis.densityY_tendsto_critical.comp (primitive_density_shift_tendsto_top n hn hreal)
    simpa only [primitiveSaddleX,planar_density_saddle_top,xCritical,Function.comp_def] using
      XR_continuous.continuousAt.tendsto.comp (hd.mono_right nhdsWithin_le_nhds)
  · have hreal : Tendsto (fun g:ℕ => (n g:ℝ)/g) atTop (𝓝 l.toReal) := by
      have ht := (ENNReal.tendsto_toReal htop).comp hl
      apply ht.congr'
      exact Eventually.of_forall (fun g => ENNReal.toReal_ofReal (by positivity : 0 ≤ (n g:ℝ)/(g:ℝ)))
    have hs := primitive_density_shift_tendsto_finite n hn l.toReal hreal
    have hd : Tendsto (fun g:ℕ => densityY (2*((n g-1:ℕ):ℝ)/(2*(g:ℝ)-1)))
        atTop (𝓝 (densityY l.toReal)) := by
      apply (Analysis.chain_densityY_continuousOn _ ENNReal.toReal_nonneg).tendsto.comp
        (tendsto_nhdsWithin_iff.mpr ⟨hs,?_⟩)
      filter_upwards [eventually_ge_atTop (1:ℕ)] with g hg
      change 0 ≤ 2*((n g-1:ℕ):ℝ)/(2*(g:ℝ)-1)
      have hgR : (1:ℝ) ≤ g := by exact_mod_cast hg
      exact div_nonneg (by positivity) (by linarith)
    simpa only [primitiveSaddleX,planar_density_saddle_finite l htop,Function.comp_def] using
      XR_continuous.continuousAt.tendsto.comp hd

theorem primitive_saddle_tendsto_density_fast (n : ℕ → ℕ)
    (hn : Tendsto (fun g:ℕ => (n g:ℝ)/Real.sqrt g) atTop atTop) (l : ℝ≥0∞)
    (hl : Tendsto (fun g:ℕ => ENNReal.ofReal ((n g:ℝ)/g)) atTop (𝓝 l)) :
    Tendsto (fun g => primitiveSaddleX g (n g)) atTop (𝓝 (planarDensitySaddle l)) := by
  apply primitive_saddle_tendsto_density n _ l hl
  filter_upwards [Spectral.fast_cusps_eventually_two n hn] with g hg
  omega

end WP.RandomGeometry
