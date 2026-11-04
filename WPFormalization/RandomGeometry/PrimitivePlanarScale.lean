import WPFormalization.RandomGeometry.PrimitivePlanarTypeComparison
import WPFormalization.Analysis.VolumeProfileShifts
import WPFormalization.Spectral.PantsScaleGrowth
noncomputable section
namespace WP.RandomGeometry
open Set Filter
open scoped Topology

lemma primitive_planar_scale_identity (g n : ℕ) (hg : 1 ≤ g) (hn : 2 ≤ n) :
    primitivePlanarEffectiveScale g n/pantsScale g n =
      (2*(g:ℝ)/(2*g-1)) *
        (profileC ((n:ℝ)/g)/profileC (2*((n-1:ℕ):ℝ)/(2*g-1))) := by
  have hgr : (1:ℝ) ≤ g := by exact_mod_cast hg
  have hnr : (2:ℝ) ≤ n := by exact_mod_cast hn
  have hgp : (0:ℝ) < g := by linarith
  have hnp : (0:ℝ) < n := by linarith
  have hd : 0 < 2*(g:ℝ)-1 := by linarith
  have hnm : (0:ℝ) < n-1 := by linarith
  have hnc : ((n-1:ℕ):ℝ) = (n:ℝ)-1 := by rw [Nat.cast_sub (by omega : 1 ≤ n),Nat.cast_one]
  have hl : 0 < 2*((n-1:ℕ):ℝ)/(2*(g:ℝ)-1) := by rw [hnc]; positivity
  have hc := Analysis.volume_profile_C_pos _ hl.le
  have hcn := Analysis.volume_profile_C_pos ((n:ℝ)/g) (by positivity)
  have hxp : primitiveSaddleX g n ≠ 0 := by
    intro hz
    unfold primitiveSaddleX at hz
    simp only [profileC,if_neg (ne_of_gt hl),hz,div_zero] at hc
    exact (lt_irrefl (0:ℝ) hc)
  unfold primitivePlanarEffectiveScale pantsScale
  simp only [profileC,if_neg (ne_of_gt hl)]
  change (n:ℝ)*primitiveSaddleX g n/(4*(2*Real.pi^2)) /
      ((n:ℝ)*(n-1)/(8*g*profileC ((n:ℝ)/g))) =
    2*(g:ℝ)/(2*g-1) *
      (profileC ((n:ℝ)/g)/(2*((n-1:ℕ):ℝ)/(2*g-1)*Real.pi^2/primitiveSaddleX g n))
  rw [hnc]
  field_simp [hgp.ne',hnp.ne',hd.ne',hnm.ne',hxp,hcn.ne',Real.pi_ne_zero]
  <;> ring

lemma primitive_shifted_profile_tendsto_one (n : ℕ → ℕ)
    (hn : ∀ᶠ g in atTop, 1 ≤ n g) :
    Tendsto (fun g => profileC (2*((n g-1:ℕ):ℝ)/(2*g-1))/
      profileC ((n g:ℝ)/g)) atTop (𝓝 1) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simp only [Real.norm_eq_abs]
  apply squeeze_zero' (Eventually.of_forall (fun g => abs_nonneg _)) ?_
    (tendsto_const_div_atTop_nhds_zero_nat 4)
  filter_upwards [hn,eventually_ge_atTop (8:ℕ)] with g hng hg
  simpa only [Nat.cast_sub hng,Nat.cast_one] using
    Analysis.volume_profile_C_shift_rate g (n g) hg hng

lemma primitive_genus_scale_tendsto_one :
    Tendsto (fun g:ℕ => 2*(g:ℝ)/(2*g-1)) atTop (𝓝 1) := by
  have hzero := tendsto_const_div_atTop_nhds_zero_nat (1/2:ℝ)
  have hinv := (tendsto_const_nhds.sub hzero).inv₀ (by norm_num : (1:ℝ)-0 ≠ 0)
  simp only [sub_zero,inv_one] at hinv
  apply hinv.congr'
  filter_upwards [eventually_ge_atTop (1:ℕ)] with g hg
  have hgr : (1:ℝ) ≤ g := by exact_mod_cast hg
  have hgp : (g:ℝ) ≠ 0 := by linarith
  have hd : 2*(g:ℝ)-1 ≠ 0 := by linarith
  field_simp
  <;> ring

lemma primitive_planar_scale_ratio_tendsto_one (n : ℕ → ℕ)
    (hn : ∀ᶠ g in atTop, 2 ≤ n g) :
    Tendsto (fun g => primitivePlanarEffectiveScale g (n g)/pantsScale g (n g))
      atTop (𝓝 1) := by
  have hc := (primitive_shifted_profile_tendsto_one n (by
    filter_upwards [hn] with g hg; omega)).inv₀ (by norm_num : (1:ℝ) ≠ 0)
  simp only [inv_one] at hc
  have ht := primitive_genus_scale_tendsto_one.mul hc
  simp only [one_mul] at ht
  apply ht.congr'
  filter_upwards [hn,eventually_ge_atTop (1:ℕ)] with g hng hg
  simpa only [inv_div] using (primitive_planar_scale_identity g (n g) hg hng).symm

lemma primitive_planar_scale_tendsto_atTop (n : ℕ → ℕ)
    (hn : Tendsto (fun g:ℕ => (n g:ℝ)/Real.sqrt g) atTop atTop) :
    Tendsto (fun g => primitivePlanarEffectiveScale g (n g)) atTop atTop := by
  have hn2 := WP.Spectral.fast_cusps_eventually_two n hn
  have hratio := primitive_planar_scale_ratio_tendsto_one n hn2
  have hq := WP.Spectral.pantsScale_tendsto_atTop n hn
  have hmul := hratio.pos_mul_atTop (by norm_num : (0:ℝ) < 1) hq
  apply hmul.congr'
  filter_upwards [hn2,eventually_ge_atTop (1:ℕ)] with g hng hg
  have hgr : (0:ℝ) < g := by exact_mod_cast (show 0 < g by omega)
  have hnr : (2:ℝ) ≤ n g := by exact_mod_cast hng
  have hcp := Analysis.volume_profile_C_pos ((n g:ℝ)/g) (by positivity)
  have hqp : 0 < pantsScale g (n g) := by
    unfold pantsScale
    exact div_pos (mul_pos (by linarith) (by linarith)) (by positivity)
  exact div_mul_cancel₀ _ hqp.ne'

lemma primitive_planar_rescaled_length_tendsto_zero (n : ℕ → ℕ)
    (hn : Tendsto (fun g:ℕ => (n g:ℝ)/Real.sqrt g) atTop atTop) (T : ℝ) :
    Tendsto (fun g => T/Real.sqrt (primitivePlanarEffectiveScale g (n g)))
      atTop (𝓝 0) := by
  exact (Real.tendsto_sqrt_atTop.comp
    (primitive_planar_scale_tendsto_atTop n hn)).const_div_atTop T

end WP.RandomGeometry
