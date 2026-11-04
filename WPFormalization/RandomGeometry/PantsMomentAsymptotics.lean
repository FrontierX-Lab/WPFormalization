import WPFormalization.Statements.VolumeRatios
import WPFormalization.Analysis.VolumeProfileShifts
import WPFormalization.Statements.Intensities
import WPFormalization.Volumes.DiagonalChainAlgebra
import WPFormalization.RandomGeometry.PantsMomentComparison

/-! The actual cusp-cut volume expressions for the first two ordered factorial
moments. All asymptotics below are proved from Theorem 1.3 and the original
profile C; no moment or integration identity is an assumption of this module. -/
noncomputable section
namespace WP.RandomGeometry
open Filter
open scoped Topology

/-- The zero-boundary first-moment integral, including the unordered cusp pair. -/
def pantsFirstBase (P : PsiTheory) (g n : ℕ) (L : ℝ) : ℝ :=
  (n:ℝ)*(n-1)*L^2/4*(volumeModel P g (n-1)/volumeModel P g n)

/-- The zero-boundary second factorial moment: four distinct ordered cusps,
with precisely the factor 2² from the two unordered cusp pairs. -/
def pantsSecondBase (P : PsiTheory) (g n : ℕ) (L : ℝ) : ℝ :=
  (n:ℝ)*(n-1)*(n-2)*(n-3)*L^4/16*
    (volumeModel P g (n-2)/volumeModel P g n)

lemma pants_limit_one_of_inverse_genus_bound (f : ℕ → ℝ) (C : ℝ)
    (hf : ∀ᶠ g in atTop, |f g-1| ≤ C/g) :
    Tendsto f atTop (𝓝 1) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simp only [Real.norm_eq_abs]
  exact squeeze_zero' (Eventually.of_forall (fun g => abs_nonneg _)) hf
    (tendsto_const_div_atTop_nhds_zero_nat C)

lemma pants_cusp_ratio_tendsto_one (P : PsiTheory) (n : ℕ → ℕ) :
    Tendsto (fun g =>
      (volumeModel P g (n g+1)/(2*g*volumeModel P g (n g)))/
        profileC ((n g:ℝ)/g)) atTop (𝓝 1) := by
  obtain ⟨C,hC,G,hG⟩ := volume_ratios P
  apply pants_limit_one_of_inverse_genus_bound _ C
  filter_upwards [eventually_ge_atTop G] with g hg
  exact ((hG g hg).1 (n g)).2

lemma pants_adjacent_profile_tendsto_one (n : ℕ → ℕ)
    (hn : ∀ᶠ g in atTop, 1 ≤ n g) :
    Tendsto (fun g => profileC (((n g-1:ℕ):ℝ)/g)/
      profileC ((n g:ℝ)/g)) atTop (𝓝 1) := by
  apply pants_limit_one_of_inverse_genus_bound _ 2
  filter_upwards [hn,eventually_ge_atTop (1:ℕ)] with g hng hg
  simpa only [Nat.cast_sub hng,Nat.cast_one] using
    Analysis.volume_profile_C_adjacent_rate g (n g) hg hng

lemma pants_D_tendsto_one (P : PsiTheory) (n : ℕ → ℕ)
    (hn : ∀ᶠ g in atTop, 1 ≤ n g) :
    Tendsto (fun g => volumeModel P g (n g)^2/
      (volumeModel P g (n g-1)*volumeModel P g (n g+1))) atTop (𝓝 1) := by
  obtain ⟨C,hC,G,hG⟩ := volume_ratios P
  apply pants_limit_one_of_inverse_genus_bound _ C
  filter_upwards [hn,eventually_ge_atTop G] with g hng hg
  exact (hG g hg).2 (n g) hng

lemma pantsFirstBase_scale_identity (P : PsiTheory) (g n : ℕ) (L : ℝ)
    (hg : 1 ≤ g) (hn : 2 ≤ n) (hL : L ≠ 0) :
    pantsFirstBase P g n L/(pantsScale g n*L^2) =
      ((volumeModel P g n/(2*g*volumeModel P g (n-1)))/
        profileC (((n-1:ℕ):ℝ)/g) *
        (profileC (((n-1:ℕ):ℝ)/g)/profileC ((n:ℝ)/g)))⁻¹ := by
  have hgR : (g:ℝ) ≠ 0 := by exact_mod_cast (show g ≠ 0 by omega)
  have hnR : (n:ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hn1 : (n:ℝ)-1 ≠ 0 := by
    have : (2:ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hc : profileC ((n:ℝ)/g) ≠ 0 :=
    (Analysis.volume_profile_C_pos _ (by positivity)).ne'
  have hc' : profileC (((n-1:ℕ):ℝ)/g) ≠ 0 :=
    (Analysis.volume_profile_C_pos _ (by positivity)).ne'
  have hv : volumeModel P g n ≠ 0 :=
    (diagonal_volume_pos_nonempty P g n (by omega) (by unfold Stable;omega)).ne'
  have hv' : volumeModel P g (n-1) ≠ 0 :=
    (diagonal_volume_pos_nonempty P g (n-1) (by omega) (by unfold Stable;omega)).ne'
  unfold pantsFirstBase pantsScale
  field_simp
  <;> ring

lemma pants_first_base_asymptotic (P : PsiTheory) (n : ℕ → ℕ) (L : ℕ → ℝ)
    (hn : Tendsto n atTop atTop) (hL : ∀ᶠ g in atTop, L g ≠ 0) :
    Tendsto (fun g => pantsFirstBase P g (n g) (L g)/
      (pantsScale g (n g)*(L g)^2)) atTop (𝓝 1) := by
  have hc := pants_cusp_ratio_tendsto_one P (fun g => n g-1)
  have hp := pants_adjacent_profile_tendsto_one n (hn.eventually_ge_atTop 1)
  have ht := (hc.mul hp).inv₀ (by norm_num : (1:ℝ)*1 ≠ 0)
  simp only [one_mul,inv_one] at ht
  apply ht.congr'
  filter_upwards [hn.eventually_ge_atTop 2,hL,eventually_ge_atTop (1:ℕ)] with g hng hLg hg
  rw [show n g-1+1=n g by omega]
  exact (pantsFirstBase_scale_identity P g (n g) (L g) hg hng hLg).symm

lemma pants_second_first_base_identity (P : PsiTheory) (g n : ℕ) (L : ℝ)
    (hg : 1 ≤ g) (hn : 4 ≤ n) (hL : L ≠ 0) :
    pantsSecondBase P g n L/(pantsFirstBase P g n L)^2 =
      (((n:ℝ)-2)*(n-3)/((n:ℝ)*(n-1)))/
        (volumeModel P g (n-1)^2/
          (volumeModel P g ((n-1)-1)*volumeModel P g ((n-1)+1))) := by
  have hn0 : (n:ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hn1 : (n:ℝ)-1 ≠ 0 := by
    have : (4:ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hv : volumeModel P g n ≠ 0 :=
    (diagonal_volume_pos_nonempty P g n (by omega) (by unfold Stable;omega)).ne'
  have hv1 : volumeModel P g (n-1) ≠ 0 :=
    (diagonal_volume_pos_nonempty P g (n-1) (by omega) (by unfold Stable;omega)).ne'
  have hv2 : volumeModel P g (n-2) ≠ 0 :=
    (diagonal_volume_pos_nonempty P g (n-2) (by omega) (by unfold Stable;omega)).ne'
  rw [show n-1-1=n-2 by omega,show n-1+1=n by omega]
  exact two_pants_base_relative n L _ _ _ hn0 hn1 hL hv hv1 hv2

lemma pants_second_first_base_asymptotic (P : PsiTheory) (n : ℕ → ℕ) (L : ℕ → ℝ)
    (hn : Tendsto n atTop atTop) (hL : ∀ᶠ g in atTop, L g ≠ 0) :
    Tendsto (fun g => pantsSecondBase P g (n g) (L g)/
      (pantsFirstBase P g (n g) (L g))^2) atTop (𝓝 1) := by
  have hn' : Tendsto (fun g => (n g:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hn
  have hd := pants_D_tendsto_one P (fun g => n g-1) (by
    filter_upwards [hn.eventually_ge_atTop 2] with g hng; omega)
  have ht := (label_pair_ratio_tendsto_one _ hn').div hd (by norm_num : (1:ℝ) ≠ 0)
  simp only [div_one] at ht
  apply ht.congr'
  filter_upwards [hn.eventually_ge_atTop 4,hL,eventually_ge_atTop (1:ℕ)] with g hng hLg hg
  exact (pants_second_first_base_identity P g (n g) (L g) hg hng hLg).symm

lemma pants_second_base_asymptotic (P : PsiTheory) (n : ℕ → ℕ) (L : ℕ → ℝ)
    (hn : Tendsto n atTop atTop) (hL : ∀ᶠ g in atTop, L g ≠ 0) :
    Tendsto (fun g => pantsSecondBase P g (n g) (L g)/
      (pantsScale g (n g)*(L g)^2)^2) atTop (𝓝 1) := by
  have hfirst := pants_first_base_asymptotic P n L hn hL
  have hsecond := pants_second_first_base_asymptotic P n L hn hL
  have ht := hsecond.mul (hfirst.pow 2)
  simp only [one_pow,mul_one] at ht
  apply ht.congr'
  filter_upwards [hn.eventually_ge_atTop 4,hL,eventually_ge_atTop (1:ℕ)] with g hng hLg hg
  have hn0 : (n g:ℝ) ≠ 0 := by exact_mod_cast (show n g ≠ 0 by omega)
  have hn1 : (n g:ℝ)-1 ≠ 0 := by
    have : (4:ℝ) ≤ n g := by exact_mod_cast hng
    linarith
  have hv : volumeModel P g (n g) ≠ 0 :=
    (diagonal_volume_pos_nonempty P g (n g) (by omega) (by unfold Stable;omega)).ne'
  have hv1 : volumeModel P g (n g-1) ≠ 0 :=
    (diagonal_volume_pos_nonempty P g (n g-1) (by omega) (by unfold Stable;omega)).ne'
  have hb : pantsFirstBase P g (n g) (L g) ≠ 0 := by
    unfold pantsFirstBase
    exact mul_ne_zero (div_ne_zero (mul_ne_zero (mul_ne_zero hn0 hn1) (pow_ne_zero 2 hLg))
      (by norm_num)) (div_ne_zero hv1 hv)
  rw [div_pow]
  field_simp

/-- Multiplicative comparison of a true integral with its zero-boundary base.
The hypotheses are proved at the integration site; this is an internal transfer
lemma, not an additional assumption on a geometric theory. -/
lemma pants_moment_comparison_transfer (M base scale L : ℕ → ℝ) (c : ℝ)
    (hbase : Tendsto (fun g => base g/scale g) atTop (𝓝 1))
    (hL : Tendsto L atTop (𝓝 0))
    (hbound : ∀ᶠ g in atTop,
      1 ≤ M g/base g ∧ M g/base g ≤ Real.exp (c*L g)) :
    Tendsto (fun g => M g/scale g) atTop (𝓝 1) := by
  have ht := (exponential_boundary_squeeze L (fun g => M g/base g) c hL hbound).mul hbase
  simp only [one_mul] at ht
  apply ht.congr'
  filter_upwards [hbase.eventually (lt_mem_nhds (by norm_num : (0:ℝ)<1))] with g hg
  have hb : base g ≠ 0 := by
    intro hzero
    simp [hzero] at hg
  exact div_mul_div_cancel₀ hb

end WP.RandomGeometry
