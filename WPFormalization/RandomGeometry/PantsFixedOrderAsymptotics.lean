import WPFormalization.RandomGeometry.PantsMomentAsymptotics
import Mathlib.Analysis.SpecialFunctions.Choose

/-! Fixed arbitrary order of the actual zero-boundary pants cut expression.
All cusp counts are allowed relative to genus; only n→∞ is required. The
original all-cusp Theorem 1.3 and its actual adjacent profile shifts supply the
finite product of inverse cusp ratios. -/
noncomputable section
namespace WP.RandomGeometry
open Filter Asymptotics
open scoped Topology

/-- The exact zero-boundary ordered r-pants cut expression. -/
def pantsFixedOrderBase (P : PsiTheory) (g n r : ℕ) (L : ℝ) : ℝ :=
  ((n.descFactorial (2*r) : ℝ)/((2:ℝ)^r*volumeModel P g n))*
    volumeModel P g (n-r)*(L^2/2)^r

lemma pants_fixed_profile_shift (r : ℕ) (n : ℕ → ℕ) (hn : Tendsto n atTop atTop) :
    Tendsto (fun g => profileC (((n g-r:ℕ):ℝ)/g)/profileC ((n g:ℝ)/g))
      atTop (𝓝 1) := by
  induction r with
  | zero =>
    convert tendsto_const_nhds (x := (1:ℝ)) using 1
    funext g
    simp only [Nat.sub_zero]
    exact div_self (Analysis.volume_profile_C_pos _ (by positivity)).ne'
  | succ r ih =>
    have ha := pants_adjacent_profile_tendsto_one (fun g => n g-r) (by
      filter_upwards [hn.eventually_ge_atTop (r+1)] with g hg
      omega)
    have ht := ha.mul ih
    simp only [one_mul] at ht
    apply ht.congr'
    filter_upwards [] with g
    rw [show n g-r-1=n g-(r+1) by omega]
    exact div_mul_div_cancel₀ (Analysis.volume_profile_C_pos _ (by positivity)).ne'

lemma pants_fixed_inverse_cusp_step (P : PsiTheory) (r : ℕ)
    (n : ℕ → ℕ) (hn : Tendsto n atTop atTop) :
    Tendsto (fun g => (2*g*profileC ((n g:ℝ)/g))*
      volumeModel P g (n g-(r+1))/volumeModel P g (n g-r)) atTop (𝓝 1) := by
  have hc := pants_cusp_ratio_tendsto_one P (fun g => n g-(r+1))
  have hp := pants_fixed_profile_shift (r+1) n hn
  have ht := (hc.mul hp).inv₀ (by norm_num : (1:ℝ)*1 ≠ 0)
  simp only [one_mul,inv_one] at ht
  apply ht.congr'
  filter_upwards [hn.eventually_ge_atTop (r+2),eventually_ge_atTop (1:ℕ)] with g hng hg
  have hindex : n g-(r+1)+1=n g-r := by omega
  rw [hindex]
  have hg0 : (g:ℝ) ≠ 0 := by exact_mod_cast (show g ≠ 0 by omega)
  have hC : profileC ((n g:ℝ)/g) ≠ 0 :=
    (Analysis.volume_profile_C_pos _ (by positivity)).ne'
  have hC' : profileC (((n g-(r+1):ℕ):ℝ)/g) ≠ 0 :=
    (Analysis.volume_profile_C_pos _ (by positivity)).ne'
  have hv : volumeModel P g (n g-r) ≠ 0 :=
    (diagonal_volume_pos_nonempty P g _ (by omega) (by unfold Stable;omega)).ne'
  have hv' : volumeModel P g (n g-(r+1)) ≠ 0 :=
    (diagonal_volume_pos_nonempty P g _ (by omega) (by unfold Stable;omega)).ne'
  field_simp

lemma pants_fixed_volume_ratio (P : PsiTheory) (r : ℕ)
    (n : ℕ → ℕ) (hn : Tendsto n atTop atTop) :
    Tendsto (fun g => (2*g*profileC ((n g:ℝ)/g))^r*
      volumeModel P g (n g-r)/volumeModel P g (n g)) atTop (𝓝 1) := by
  induction r with
  | zero =>
    apply tendsto_const_nhds.congr'
    filter_upwards [hn.eventually_ge_atTop 1,eventually_ge_atTop (1:ℕ)] with g hng hg
    have hv : volumeModel P g (n g) ≠ 0 :=
      (diagonal_volume_pos_nonempty P g _ hng (by unfold Stable;omega)).ne'
    simp [hv]
  | succ r ih =>
    have ht := (pants_fixed_inverse_cusp_step P r n hn).mul ih
    simp only [one_mul] at ht
    apply ht.congr'
    filter_upwards [hn.eventually_ge_atTop (r+1),eventually_ge_atTop (1:ℕ)] with g hng hg
    have hv : volumeModel P g (n g-r) ≠ 0 :=
      (diagonal_volume_pos_nonempty P g _ (by omega) (by unfold Stable;omega)).ne'
    rw [pow_succ]
    field_simp
    <;> ring

lemma pants_fixed_descFactorial_limit (k : ℕ) (n : ℕ → ℕ) (hn : Tendsto n atTop atTop) :
    Tendsto (fun g => ((n g).descFactorial k : ℝ)/(n g:ℝ)^k) atTop (𝓝 1) := by
  have hz : ∀ᶠ N : ℕ in atTop, (N:ℝ)^k ≠ 0 := by
    filter_upwards [eventually_ge_atTop (1:ℕ)] with N hN
    exact pow_ne_zero _ (by exact_mod_cast (show N ≠ 0 by omega))
  exact ((isEquivalent_iff_tendsto_one hz).mp (isEquivalent_descFactorial k)).comp hn

lemma pants_fixed_label_ratio (r : ℕ) (n : ℕ → ℕ) (hn : Tendsto n atTop atTop) :
    Tendsto (fun g => ((n g).descFactorial (2*r) : ℝ)/
      ((n g:ℝ)*(n g-1))^r) atTop (𝓝 1) := by
  have ht := (pants_fixed_descFactorial_limit (2*r) n hn).div
    ((pants_fixed_descFactorial_limit 2 n hn).pow r) (by simp : (1:ℝ)^r ≠ 0)
  simp only [one_pow,div_one] at ht
  apply ht.congr'
  filter_upwards [hn.eventually_ge_atTop 2] with g hng
  have hn0 : (n g:ℝ) ≠ 0 := by exact_mod_cast (show n g ≠ 0 by omega)
  have hn1 : (n g:ℝ)-1 ≠ 0 := by
    have : (2:ℝ) ≤ n g := by exact_mod_cast hng
    linarith
  have htwo : ((n g).descFactorial 2 : ℝ)=(n g:ℝ)*((n g:ℝ)-1) := by
    simp only [show (2:ℕ)=1+1 by rfl,Nat.descFactorial_succ,Nat.descFactorial_zero,
      Nat.mul_one,Nat.sub_zero,Nat.cast_mul,Nat.cast_sub (show 1 ≤ n g by omega),Nat.cast_one]
    ring
  change ((n g).descFactorial (2*r) : ℝ)/(n g:ℝ)^(2*r) /
    (((n g).descFactorial 2 : ℝ)/(n g:ℝ)^2)^r = _
  rw [htwo,div_pow,←pow_mul]
  field_simp

lemma pants_fixed_base_scale_identity (P : PsiTheory) (g n r : ℕ) (L : ℝ)
    (hg : 1 ≤ g) (hn : 2 ≤ n) (hL : L ≠ 0) :
    pantsFixedOrderBase P g n r L/(pantsScale g n*L^2)^r =
      ((n.descFactorial (2*r) : ℝ)/((n:ℝ)*(n-1))^r)*
        ((2*g*profileC ((n:ℝ)/g))^r*volumeModel P g (n-r)/volumeModel P g n) := by
  have hg0 : (g:ℝ) ≠ 0 := by exact_mod_cast (show g ≠ 0 by omega)
  have hn0 : (n:ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hn1 : (n:ℝ)-1 ≠ 0 := by
    have : (2:ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hC : profileC ((n:ℝ)/g) ≠ 0 :=
    (Analysis.volume_profile_C_pos _ (by positivity)).ne'
  have hv : volumeModel P g n ≠ 0 :=
    (diagonal_volume_pos_nonempty P g n (by omega) (by unfold Stable;omega)).ne'
  unfold pantsFixedOrderBase pantsScale
  simp only [mul_pow,div_pow]
  have he : (8:ℝ)^r=(2:ℝ)^r*((2:ℝ)^r*(2:ℝ)^r) := by
    rw [←mul_pow,←mul_pow]
    norm_num
  rw [he]
  field_simp
  <;> ring

lemma pants_fixed_order_zero (P : PsiTheory) (g n : ℕ) (L : ℝ)
    (hg : 1 ≤ g) (hn : 1 ≤ n) : pantsFixedOrderBase P g n 0 L=1 := by
  have hv : volumeModel P g n ≠ 0 :=
    (diagonal_volume_pos_nonempty P g n hn (by unfold Stable;omega)).ne'
  simp [pantsFixedOrderBase,hv]

/-- Every fixed factorial order has the original physical q_g L² scale,
without any restriction on n/g. The r=0 case is included. -/
lemma pants_fixed_order_base_asymptotic (P : PsiTheory) (r : ℕ)
    (n : ℕ → ℕ) (L : ℕ → ℝ) (hn : Tendsto n atTop atTop)
    (hL : ∀ᶠ g in atTop, L g ≠ 0) :
    Tendsto (fun g => pantsFixedOrderBase P g (n g) r (L g)/
      (pantsScale g (n g)*(L g)^2)^r) atTop (𝓝 1) := by
  have ht := (pants_fixed_label_ratio r n hn).mul (pants_fixed_volume_ratio P r n hn)
  simp only [one_mul] at ht
  apply ht.congr'
  filter_upwards [hn.eventually_ge_atTop 2,hL,eventually_ge_atTop (1:ℕ)] with g hng hLg hg
  exact (pants_fixed_base_scale_identity P g (n g) r (L g) hg hng hLg).symm

end WP.RandomGeometry
