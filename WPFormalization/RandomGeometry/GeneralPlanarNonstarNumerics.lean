import WPFormalization.RandomGeometry.GeneralPlanarStarPrefactor

/-! The numerical decay mechanism in (14.13), retaining the nonnegative
power of the saddle even when the cusp density tends to zero. The geometric
classification and finite-pattern bound must be supplied by actual cut proofs. -/
noncomputable section
namespace WP.RandomGeometry
open Filter
open scoped Topology

lemma planar_nonstar_power_ratio_tendsto (r d : ℕ) (hd : d<r)
    (n : ℕ → ℕ) (hn : Tendsto n atTop atTop) :
    Tendsto (fun g => (n g:ℝ)^d/(n g:ℝ)^r) atTop (𝓝 0) := by
  have hN : Tendsto (fun g => (n g:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hn
  have ht := ((tendsto_inv_atTop_zero : Tendsto (fun x : ℝ => x⁻¹) atTop (𝓝 0)).comp hN).pow (r-d)
  rw [zero_pow (show r-d≠0 by omega)] at ht
  apply ht.congr'
  filter_upwards [hn.eventually_ge_atTop 1] with g hg
  have hN0 : (n g:ℝ)≠0 := by exact_mod_cast (show n g≠0 by omega)
  have he : r=d+(r-d) := by omega
  change ((n g:ℝ)⁻¹)^(r-d)=(n g:ℝ)^d/(n g:ℝ)^r
  rw [inv_pow]
  conv_rhs => rw [he,pow_add]
  field_simp

lemma general_planar_nonstar_algebra (N x B V U T : ℝ) (r a d : ℕ)
    (ha : r+d≤a) (hN : N≠0) (hx : x≠0) (hB : B≠0) (hV : V≠0) :
    N^a*U/V*(T^2/(2*(N*x/(4*B))))^r =
      ((B*N/x)^(a-d)*U/V)*(N^d/N^r*(x/B)^(a-d-r)*(2*T^2)^r) := by
  generalize he : a-d-r=e
  have h1 : a-d=e+r := by omega
  have h2 : a=e+r+d := by omega
  rw [h1,h2]
  simp only [mul_pow,div_pow,pow_add,pow_mul]
  field_simp
  simp only [show (4:ℝ)=2^2 by norm_num,←pow_mul,Nat.mul_comm]

def generalPlanarNonstarBase (P : PsiTheory) (g n r a d : ℕ) (T : ℝ) : ℝ :=
  (n:ℝ)^a * volumeModel P g (n-a+d)/volumeModel P g n *
    (T^2/(2*primitivePlanarEffectiveScale g n))^r

lemma general_planar_nonstar_moving_weight_tendsto (r a d : ℕ)
    (hd : d<r) (ha : r+d≤a) (n : ℕ → ℕ) (hn : Tendsto n atTop atTop) (T : ℝ) :
    Tendsto (fun g => (n g:ℝ)^d/(n g:ℝ)^r *
      (primitiveSaddleX g (n g)/(2*Real.pi^2))^(a-d-r)*(2*T^2)^r) atTop (𝓝 0) := by
  let B : ℝ := max 1 (xCritical/(2*Real.pi^2))
  have hB : 0≤B := le_trans (by norm_num) (le_max_left _ _)
  have hlim := (planar_nonstar_power_ratio_tendsto r d hd n hn).mul_const
    (B^(a-d-r)*(2*T^2)^r)
  simp only [zero_mul] at hlim
  apply squeeze_zero' _ _ hlim
  · filter_upwards [eventually_ge_atTop (1:ℕ),hn.eventually_ge_atTop 2] with g hg hng
    have hx := general_planar_saddle_mem g (n g) hg hng
    have hx0 := hx.1.le
    positivity
  · filter_upwards [eventually_ge_atTop (1:ℕ),hn.eventually_ge_atTop 2] with g hg hng
    have hx := general_planar_saddle_mem g (n g) hg hng
    have hquot : primitiveSaddleX g (n g)/(2*Real.pi^2)≤B := by
      exact (div_le_div_of_nonneg_right hx.2.le (by positivity)).trans (le_max_right _ _)
    have hx0 := hx.1.le
    have hpow := pow_le_pow_left₀ (by positivity : 0≤primitiveSaddleX g (n g)/(2*Real.pi^2)) hquot (a-d-r)
    nlinarith [mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hpow (show 0≤(n g:ℝ)^d/(n g:ℝ)^r by positivity))
      (show 0≤(2*T^2)^r by positivity)]

lemma general_planar_nonstar_base_tendsto_zero (P : PsiTheory) (r a d : ℕ)
    (hd : d<r) (ha : r+d≤a) (n : ℕ → ℕ) (hn : Tendsto n atTop atTop) (T : ℝ) :
    Tendsto (fun g => generalPlanarNonstarBase P g (n g) r a d T) atTop (𝓝 0) := by
  have ht := (general_planar_fixed_volume_ratio P (a-d) n hn).mul
    (general_planar_nonstar_moving_weight_tendsto r a d hd ha n hn T)
  simp only [one_mul] at ht
  apply ht.congr'
  filter_upwards [eventually_ge_atTop (1:ℕ),hn.eventually_ge_atTop (max 2 a)] with g hg hng
  have hn2 : 2≤n g := (le_max_left _ _).trans hng
  have hna : a≤n g := (le_max_right _ _).trans hng
  have hx := general_planar_saddle_mem g (n g) hg hn2
  have hV := (diagonal_volume_pos_nonempty P g (n g) (by omega) (by unfold Stable;omega)).ne'
  have hnR : (n g:ℝ)≠0 := by exact_mod_cast (show n g≠0 by omega)
  have hshift : n g-a+d=n g-(a-d) := by omega
  unfold generalPlanarNonstarBase primitivePlanarEffectiveScale
  rw [hshift]
  exact (general_planar_nonstar_algebra (n g:ℝ) (primitiveSaddleX g (n g))
    (2*Real.pi^2) (volumeModel P g (n g)) (volumeModel P g (n g-(a-d))) T r a d ha
    hnR hx.1.ne' (by positivity) hV).symm
end WP.RandomGeometry
