import WPFormalization.RandomGeometry.GeneralPlanarNonstarNumerics

/-! The explicit O(1/n) rate in (14.13), including vanishing saddle weight. -/
noncomputable section
namespace WP.RandomGeometry
open Filter
open scoped Topology

lemma planar_nonstar_power_ratio_le_inverse (r d : ℕ) (hd : d<r) (N : ℝ) (hN : 1≤N) :
    N^d/N^r≤1/N := by
  have hNp : 0<N := by linarith
  apply (div_le_div_iff₀ (pow_pos hNp _) hNp).mpr
  simpa only [one_mul,←pow_succ] using pow_le_pow_right₀ hN (show d+1≤r by omega)

theorem general_planar_nonstar_base_rate (P : PsiTheory) (r a d : ℕ)
    (hd : d<r) (ha : r+d≤a) (n : ℕ→ℕ) (hn : Tendsto n atTop atTop) (t : ℝ) :
    ∃C : ℝ,0<C ∧ ∀ᶠg : ℕ in atTop,
      0≤generalPlanarNonstarBase P g (n g) r a d t ∧
        generalPlanarNonstarBase P g (n g) r a d t≤C/(n g:ℝ) := by
  let B : ℝ := max 1 (xCritical/(2*Real.pi^2))
  let D : ℝ := B^(a-d-r)*(2*t^2)^r
  let C : ℝ := 2*D+1
  have hB : 0≤B := le_trans (by norm_num) (le_max_left _ _)
  have hD : 0≤D := by dsimp [D];positivity
  have hC : 0<C := by dsimp [C];linarith
  refine ⟨C,hC,?_⟩
  have hratio := (general_planar_fixed_volume_ratio P (a-d) n hn).eventually
    (gt_mem_nhds (by norm_num : (1:ℝ)<2))
  filter_upwards [eventually_ge_atTop (2:ℕ),hn.eventually_ge_atTop (max 2 (a+1)),hratio]
    with g hg hng hRg
  have hn2 : 2≤n g := (le_max_left _ _).trans hng
  have hna : a+1≤n g := (le_max_right _ _).trans hng
  have hN1 : (1:ℝ)≤n g := by exact_mod_cast (show 1≤n g by omega)
  have hNp : (0:ℝ)<n g := by linarith
  have hx := general_planar_saddle_mem g (n g) (by omega) hn2
  have hxp : 0<primitiveSaddleX g (n g) := hx.1
  have hv := diagonal_volume_pos_nonempty P g (n g) (by omega) (by unfold Stable;omega)
  have hvr := diagonal_volume_pos_nonempty P g (n g-a+d) (by omega) (by unfold Stable;omega)
  have hq : 0<primitivePlanarEffectiveScale g (n g) := by
    unfold primitivePlanarEffectiveScale
    positivity
  have hnonneg : 0≤generalPlanarNonstarBase P g (n g) r a d t := by
    unfold generalPlanarNonstarBase
    positivity
  refine ⟨hnonneg,?_⟩
  let R : ℝ := (2*Real.pi^2*(n g:ℝ)/primitiveSaddleX g (n g))^(a-d)*
    volumeModel P g (n g-(a-d))/volumeModel P g (n g)
  let W : ℝ := (n g:ℝ)^d/(n g:ℝ)^r*
    (primitiveSaddleX g (n g)/(2*Real.pi^2))^(a-d-r)*(2*t^2)^r
  have hR : R≤2 := hRg.le
  have hxB : primitiveSaddleX g (n g)/(2*Real.pi^2)≤B :=
    (div_le_div_of_nonneg_right hx.2.le (by positivity)).trans (le_max_right _ _)
  have hweight : (primitiveSaddleX g (n g)/(2*Real.pi^2))^(a-d-r)≤B^(a-d-r) :=
    pow_le_pow_left₀ (by positivity) hxB _
  have hW : W≤(1/(n g:ℝ))*D := by
    dsimp [W,D]
    have hrat := planar_nonstar_power_ratio_le_inverse r d hd (n g:ℝ) hN1
    have hm := mul_le_mul hrat hweight (by positivity) (by positivity)
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hm
      (show 0≤(2*t^2)^r by positivity)
  have hW0 : 0≤W := by dsimp [W];positivity
  have heq : generalPlanarNonstarBase P g (n g) r a d t=R*W := by
    have hshift : n g-a+d=n g-(a-d) := by omega
    unfold generalPlanarNonstarBase primitivePlanarEffectiveScale
    rw [hshift]
    exact general_planar_nonstar_algebra (n g:ℝ) (primitiveSaddleX g (n g))
      (2*Real.pi^2) (volumeModel P g (n g)) (volumeModel P g (n g-(a-d))) t r a d ha
      hNp.ne' hx.1.ne' (by positivity) hv.ne'
  calc
    _=R*W := heq
    _≤2*((1/(n g:ℝ))*D) := mul_le_mul hR hW hW0 (by norm_num)
    _=(2*D)/(n g:ℝ) := by ring
    _≤C/(n g:ℝ) := div_le_div_of_nonneg_right (by dsimp [C];linarith) hNp.le

end WP.RandomGeometry
