import WPFormalization.RandomGeometry.PantsMomentAsymptoticsIntegrals

/-! The physical one- and two-pants cut-volume integrals, with the exact
ordered-cusp coefficients from (14.6). Invalid cusp counts contribute zero,
as do their falling factorials. These are numerical integrals of the actual
boundary polynomial, not definitions of geometric expectations. -/
noncomputable section
namespace WP.RandomGeometry
open Filter
open scoped Topology

def pantsFirstCutIntegral (P : PsiTheory) (g n : ℕ) (L : ℝ) : ℝ :=
  if hn : 2 ≤ n then
    ((n:ℝ)*(n-1)/(2*volumeModel P g n))*
      weightedBoxIntegral P g (n-1) 1 (by omega) L
  else 0

def pantsSecondCutIntegral (P : PsiTheory) (g n : ℕ) (L : ℝ) : ℝ :=
  if hn : 4 ≤ n then
    ((n:ℝ)*(n-1)*(n-2)*(n-3)/(4*volumeModel P g n))*
      weightedBoxIntegral P g (n-2) 2 (by omega) L
  else 0

lemma pants_first_cut_bounds (P : PsiTheory) (g n : ℕ) (L : ℝ)
    (hg : 1 ≤ g) (hn : 2 ≤ n) (hL : 0 ≤ L) :
    pantsFirstBase P g n L ≤ pantsFirstCutIntegral P g n L ∧
      pantsFirstCutIntegral P g n L ≤ Real.exp (L/2)*pantsFirstBase P g n L := by
  have hv : 0 < volumeModel P g n :=
    diagonal_volume_pos_nonempty P g n (by omega) (by unfold Stable;omega)
  have hnR : (2:ℝ) ≤ n := by exact_mod_cast hn
  have ha : 0 ≤ (n:ℝ)*(n-1)/(2*volumeModel P g n) :=
    div_nonneg (mul_nonneg (by positivity) (by linarith)) (by positivity)
  have hb := weightedBoxIntegral_bounds P g (n-1) 1 (by omega) hg (by omega) L hL
  simp only [Nat.cast_one,one_mul,pow_one] at hb
  rw [pantsFirstCutIntegral,dif_pos hn]
  constructor
  · convert mul_le_mul_of_nonneg_left hb.1 ha using 1 <;> unfold pantsFirstBase <;> ring
  · convert mul_le_mul_of_nonneg_left hb.2 ha using 1 <;> unfold pantsFirstBase <;> ring

lemma pants_second_cut_bounds (P : PsiTheory) (g n : ℕ) (L : ℝ)
    (hg : 1 ≤ g) (hn : 4 ≤ n) (hL : 0 ≤ L) :
    pantsSecondBase P g n L ≤ pantsSecondCutIntegral P g n L ∧
      pantsSecondCutIntegral P g n L ≤ Real.exp L*pantsSecondBase P g n L := by
  have hv : 0 < volumeModel P g n :=
    diagonal_volume_pos_nonempty P g n (by omega) (by unfold Stable;omega)
  have hnR : (4:ℝ) ≤ n := by exact_mod_cast hn
  have ha : 0 ≤ (n:ℝ)*(n-1)*(n-2)*(n-3)/(4*volumeModel P g n) :=
    div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by positivity) (by linarith))
      (by linarith)) (by linarith)) (by positivity)
  have hb := weightedBoxIntegral_bounds P g (n-2) 2 (by omega) hg (by omega) L hL
  have he : (2:ℝ)*L/2=L := by ring
  simp only [Nat.cast_ofNat,he] at hb
  rw [pantsSecondCutIntegral,dif_pos hn]
  constructor
  · convert mul_le_mul_of_nonneg_left hb.1 ha using 1 <;> unfold pantsSecondBase <;> ring
  · convert mul_le_mul_of_nonneg_left hb.2 ha using 1 <;> unfold pantsSecondBase <;> ring

lemma pants_first_base_pos (P : PsiTheory) (g n : ℕ) (L : ℝ)
    (hg : 1 ≤ g) (hn : 2 ≤ n) (hL : L ≠ 0) : 0 < pantsFirstBase P g n L := by
  have hv : 0 < volumeModel P g n :=
    diagonal_volume_pos_nonempty P g n (by omega) (by unfold Stable;omega)
  have hv' : 0 < volumeModel P g (n-1) :=
    diagonal_volume_pos_nonempty P g (n-1) (by omega) (by unfold Stable;omega)
  have hnR : (2:ℝ) ≤ n := by exact_mod_cast hn
  unfold pantsFirstBase
  exact mul_pos (div_pos (mul_pos (mul_pos (by linarith) (by linarith)) (sq_pos_of_ne_zero hL))
    (by norm_num)) (div_pos hv' hv)

lemma pants_second_base_pos (P : PsiTheory) (g n : ℕ) (L : ℝ)
    (hg : 1 ≤ g) (hn : 4 ≤ n) (hL : L ≠ 0) : 0 < pantsSecondBase P g n L := by
  have hv : 0 < volumeModel P g n :=
    diagonal_volume_pos_nonempty P g n (by omega) (by unfold Stable;omega)
  have hv' : 0 < volumeModel P g (n-2) :=
    diagonal_volume_pos_nonempty P g (n-2) (by omega) (by unfold Stable;omega)
  have hnR : (4:ℝ) ≤ n := by exact_mod_cast hn
  unfold pantsSecondBase
  have hp : 0 < L^4 := pow_pos (sq_pos_of_ne_zero hL) 2 |>.trans_eq (by ring)
  exact mul_pos (div_pos (mul_pos (mul_pos (mul_pos (mul_pos (by linarith) (by linarith))
    (by linarith)) (by linarith)) hp) (by norm_num)) (div_pos hv' hv)

lemma pants_first_cut_asymptotic (P : PsiTheory) (n : ℕ → ℕ) (L : ℕ → ℝ)
    (hn : Tendsto n atTop atTop) (hL0 : ∀ᶠ g in atTop, 0 ≤ L g)
    (hLne : ∀ᶠ g in atTop, L g ≠ 0) (hL : Tendsto L atTop (𝓝 0)) :
    Tendsto (fun g => pantsFirstCutIntegral P g (n g) (L g)/
      (pantsScale g (n g)*(L g)^2)) atTop (𝓝 1) := by
  apply pants_moment_comparison_transfer _ (fun g => pantsFirstBase P g (n g) (L g)) _ L (1/2)
    (pants_first_base_asymptotic P n L hn hLne) hL
  filter_upwards [hn.eventually_ge_atTop 2,hL0,hLne,eventually_ge_atTop (1:ℕ)] with g hng hLg hLneg hg
  have hb := pants_first_cut_bounds P g (n g) (L g) hg hng hLg
  have hp := pants_first_base_pos P g (n g) (L g) hg hng hLneg
  constructor
  · exact (le_div_iff₀ hp).2 (by simpa using hb.1)
  · apply (div_le_iff₀ hp).2
    convert hb.2 using 1 <;> congr 2 <;> ring

lemma pants_second_cut_asymptotic (P : PsiTheory) (n : ℕ → ℕ) (L : ℕ → ℝ)
    (hn : Tendsto n atTop atTop) (hL0 : ∀ᶠ g in atTop, 0 ≤ L g)
    (hLne : ∀ᶠ g in atTop, L g ≠ 0) (hL : Tendsto L atTop (𝓝 0)) :
    Tendsto (fun g => pantsSecondCutIntegral P g (n g) (L g)/
      (pantsScale g (n g)*(L g)^2)^2) atTop (𝓝 1) := by
  apply pants_moment_comparison_transfer _ (fun g => pantsSecondBase P g (n g) (L g)) _ L 1
    (pants_second_base_asymptotic P n L hn hLne) hL
  filter_upwards [hn.eventually_ge_atTop 4,hL0,hLne,eventually_ge_atTop (1:ℕ)] with g hng hLg hLneg hg
  have hb := pants_second_cut_bounds P g (n g) (L g) hg hng hLg
  have hp := pants_second_base_pos P g (n g) (L g) hg hng hLneg
  constructor
  · exact (le_div_iff₀ hp).2 (by simpa using hb.1)
  · simpa only [one_mul] using (div_le_iff₀ hp).2 hb.2

/-- The divergent physical scale hypothesis itself supplies the eventual
nonzero lengths required by the normalized integral expressions. -/
lemma pants_length_ne_zero_of_scale_diverges (n : ℕ → ℕ) (L : ℕ → ℝ)
    (hscale : Tendsto (fun g => pantsScale g (n g)*(L g)^2) atTop atTop) :
    ∀ᶠ g in atTop, L g ≠ 0 := by
  filter_upwards [hscale.eventually_gt_atTop 0] with g hg
  intro hzero
  simp [hzero] at hg

end WP.RandomGeometry
