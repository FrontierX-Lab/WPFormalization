import WPFormalization.Analysis.VolumeProfileRegular

/-! Uniform replacement of the actual original volume-ratio profiles at the
shifted finite-genus density, and at adjacent cusp densities. Constants and
thresholds precede the unrestricted cusp count. -/
noncomputable section
namespace WP.Analysis
open Set

lemma volume_profile_relative_of_log_bound (a b δ : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hδ : |Real.log a-Real.log b| ≤ δ) (hsmall : δ ≤ 1) :
    |a/b-1| ≤ 2*δ := by
  have he : Real.exp (Real.log a-Real.log b) = a/b := by
    rw [Real.exp_sub,Real.exp_log ha,Real.exp_log hb]
  rw [←he]
  exact (Real.abs_exp_sub_one_le (hδ.trans hsmall)).trans
    (mul_le_mul_of_nonneg_left hδ (by norm_num))

lemma volume_profile_shift_weighted (g n : ℝ) (hg : 1 ≤ g) (hn : 1 ≤ n) :
    |2*(n-1)/(2*g-1)-n/g|/(1+min (2*(n-1)/(2*g-1)) (n/g)) ≤ 2/g := by
  have hgp : 0 < g := by linarith
  have hdp : 0 < 2*g-1 := by linarith
  let u := 2*(n-1)/(2*g-1)
  let v := n/g
  have hu0 : 0 ≤ u := div_nonneg (by linarith) hdp.le
  have hv0 : 0 ≤ v := div_nonneg (by linarith) hgp.le
  have he : u-v = (n-2*g)/(g*(2*g-1)) := by
    dsimp [u,v]
    field_simp
    <;> ring
  change |u-v|/(1+min u v) ≤ 2/g
  rcases le_total n (2*g) with hng | hgn
  · have huv : u ≤ v := by
      apply sub_nonpos.mp
      rw [he]
      exact div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hng) (mul_pos hgp hdp).le
    rw [min_eq_left huv,abs_of_nonpos (sub_nonpos.mpr huv),neg_sub]
    apply (div_le_iff₀ (by linarith : 0 < 1+u)).2
    have hh : (2*g-n)/(2*g-1) ≤ 2 := by
      apply (div_le_iff₀ hdp).2
      linarith
    have hh' := div_le_div_of_nonneg_right hh hgp.le
    have hh'' : v-u ≤ 2/g := by
      have hneg : v-u = (2*g-n)/(g*(2*g-1)) := by rw [←neg_sub,he,←neg_div,neg_sub]
      rw [hneg]
      simpa only [div_div,mul_comm] using hh'
    exact hh''.trans (le_mul_of_one_le_right (div_nonneg (by norm_num) hgp.le) (by linarith))
  · have hvu : v ≤ u := by
      apply sub_nonneg.mp
      rw [he]
      exact div_nonneg (sub_nonneg.mpr hgn) (mul_pos hgp hdp).le
    rw [min_eq_right hvu,abs_of_nonneg (sub_nonneg.mpr hvu)]
    apply (div_le_iff₀ (by linarith : 0 < 1+v)).2
    have hh : (n-2*g)/(2*g-1) ≤ n/g := by
      apply (div_le_div_iff₀ hdp hgp).2
      have hmul := mul_nonneg (by linarith : 0 ≤ g-1) (by linarith : 0 ≤ n)
      nlinarith [sq_nonneg g]
    have hh' := div_le_div_of_nonneg_right hh hgp.le
    have hh'' : u-v ≤ v/g := by
      rw [he]
      simpa only [div_div,mul_comm,v] using hh'
    exact hh''.trans (by
      calc v/g ≤ (2*(1+v))/g := div_le_div_of_nonneg_right (by linarith) hgp.le
           _ = (2/g)*(1+v) := by ring)

lemma volume_profile_B_shift_rate (g n : ℕ) (hg : 8 ≤ g) (hn : 1 ≤ n) :
    |profileB (2*((n:ℝ)-1)/(2*g-1))/profileB ((n:ℝ)/g)-1| ≤ 16/g := by
  have hgr : (8:ℝ) ≤ g := by exact_mod_cast hg
  have hnr : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hgp : (0:ℝ) < g := by linarith
  have hdp : (0:ℝ) < 2*g-1 := by linarith
  have hl : 0 ≤ 2*((n:ℝ)-1)/(2*g-1) := div_nonneg (by linarith) hdp.le
  have hm : 0 ≤ (n:ℝ)/g := by positivity
  have hs := volume_profile_shift_weighted g n (by linarith) hnr
  have hh := volume_profile_B_log_comparison _ _ hl hm
  have hh' : |Real.log (profileB (2*((n:ℝ)-1)/(2*g-1)))-Real.log (profileB ((n:ℝ)/g))| ≤ 8/g := by
    have hb := mul_le_mul_of_nonneg_left hs (show (0:ℝ) ≤ 4 by norm_num)
    calc
      _ ≤ 4*|2*((n:ℝ)-1)/(2*g-1)-(n:ℝ)/g|/(1+min (2*((n:ℝ)-1)/(2*g-1)) ((n:ℝ)/g)) := hh
      _ ≤ 8/g := by convert hb using 1 <;> ring
  have hr := volume_profile_relative_of_log_bound _ _ (8/g)
    (volume_profile_B_pos _ hl) (volume_profile_B_pos _ hm) hh'
    ((div_le_one hgp).2 hgr)
  convert hr using 1 <;> ring

lemma volume_profile_C_shift_rate (g n : ℕ) (hg : 8 ≤ g) (hn : 1 ≤ n) :
    |profileC (2*((n:ℝ)-1)/(2*g-1))/profileC ((n:ℝ)/g)-1| ≤ 4/g := by
  have hgr : (8:ℝ) ≤ g := by exact_mod_cast hg
  have hnr : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hgp : (0:ℝ) < g := by linarith
  have hdp : (0:ℝ) < 2*g-1 := by linarith
  have hl : 0 ≤ 2*((n:ℝ)-1)/(2*g-1) := div_nonneg (by linarith) hdp.le
  have hm : 0 ≤ (n:ℝ)/g := by positivity
  have hs := volume_profile_shift_weighted g n (by linarith) hnr
  have hh := (volume_profile_C_log_comparison _ _ hl hm).trans hs
  have hr := volume_profile_relative_of_log_bound _ _ (2/g)
    (volume_profile_C_pos _ hl) (volume_profile_C_pos _ hm) hh
    ((div_le_one hgp).2 (by linarith))
  convert hr using 1 <;> ring

lemma volume_profile_C_adjacent_rate (g n : ℕ) (hg : 1 ≤ g) (hn : 1 ≤ n) :
    |profileC (((n:ℝ)-1)/g)/profileC ((n:ℝ)/g)-1| ≤ 2/g := by
  have hgr : (1:ℝ) ≤ g := by exact_mod_cast hg
  have hnr : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hgp : (0:ℝ) < g := by linarith
  have hl : 0 ≤ ((n:ℝ)-1)/g := div_nonneg (by linarith) hgp.le
  have hm : 0 ≤ (n:ℝ)/g := by positivity
  have hle : ((n:ℝ)-1)/g ≤ (n:ℝ)/g := div_le_div_of_nonneg_right (by linarith) hgp.le
  have hh := volume_profile_C_log_comparison _ _ hl hm
  have hdiff : |((n:ℝ)-1)/g-(n:ℝ)/g| = 1/g := by
    rw [abs_of_nonpos (sub_nonpos.mpr hle)]
    ring
  rw [hdiff,min_eq_left hle] at hh
  have hh' : |Real.log (profileC (((n:ℝ)-1)/g))-Real.log (profileC ((n:ℝ)/g))| ≤ 1/g :=
    hh.trans (div_le_self (by positivity) (by linarith))
  have hr := volume_profile_relative_of_log_bound _ _ (1/g)
    (volume_profile_C_pos _ hl) (volume_profile_C_pos _ hm) hh'
    ((div_le_one hgp).2 hgr)
  convert hr using 1 <;> ring


lemma volume_profile_B_shift_uniform :
    ∃ C : ℝ, 0 < C ∧ ∃ G : ℕ, ∀ g ≥ G, ∀ n : ℕ, 1 ≤ n →
      |profileB (2*((n-1:ℕ):ℝ)/(2*g-1))/profileB ((n:ℝ)/g)-1| ≤ C/g := by
  refine ⟨16,by norm_num,8,?_⟩
  intro g hg n hn
  simpa only [Nat.cast_sub hn,Nat.cast_one] using volume_profile_B_shift_rate g n hg hn

lemma volume_profile_C_shift_uniform :
    ∃ C : ℝ, 0 < C ∧ ∃ G : ℕ, ∀ g ≥ G, ∀ n : ℕ, 1 ≤ n →
      |profileC (2*((n-1:ℕ):ℝ)/(2*g-1))/profileC ((n:ℝ)/g)-1| ≤ C/g := by
  refine ⟨4,by norm_num,8,?_⟩
  intro g hg n hn
  simpa only [Nat.cast_sub hn,Nat.cast_one] using volume_profile_C_shift_rate g n hg hn

lemma volume_profile_C_adjacent_uniform :
    ∃ C : ℝ, 0 < C ∧ ∃ G : ℕ, ∀ g ≥ G, ∀ n : ℕ, 1 ≤ n →
      |profileC (((n-1:ℕ):ℝ)/g)/profileC ((n:ℝ)/g)-1| ≤ C/g := by
  refine ⟨2,by norm_num,1,?_⟩
  intro g hg n hn
  simpa only [Nat.cast_sub hn,Nat.cast_one] using volume_profile_C_adjacent_rate g n hg hn

end WP.Analysis
