import WPFormalization.Analysis.ChainProfileEndpoint
import WPFormalization.External.FixedGenus
import WPFormalization.Volumes.FixedCuspProof

/-! The bounded-genus end of the chain. Only the old fixed-genus asymptotic
is deferred; the profile matching and error normalization are proved here. -/
noncomputable section
namespace WP
open Filter
open scoped Topology

lemma diagonal_fixed_genus_logarithm_tendsto (P : PsiTheory) (g : ℕ) :
    Tendsto (fun n : ℕ => Real.log (normalizedVolume P g n)/(n : ℝ)) atTop
      (𝓝 (-Real.log (2*xCritical))) := by
  obtain ⟨C,hC,N,hbound⟩ := External.fixed_genus_normalized_volume_logarithm P g
  have he : Tendsto (fun n : ℕ => C*Real.log ((n : ℝ)+1)/(n : ℝ)) atTop (𝓝 0) := by
    simpa only [← mul_div_assoc,mul_zero] using log_genus_over_genus_tendsto_zero.const_mul C
  apply real_tendsto_of_abs_error _ _ _ he
  filter_upwards [eventually_ge_atTop (N+3)] with n hn
  have hnr : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hb := hbound n (by omega) (by unfold Stable;omega)
  have hid : Real.log (normalizedVolume P g n)/(n : ℝ)-(-Real.log (2*xCritical)) =
      (Real.log (normalizedVolume P g n)+(n : ℝ)*Real.log (2*xCritical))/n := by
    field_simp
    ring
  rw [hid,abs_div,abs_of_pos hnr]
  exact div_le_div_of_nonneg_right hb hnr.le

lemma diagonal_fixed_genus_cusp_fraction_tendsto (g : ℕ) :
    Tendsto (fun n : ℕ => (n : ℝ)/(2*g+n)) atTop (𝓝 1) := by
  have hi : Tendsto (fun n : ℕ => (2*(g : ℝ))/(n : ℝ)) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv,mul_zero] using inverse_genus_tendsto_zero.const_mul (2*(g : ℝ))
  have ht := (hi.add_const 1).inv₀ (by norm_num : (0 : ℝ)+1 ≠ 0)
  simp only [zero_add,inv_one] at ht
  apply ht.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hd : (0 : ℝ) < 2*g+n := by positivity
  field_simp

lemma diagonal_fixed_genus_profile_tendsto (g : ℕ) :
    Tendsto (fun n : ℕ => chainProfile ((n : ℝ)/(2*g+n))) atTop
      (𝓝 (-2*Real.log (2*xCritical))) := by
  by_cases hg : g = 0
  · subst g
    apply (tendsto_const_nhds : Tendsto (fun _ : ℕ => -2*Real.log (2*xCritical)) atTop _).congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    simp [hnR,chainProfile]
  have hgR : (0 : ℝ) < g := by exact_mod_cast (show 0 < g by omega)
  have hl : Tendsto (fun n : ℕ => (n : ℝ)/g) atTop atTop :=
    Filter.Tendsto.atTop_div_const hgR (tendsto_natCast_atTop_atTop (R := ℝ))
  have ht := Analysis.chainProfile_density_tendsto.comp hl
  simp only [Function.comp_def] at ht
  apply ht.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hd : (0 : ℝ) < 2*g+n := by positivity
  congr 1
  field_simp

lemma diagonal_fixed_genus_error_tendsto (P : PsiTheory) (g : ℕ) :
    Tendsto (fun n : ℕ => (Real.log (normalizedVolume P g n)-((2*(g : ℝ)+n)/2)*
      chainProfile ((n : ℝ)/(2*g+n)))/(2*g+n)) atTop (𝓝 0) := by
  have ht := ((diagonal_fixed_genus_logarithm_tendsto P g).mul
    (diagonal_fixed_genus_cusp_fraction_tendsto g)).sub
      ((diagonal_fixed_genus_profile_tendsto g).div_const 2)
  have hlim : -Real.log (2*xCritical)*1-(-2*Real.log (2*xCritical))/2 = 0 := by ring
  rw [hlim] at ht
  apply ht.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hd : (0 : ℝ) < 2*g+n := by positivity
  field_simp

lemma diagonal_fixed_genus_estimate (P : PsiTheory) (g : ℕ) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, Stable g n →
      |Real.log (normalizedVolume P g n)-((2*(g : ℝ)+n)/2)*
        chainProfile ((n : ℝ)/(2*g+n))| ≤ ε*(2*g+n) := by
  intro ε hε
  have hb := (diagonal_fixed_genus_error_tendsto P g).eventually
    (Metric.ball_mem_nhds (0 : ℝ) hε)
  obtain ⟨N,hN⟩ := eventually_atTop.mp (hb.and (eventually_ge_atTop 1))
  refine ⟨N,?_⟩
  intro n hn _
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n from by have := (hN n hn).2;omega)
  have hd : (0 : ℝ) < 2*g+n := by positivity
  have hb' := (hN n hn).1
  simp only [Real.dist_eq,sub_zero,abs_div,abs_of_pos hd] at hb'
  exact ((div_lt_iff₀ hd).mp hb').le

end WP
