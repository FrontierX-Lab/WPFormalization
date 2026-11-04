import WPFormalization.RandomGeometry.PantsFixedOrderAsymptotics
import WPFormalization.Critical.CutCriticalRegime
import WPFormalization.Volumes.VolumeRatiosEndpoints

/-! Actual zero-boundary ratios for the surviving mixed cut in (G.6).
Only the original all-cusp Theorem 1.3 is used; no mixed-cut estimate is
introduced as a premise. -/
noncomputable section
namespace WP.Critical
open Filter
open scoped Topology

lemma surviving_genus_shift_tendsto (k : ℕ) :
    Tendsto (fun g : ℕ => (g:ℝ)/((g-k:ℕ):ℝ)) atTop (𝓝 1) := by
  have hh := (tendsto_const_nhds.sub
    (tendsto_const_div_atTop_nhds_zero_nat (k:ℝ))).inv₀ (by norm_num : (1:ℝ)-0 ≠ 0)
  simp only [sub_zero,inv_one] at hh
  apply hh.congr'
  filter_upwards [eventually_ge_atTop (k+1)] with g hg
  rw [Nat.cast_sub (by omega : k ≤ g)]
  have hg0 : (g:ℝ) ≠ 0 := by exact_mod_cast (show g ≠ 0 by omega)
  field_simp

lemma surviving_critical_density (n : ℕ → ℕ) (c : ℝ)
    (hn : Tendsto (fun g : ℕ => (n g:ℝ)/Real.sqrt g) atTop (𝓝 c)) :
    Tendsto (fun g : ℕ => (n g:ℝ)/g) atTop (𝓝 0) := by
  have hh := hn.mul (tendsto_inv_atTop_zero.comp
    (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop))
  simp only [mul_zero] at hh
  apply hh.congr'
  filter_upwards [eventually_ge_atTop (1:ℕ)] with g hg
  have hg0 : (0:ℝ) < g := by exact_mod_cast (show 0 < g by omega)
  change (n g:ℝ)/Real.sqrt (g:ℝ)*(Real.sqrt (g:ℝ))⁻¹ = _
  rw [←div_eq_mul_inv,div_div,Real.mul_self_sqrt hg0.le]

lemma surviving_critical_cusps_tendsto (n : ℕ → ℕ) (c : ℝ) (hc : 0 < c)
    (hn : Tendsto (fun g : ℕ => (n g:ℝ)/Real.sqrt g) atTop (𝓝 c)) :
    Tendsto n atTop atTop := by
  have hh := hn.pos_mul_atTop hc (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  apply (tendsto_natCast_atTop_iff (R := ℝ)).mp
  apply hh.congr'
  filter_upwards [eventually_ge_atTop (1:ℕ)] with g hg
  have hs : Real.sqrt (g:ℝ) ≠ 0 := by positivity
  exact div_mul_cancel₀ _ hs

lemma surviving_shifted_density (n : ℕ → ℕ)
    (hn : Tendsto (fun g => (n g:ℝ)/g) atTop (𝓝 0)) (k q : ℕ) :
    Tendsto (fun g => ((n g+q:ℕ):ℝ)/((g-k:ℕ):ℝ)) atTop (𝓝 0) := by
  have hh := (hn.add (tendsto_const_div_atTop_nhds_zero_nat (q:ℝ))).mul
    (surviving_genus_shift_tendsto k)
  simp only [zero_add,zero_mul] at hh
  apply hh.congr'
  filter_upwards [eventually_ge_atTop (k+1)] with g hg
  rw [Nat.cast_add]
  have hg0 : (g:ℝ) ≠ 0 := by exact_mod_cast (show g ≠ 0 by omega)
  field_simp

lemma surviving_sub_density (n : ℕ → ℕ)
    (hn : Tendsto (fun g => (n g:ℝ)/g) atTop (𝓝 0)) (r : ℕ) :
    Tendsto (fun g => ((n g-r:ℕ):ℝ)/g) atTop (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall (fun _ => by positivity)) _ hn
  exact Eventually.of_forall (fun g => div_le_div_of_nonneg_right
    (by exact_mod_cast Nat.sub_le (n g) r) (Nat.cast_nonneg g))

lemma surviving_profile_B_zero (l : ℕ → ℝ) (hl : ∀ g, 0 ≤ l g)
    (ht : Tendsto l atTop (𝓝 0)) : Tendsto (fun g => profileB (l g)) atTop (𝓝 1) := by
  have hh : Tendsto (fun g => Real.log (profileB (l g))) atTop (𝓝 (Real.log (profileB 0))) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    simp only [Real.norm_eq_abs]
    apply squeeze_zero' (Eventually.of_forall (fun _ => abs_nonneg _)) _ (by simpa only [mul_zero] using ht.const_mul 4)
    exact Eventually.of_forall (fun g => by
      simpa only [sub_zero,abs_of_nonneg (hl g),min_eq_right (hl g),add_zero,div_one]
        using Analysis.volume_profile_B_log_comparison (l g) 0 (hl g) le_rfl)
  have he := Real.continuous_exp.continuousAt.tendsto.comp hh
  simpa only [Function.comp_def,Real.exp_log (Analysis.volume_profile_B_pos _ le_rfl),
    Real.exp_log (Analysis.volume_profile_B_pos _ (hl _)),profileB_zero_volume_ratios,Real.log_one,Real.exp_zero] using he

lemma surviving_profile_C_zero (l : ℕ → ℝ) (hl : ∀ g, 0 ≤ l g)
    (ht : Tendsto l atTop (𝓝 0)) :
    Tendsto (fun g => profileC (l g)) atTop (𝓝 (4*Real.pi^2)) := by
  have hh : Tendsto (fun g => Real.log (profileC (l g))) atTop (𝓝 (Real.log (profileC 0))) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    simp only [Real.norm_eq_abs]
    apply squeeze_zero' (Eventually.of_forall (fun _ => abs_nonneg _)) _ ht
    exact Eventually.of_forall (fun g => by
      simpa only [sub_zero,abs_of_nonneg (hl g),min_eq_right (hl g),add_zero,div_one]
        using Analysis.volume_profile_C_log_comparison (l g) 0 (hl g) le_rfl)
  have he := Real.continuous_exp.continuousAt.tendsto.comp hh
  simpa only [Function.comp_def,Real.exp_log (Analysis.volume_profile_C_pos _ le_rfl),
    Real.exp_log (Analysis.volume_profile_C_pos _ (hl _)),profileC_zero_volume_ratios,Real.exp_log (by positivity : (0:ℝ)<4*Real.pi^2)] using he

lemma surviving_genus_step (P : PsiTheory) (m : ℕ → ℕ)
    (hm : Tendsto m atTop atTop)
    (hd : Tendsto (fun g => (m g:ℝ)/g) atTop (𝓝 0)) (j : ℕ) :
    Tendsto (fun g => volumeModel P (g-j-1) (m g+2*j+2)/
      volumeModel P (g-j) (m g+2*j)) atTop (𝓝 1) := by
  obtain ⟨C,hC,G,hG⟩ := volume_ratios P
  have ht : Tendsto (fun g =>
      (volumeModel P (g-j) (m g+2*j)/volumeModel P (g-j-1) (m g+2*j+2))/
      profileB (((m g+2*j:ℕ):ℝ)/((g-j:ℕ):ℝ))) atTop (𝓝 1) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    simp only [Real.norm_eq_abs]
    apply squeeze_zero' (Eventually.of_forall (fun _ => abs_nonneg _)) _
      ((tendsto_const_div_atTop_nhds_zero_nat C).comp (tendsto_sub_atTop_nat j))
    filter_upwards [(tendsto_sub_atTop_nat j).eventually_ge_atTop G] with g hg
    exact ((hG (g-j) hg).1 (m g+2*j)).1
  have hb := surviving_profile_B_zero _ (fun _ => by positivity)
    (surviving_shifted_density m hd j (2*j))
  have hh := (ht.mul hb).inv₀ (by norm_num : (1:ℝ)*1 ≠ 0)
  simp only [one_mul,inv_one] at hh
  apply hh.congr'
  filter_upwards [eventually_ge_atTop (j+2),hm.eventually_ge_atTop 1] with g hg hmg
  have hp := (Analysis.volume_profile_B_pos
    (((m g+2*j:ℕ):ℝ)/((g-j:ℕ):ℝ)) (by positivity)).ne'
  rw [div_mul_cancel₀ _ hp,inv_div]

/-- Every fixed number of nonseparating loops has the actual zero-density
B(0)=1 ratio. The cusp sequence itself need not have a limit. -/
lemma surviving_genus_ratio (P : PsiTheory) (m : ℕ → ℕ)
    (hm : Tendsto m atTop atTop)
    (hd : Tendsto (fun g => (m g:ℝ)/g) atTop (𝓝 0)) (k : ℕ) :
    Tendsto (fun g => volumeModel P (g-k) (m g+2*k)/volumeModel P g (m g))
      atTop (𝓝 1) := by
  induction k with
  | zero =>
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop (1:ℕ),hm.eventually_ge_atTop 1] with g hg hmg
    have hp := (diagonal_volume_pos_nonempty P g (m g) hmg
      (by unfold Stable;omega)).ne'
    simp [hp]
  | succ k ih =>
    have hh := (surviving_genus_step P m hm hd k).mul ih
    simp only [one_mul] at hh
    apply hh.congr'
    filter_upwards [eventually_ge_atTop (k+2),hm.eventually_ge_atTop 1] with g hg hmg
    have hp := (diagonal_volume_pos_nonempty P (g-k) (m g+2*k)
      (by omega) (by unfold Stable;omega)).ne'
    rw [show g-k-1=g-(k+1) by omega,show m g+2*k+2=m g+2*(k+1) by omega]
    exact div_mul_div_cancel₀ hp

/-- The zero-boundary root-volume ratio of the surviving mixed graph in G.6. -/
lemma surviving_mixed_volume_ratio (P : PsiTheory) (n : ℕ → ℕ)
    (hn : Tendsto n atTop atTop)
    (hd : Tendsto (fun g => (n g:ℝ)/g) atTop (𝓝 0)) (r k : ℕ) :
    Tendsto (fun g => (8*Real.pi^2*g)^r*
      volumeModel P (g-k) (n g-r+2*k)/volumeModel P g (n g)) atTop (𝓝 1) := by
  have hC := surviving_profile_C_zero _ (fun _ => by positivity) hd
  have hs := ((tendsto_const_nhds (x := (4*Real.pi^2:ℝ))).div hC (by positivity : (4*Real.pi^2:ℝ) ≠ 0)).pow r
  have hf := RandomGeometry.pants_fixed_volume_ratio P r n hn
  have hgen := surviving_genus_ratio P (fun g => n g-r)
    ((tendsto_sub_atTop_nat r).comp hn) (surviving_sub_density n hd r) k
  have hh := (hs.mul hf).mul hgen
  norm_num only [div_self (by positivity : (4*Real.pi^2:ℝ) ≠ 0),one_pow,one_mul] at hh
  apply hh.congr'
  filter_upwards [eventually_ge_atTop (k+2),hn.eventually_ge_atTop (r+1)] with g hg hng
  have hcp := (Analysis.volume_profile_C_pos ((n g:ℝ)/g) (by positivity)).ne'
  have hv := (diagonal_volume_pos_nonempty P g (n g-r)
    (by omega) (by unfold Stable;omega)).ne'
  change (((4*Real.pi^2)/profileC ((n g:ℝ)/g))^r*
    ((2*g*profileC ((n g:ℝ)/g))^r*volumeModel P g (n g-r)/volumeModel P g (n g)))*
      (volumeModel P (g-k) (n g-r+2*k)/volumeModel P g (n g-r)) = _
  rw [div_pow]
  field_simp
  simp only [mul_pow]
  rw [show (8:ℝ)^r=(4:ℝ)^r*2^r by rw [←mul_pow]; norm_num]
  ring

end WP.Critical
