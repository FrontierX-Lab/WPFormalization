import WPFormalization.Volumes.RatioModelSaddle

noncomputable section
namespace WP.Analysis
open Set

lemma ratioSaddle_density_root (h k : ℝ) (hh : 0<h) (hk : 0<k) :
    let Y:=densityY (2*k/h)
    Y ∈ Ioo (0:ℝ) y₀ ∧ h*Psi (XR Y)=k := by
  dsimp only
  have hρ : 0<2*k/h := by positivity
  have hY := densityY_spec (2*k/h) hρ.le
  have hYpos : 0 < densityY (2*k/h) := by
    by_contra hn
    have hz : densityY (2*k/h)=0 := le_antisymm (le_of_not_gt hn) hY.1.1
    have he := hY.2
    rw [hz,density_zero_value] at he
    linarith
  refine ⟨⟨hYpos,hY.1.2⟩,?_⟩
  unfold Psi
  rw [inverseY_eq_of_root _ _ hY.1.2.le rfl,hY.2]
  field_simp [hh.ne']
  <;> ring

lemma ratioSaddle_density_root_order (h k : ℝ) (hh : 0<h) (hk : 0<k) :
    densityY (2*k/(h+1)) ≤ densityY (2*k/h) := by
  have hρ : 0≤2*k/h := by positivity
  have hρ' : 0≤2*k/(h+1) := by positivity
  have hY := densityY_spec (2*k/h) hρ
  have hY' := densityY_spec (2*k/(h+1)) hρ'
  have harg : 2*k/(h+1) ≤ 2*k/h := by
    apply (div_le_div_iff₀ (by linarith : 0<h+1) hh).mpr
    nlinarith
  by_contra hn
  have hm := density_strictMonoOn hY.1 hY'.1 (lt_of_not_ge hn)
  rw [hY.2,hY'.2] at hm
  exact (not_lt_of_ge harg) hm

lemma ratioModel_cusp_actual_saddle_log_bounds :
    ∃ C : ℝ,0<C ∧ ∀ g k : ℕ,1≤g → 1≤k →
      let h:ℝ:=complexity g 1
      let Y:=densityY (2*(k:ℝ)/h)
      let Y':=densityY (2*(k:ℝ)/(h+1))
      |(Real.log (markedModel g 2 Y')-(k:ℝ)*Real.log (XR Y'))-
        (Real.log (markedModel g 2 Y)-(k:ℝ)*Real.log (XR Y))|≤C/h ∧
      |Real.log (euler Psi (XR Y'))-Real.log (euler Psi (XR Y))|≤C/h := by
  obtain ⟨C,hC,hmodel⟩ := ratioModel_saddle_log_variation 2
  obtain ⟨D,hD,hvar⟩ := ratioSaddle_variance_log_variation
  refine ⟨max C D,lt_of_lt_of_le hC (le_max_left _ _),?_⟩
  intro g k hg hk
  dsimp only
  have hs : Stable g 2 := by unfold Stable;omega
  have hh : 0<(complexity g 1:ℝ) := by
    exact_mod_cast (show 0<complexity g 1 by unfold complexity;omega)
  have hkp : 0<(k:ℝ) := by exact_mod_cast (show 0<k by omega)
  have hc : (complexity g 2:ℝ)=(complexity g 1:ℝ)+1 := by
    have hn : complexity g 2=complexity g 1+1 := by unfold complexity;omega
    exact_mod_cast hn
  have hY := ratioSaddle_density_root (complexity g 1) k hh hkp
  have hY' := ratioSaddle_density_root ((complexity g 1:ℝ)+1) k (by linarith) hkp
  have hYY := ratioSaddle_density_root_order (complexity g 1) k hh hkp
  have hm := hmodel g k hs hk _ hY'.1 _ hY.1 hYY
    (by rw [hc];linarith) (by simpa only [hc,add_sub_cancel_right] using hY.2)
    (by simpa only [hc] using hY'.2)
  have hv := hvar (complexity g 1) k hh hkp _ hY'.1 _ hY.1 hYY hY.2 hY'.2
  rw [abs_sub_comm,hc,add_sub_cancel_right] at hm
  rw [abs_sub_comm] at hv
  exact ⟨hm.trans (div_le_div_of_nonneg_right (le_max_left _ _) hh.le),
    hv.trans (div_le_div_of_nonneg_right (le_max_right _ _) hh.le)⟩

end WP.Analysis
