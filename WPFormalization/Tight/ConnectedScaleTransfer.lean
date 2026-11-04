import WPFormalization.Tight.ConnectedScale
noncomputable section
namespace WP.TightConnected
open Set Filter
open scoped Topology

lemma connected_r_eq_scale_square (Y:ℝ) (hY:Y∈Ico (0:ℝ) y₀) :
    r Y=(Real.pi^2/2)*(tightParameterScale Y)^2 := by
  have hh := tightParameterScale_square Y hY
  field_simp [Real.pi_ne_zero] at hh
  nlinarith

lemma connected_r_ratio_eq_scale_square (Y Z:ℝ)
    (hY:Y∈Ico (0:ℝ) y₀) (hZ:Z∈Ico (0:ℝ) y₀) :
    r Y/r Z=(tightParameterScale Y/tightParameterScale Z)^2 := by
  rw [connected_r_eq_scale_square Y hY,connected_r_eq_scale_square Z hZ]
  have hα := (tightParameterScale_pos Z hZ).ne'
  field_simp [hα,Real.pi_ne_zero]

lemma connected_r_ratio_tendsto (Ys Zs:ℕ→ℝ)
    (hY:∀j,Ys j∈Ico (0:ℝ) y₀) (hZ:∀j,Zs j∈Ico (0:ℝ) y₀)
    (hscale:Tendsto (fun j=>tightParameterScale (Ys j)/tightParameterScale (Zs j)) atTop (𝓝 1)) :
    Tendsto (fun j=>r (Ys j)/r (Zs j)) atTop (𝓝 1) := by
  have ht := hscale.pow 2
  simp only [one_pow] at ht
  apply ht.congr'
  exact Eventually.of_forall (fun j=>(connected_r_ratio_eq_scale_square _ _ (hY j) (hZ j)).symm)
end WP.TightConnected
