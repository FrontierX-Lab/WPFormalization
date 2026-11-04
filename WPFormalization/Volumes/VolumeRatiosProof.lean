import WPFormalization.Volumes.VolumeRatiosGenus
import WPFormalization.Volumes.VolumeRatiosCusp
import WPFormalization.Volumes.RatioQCusp

/-! Original Theorem 1.3 with one common inverse-genus constant, uniformly in
all cusp counts. The true extraction models, their two different saddles,
the original profile shifts and the fixed-cusp zero endpoint are all supplied
by proved producers. No paper-specific estimate is an explicit premise. -/
noncomputable section
namespace WP

theorem volume_ratios_proof (P : PsiTheory) :
    ∃ C : ℝ, 0 < C ∧ ∃ g₀ : ℕ, ∀ g ≥ g₀,
      (∀ n : ℕ,
        |(volumeModel P g n/volumeModel P (g-1) (n+2))/profileB ((n : ℝ)/g)-1| ≤ C/g ∧
        |(volumeModel P g (n+1)/(2*g*volumeModel P g n))/profileC ((n : ℝ)/g)-1| ≤ C/g) ∧
      (∀ n : ℕ, 1 ≤ n →
        |volumeModel P g n^2/(volumeModel P g (n-1)*volumeModel P g (n+1))-1| ≤ C/g) := by
  have hstar := volume_ratios_cusp_at_extraction_density_of_model_bound P
    Analysis.ratioQ_cusp_uniform_rate
  have hpos := volume_ratios_cusp_positive_of_extraction_density P hstar
  have hcusp := volume_ratios_cusp_all_of_positive P hpos
  have hthird := volume_ratios_third_of_cusp_control P hcusp
    Analysis.volume_profile_C_adjacent_uniform
  exact volume_ratios_join P (volume_ratios_genus_all_cusps P) hcusp hthird

end WP
