import WPFormalization.Volumes.GrowingBoundaryMoments
import WPFormalization.Geometry.Bridge

/-! Original (7.19): fixed cusp count and every nonnegative length vector.
The coefficient constant depends only on the fixed cusp count, and the
estimate is valid already for every positive genus. -/
noncomputable section
universe u v
namespace WP
open Set Filter BoundaryConvolution
open scoped Topology

theorem fixed_cusp_all_length_model_bound (P : PsiTheory) (n : ℕ) (hn : 1 ≤ n) :
    ∃ C : ℝ, 0 < C ∧ ∀ g : ℕ, 1 ≤ g → ∀ L : Fin n → ℝ,
      0 ≤ 1-boundaryVolumeModel P g n L /
        (volumeModel P g n * ∏ i, boundaryFactor 0 (L i)) ∧
      1-boundaryVolumeModel P g n L /
        (volumeModel P g n * ∏ i, boundaryFactor 0 (L i)) ≤
        C/g * ∑ i, (L i)^2 := by
  obtain ⟨C,hC,hprofile⟩ := quadratic_profile_all_markings_proof P n hn
  refine ⟨C*(n:ℝ)/8,by positivity,?_⟩
  intro g hg L
  have hgR : (0:ℝ) < g := by exact_mod_cast (show 0 < g by omega)
  have hB : 0 < ∏ i, boundaryFactor 0 (L i) :=
    zero_lt_one.trans_le (Finset.one_le_prod₀ (fun i _ => one_le_boundaryFactor _ _))
  have hnon (d : Fin n → ℕ) : 0 ≤ boundaryProfileLoss P g n L d :=
    mul_nonneg (hprofile g hg (List.ofFn d) (by simp) 0 ⟨le_rfl,y₀_pos.le⟩).1
      (boundaryDegreeWeight_nonneg n L d)
  have hsum0 : 0 ≤ ∑' d, boundaryProfileLoss P g n L d := tsum_nonneg hnon
  have hdegree := boundary_degree_quadratic_moment n hn L
  have hterm (d : Fin n → ℕ) : boundaryProfileLoss P g n L d ≤
      C/g * (boundaryProfileMoment d * boundaryDegreeWeight n L d) := by
    have hp := (hprofile g hg (List.ofFn d) (by simp) 0 ⟨le_rfl,y₀_pos.le⟩).2
    have he : C*((List.ofFn d).sum:ℝ)*((List.ofFn d).sum+1)/(g:ℝ) =
        C/g*boundaryProfileMoment d := by
      simp only [List.sum_ofFn,boundaryProfileMoment]
      push_cast
      ring
    rw [he] at hp
    simpa only [boundaryProfileLoss,mul_assoc] using
      mul_le_mul_of_nonneg_right hp (boundaryDegreeWeight_nonneg n L d)
  have hsum : (∑' d, boundaryProfileLoss P g n L d) ≤
      (C/g) * (((n:ℝ)/8 * ∑ i, (L i)^2) * ∏ i, boundaryFactor 0 (L i)) := by
    calc _ ≤ ∑' d, C/g*(boundaryProfileMoment d*boundaryDegreeWeight n L d) :=
           (boundaryProfileLoss_summable P g n hg hn L).tsum_le_tsum hterm (hdegree.1.mul_left (C/g))
         _ = (C/g) * ∑' d, boundaryProfileMoment d*boundaryDegreeWeight n L d := tsum_mul_left
         _ ≤ _ := mul_le_mul_of_nonneg_left hdegree.2 (div_nonneg hC.le hgR.le)
  have he : 1-boundaryVolumeModel P g n L /
      (volumeModel P g n * ∏ i, boundaryFactor 0 (L i)) =
      (∑' d, boundaryProfileLoss P g n L d)/(∏ i, boundaryFactor 0 (L i)) := by
    rw [boundaryProfileLoss_tsum_eq P g n hg hn L,sub_div,div_self hB.ne',div_mul_eq_div_div]
  rw [he]
  refine ⟨div_nonneg hsum0 hB.le,?_⟩
  apply (div_le_iff₀ hB).2
  convert hsum using 1
  ring

/-- The actual WP-volume statement of (7.19), via the exact geometric
volume-polynomial bridge, with no bounded-length hypothesis. -/
theorem fixed_cusp_all_length_bound (P : PsiTheory)
    (G : External.WeilPeterssonGeometry.{u,v} P) (n : ℕ) (hn : 1 ≤ n) :
    ∃ C : ℝ, 0 < C ∧ ∀ g : ℕ, 1 ≤ g → ∀ L : Fin n → ℝ,
      (∀ i, 0 ≤ L i) →
      0 ≤ 1-External.wpVolume G g n L /
        (External.cuspVolume G g n * ∏ i, boundaryFactor 0 (L i)) ∧
      1-External.wpVolume G g n L /
        (External.cuspVolume G g n * ∏ i, boundaryFactor 0 (L i)) ≤
        C/g * ∑ i, (L i)^2 := by
  obtain ⟨C,hC,h⟩ := fixed_cusp_all_length_model_bound P n hn
  refine ⟨C,hC,?_⟩
  intro g hg L hL
  have hs : Stable g n := by unfold Stable;omega
  rw [Geometry.wpVolume_eq_boundaryVolumeModel P G g n L hs hL,
    Geometry.cuspVolume_eq_volumeModel P G g n hs]
  exact h g hg L

end WP
