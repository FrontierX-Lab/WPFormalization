import WPFormalization.Volumes.GrowingBoundaryEstimate
import WPFormalization.Statements.ZografConstant

/-! Boundary lengths may depend on genus and grow as o(sqrt g).
The original WP measure volume, rather than only a numerical recurrence,
is retained in the geometric conclusion. -/
noncomputable section
universe u v
namespace WP
open Set Filter
open scoped Topology

lemma boundary_square_sum_over_genus_tendsto_zero (n : ℕ) (L : ℕ → Fin n → ℝ)
    (hL : ∀ i, Tendsto (fun g : ℕ => L g i/Real.sqrt g) atTop (𝓝 0)) :
    Tendsto (fun g : ℕ => (∑ i, (L g i)^2)/(g:ℝ)) atTop (𝓝 0) := by
  have hi (i : Fin n) : Tendsto (fun g : ℕ => (L g i)^2/(g:ℝ)) atTop (𝓝 0) := by
    have ht := (hL i).pow 2
    simpa only [div_pow,Real.sq_sqrt (Nat.cast_nonneg _),zero_pow (by norm_num : (2:ℕ) ≠ 0)] using ht
  simpa only [Finset.sum_div,Finset.sum_const_zero] using tendsto_finsetSum Finset.univ (fun i _ => hi i)

theorem fixed_cusp_growing_boundary_model_limit (P : PsiTheory)
    (n : ℕ) (hn : 1 ≤ n) (L : ℕ → Fin n → ℝ)
    (hL : ∀ i, Tendsto (fun g : ℕ => L g i/Real.sqrt g) atTop (𝓝 0)) :
    Tendsto (fun g : ℕ => boundaryVolumeModel P g n (L g) /
      (volumeModel P g n * ∏ i, boundaryFactor 0 (L g i))) atTop (𝓝 1) := by
  obtain ⟨C,hC,hbound⟩ := fixed_cusp_all_length_model_bound P n hn
  have herr : Tendsto (fun g : ℕ => C/g*∑ i, (L g i)^2) atTop (𝓝 0) := by
    have ht := (boundary_square_sum_over_genus_tendsto_zero n L hL).const_mul C
    simpa only [mul_zero,mul_div_assoc,div_mul_eq_mul_div] using ht
  apply real_tendsto_of_abs_error _ _ 1 herr
  filter_upwards [eventually_ge_atTop (1:ℕ)] with g hg
  have hb := hbound g hg (L g)
  rw [abs_sub_comm,abs_of_nonneg hb.1]
  exact hb.2

theorem fixed_cusp_growing_boundary_limit (P : PsiTheory)
    (G : External.WeilPeterssonGeometry.{u,v} P)
    (n : ℕ) (hn : 1 ≤ n) (L : ℕ → Fin n → ℝ)
    (hLnonneg : ∀ g i, 0 ≤ L g i)
    (hL : ∀ i, Tendsto (fun g : ℕ => L g i/Real.sqrt g) atTop (𝓝 0)) :
    Tendsto (fun g : ℕ => External.wpVolume G g n (L g) /
      (External.cuspVolume G g n * ∏ i, boundaryFactor 0 (L g i))) atTop (𝓝 1) := by
  apply (fixed_cusp_growing_boundary_model_limit P n hn L hL).congr'
  filter_upwards [eventually_ge_atTop (1:ℕ)] with g hg
  have hs : Stable g n := by unfold Stable;omega
  rw [Geometry.wpVolume_eq_boundaryVolumeModel P G g n (L g) hs (hLnonneg g),
    Geometry.cuspVolume_eq_volumeModel P G g n hs]

lemma fixed_cusp_volume_over_leading_tendsto (P : PsiTheory) (n : ℕ) :
    Tendsto (fun g : ℕ => volumeModel P g n/fixedCuspLeadingScale g n) atTop (𝓝 1) := by
  obtain ⟨C,hC,G,hbound⟩ := zograf_constant P n
  apply real_tendsto_of_abs_error _ _ 1 (tendsto_const_div_atTop_nhds_zero_nat C)
  exact eventually_atTop.mpr ⟨G,hbound⟩

end WP
