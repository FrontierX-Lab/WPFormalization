import WPFormalization.Volumes.GrowingBoundaryLimit
import WPFormalization.Volumes.KimuraGammaNormalization

/-! The growing-boundary Kimura consequence in the introduction, proved from
the paper's all-length estimate and its proved identification of Zograf's
constant. The physical conjecture is not an assumption. -/
noncomputable section
universe u v
namespace WP
open Set Filter
open scoped Topology

lemma fixed_cusp_volume_over_kimura_tendsto (P : PsiTheory) (n : ℕ) :
    Tendsto (fun g : ℕ => volumeModel P g n/kimuraCuspLeadingScale g n)
      atTop (𝓝 1) := by
  have ht := (fixed_cusp_volume_over_leading_tendsto P n).mul
    (fixed_cusp_leading_over_kimura_tendsto n)
  simp only [one_mul] at ht
  apply ht.congr'
  filter_upwards [eventually_ge_atTop (2:ℕ)] with g hg
  have hgp : (0:ℝ) < g := by exact_mod_cast (show 0 < g by omega)
  have hF : fixedCuspLeadingScale g n ≠ 0 := by unfold fixedCuspLeadingScale;positivity
  have hK := (kimuraCuspLeadingScale_pos g n hg).ne'
  field_simp [hF,hK]

theorem fixed_cusp_growing_boundary_kimura_model (P : PsiTheory)
    (n : ℕ) (hn : 1 ≤ n) (L : ℕ → Fin n → ℝ)
    (hL : ∀ i, Tendsto (fun g : ℕ => L g i/Real.sqrt g) atTop (𝓝 0)) :
    Tendsto (fun g : ℕ => boundaryVolumeModel P g n (L g) /
      (kimuraCuspLeadingScale g n * ∏ i, boundaryFactor 0 (L g i)))
      atTop (𝓝 1) := by
  have hv := fixed_cusp_volume_over_kimura_tendsto P n
  have ht := (fixed_cusp_growing_boundary_model_limit P n hn L hL).mul hv
  simp only [one_mul] at ht
  apply ht.congr'
  filter_upwards [eventually_ge_atTop (2:ℕ),hv.eventually (lt_mem_nhds zero_lt_one)] with g hg hvg
  have hK := (kimuraCuspLeadingScale_pos g n hg).ne'
  have hV : volumeModel P g n ≠ 0 := by
    intro hz
    simp only [hz,zero_div] at hvg
    exact lt_irrefl 0 hvg
  have hB : (∏ i, boundaryFactor 0 (L g i)) ≠ 0 :=
    (zero_lt_one.trans_le (Finset.one_le_prod₀ (fun i _ => one_le_boundaryFactor _ _))).ne'
  field_simp [hK,hV,hB]

/-- Actual WP volumes, with arbitrary nonnegative lengths satisfying only
the coordinatewise o(sqrt g) condition. -/
theorem fixed_cusp_growing_boundary_kimura (P : PsiTheory)
    (G : External.WeilPeterssonGeometry.{u,v} P)
    (n : ℕ) (hn : 1 ≤ n) (L : ℕ → Fin n → ℝ)
    (hLnonneg : ∀ g i, 0 ≤ L g i)
    (hL : ∀ i, Tendsto (fun g : ℕ => L g i/Real.sqrt g) atTop (𝓝 0)) :
    Tendsto (fun g : ℕ => External.wpVolume G g n (L g) /
      (Real.sqrt (2/Real.pi)*(4*Real.pi^2)^(2*g+n-3)*
        Real.Gamma (2*(g:ℝ)+n-5/2) *
        ∏ i, (if L g i=0 then 1 else Real.sinh (L g i/2)/(L g i/2))))
      atTop (𝓝 1) := by
  have ht := fixed_cusp_growing_boundary_kimura_model P n hn L hL
  have he (x : ℝ) := (boundary_factor_endpoints x).1
  simp_rw [kimuraCuspLeadingScale,he] at ht
  apply ht.congr'
  filter_upwards [eventually_ge_atTop (1:ℕ)] with g hg
  rw [Geometry.wpVolume_eq_boundaryVolumeModel P G g n (L g)
    (by unfold Stable;omega) (hLnonneg g)]

end WP
