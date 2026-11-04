import WPFormalization.Marked.ExternalBoundaryContinuity
import WPFormalization.Volumes.BoundaryDensityShift
noncomputable section
namespace WP.BoundaryConvolution
open Set Filter
open scoped Topology

/-- Replacing the saddle density by n/g does not change the original bounded
boundary-factor product in the large-genus limit, even at unbounded n/g. -/
lemma boundaryFactor_product_density_shift_tendsto (p : ℕ) (L0 : ℝ)
    (gs ns : ℕ → ℕ) (Ls : ℕ → Fin p → ℝ)
    (hg : Tendsto gs atTop atTop) (hn : ∀ j, p ≤ ns j)
    (hL : ∀ j i, Ls j i ∈ Icc 0 L0) :
    Tendsto (fun j =>
      (∏ i, boundaryFactor (densityY (2*((ns j:ℝ)-p)/(2*(gs j:ℝ)-2+p))) (Ls j i)) /
      (∏ i, boundaryFactor (densityY ((ns j:ℝ)/(gs j:ℝ))) (Ls j i))) atTop (𝓝 1) := by
  apply Metric.tendsto_nhds.2
  intro ε hε
  obtain ⟨δ,hδ,hclose⟩ := boundaryFactor_product_uniform_relative_continuity p L0
    (ε/2) (half_pos hε)
  have hgr : Tendsto (fun j => (gs j:ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hg
  have hr : Tendsto (fun j => (Real.pi^2*((p:ℝ)+2)^2)/(gs j:ℝ)) atTop (𝓝 0) :=
    hgr.const_div_atTop _
  filter_upwards [hg.eventually_ge_atTop (p+2),hr.eventually (gt_mem_nhds hδ)] with j hj hs
  have hp : (0:ℝ) ≤ p := Nat.cast_nonneg p
  have hgR : (p:ℝ)+2 ≤ gs j := by exact_mod_cast hj
  have hnR : (p:ℝ) ≤ ns j := by exact_mod_cast hn j
  have hg0 : (0:ℝ) < gs j := by linarith
  have hd : (0:ℝ) < 2*(gs j:ℝ)-2+p := by linarith
  have hLam : 0 ≤ 2*((ns j:ℝ)-p)/(2*(gs j:ℝ)-2+p) :=
    div_nonneg (mul_nonneg (by norm_num) (sub_nonneg.mpr hnR)) hd.le
  have hMu : 0 ≤ (ns j:ℝ)/(gs j:ℝ) := div_nonneg (Nat.cast_nonneg _) hg0.le
  have hY := (Analysis.densityY_spec _ hLam).1
  have hZ := (Analysis.densityY_spec _ hMu).1
  have hdiff := (boundary_densityY_shift p (gs j) (ns j) hj (hn j)).trans_lt hs
  have hh := hclose _ ⟨hY.1,hY.2.le⟩ _ ⟨hZ.1,hZ.2.le⟩ (Ls j) (hL j) hdiff
  simpa only [Real.dist_eq] using hh.trans_lt (half_lt_self hε)
end WP.BoundaryConvolution
