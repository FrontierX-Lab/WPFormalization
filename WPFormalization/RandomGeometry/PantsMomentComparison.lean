import Mathlib
noncomputable section
open Filter
open scoped Topology
namespace WP.RandomGeometry

/-- These are the exact finite factors left by the ordered two- and four-cusp
label counts. The inputs are elementary real numbers, not asymptotic fields. -/
lemma two_pants_base_relative (n L V0 V1 V2 : ℝ)
    (hn0 : n ≠ 0) (hn1 : n-1 ≠ 0) (hL : L ≠ 0)
    (hV0 : V0 ≠ 0) (hV1 : V1 ≠ 0) (hV2 : V2 ≠ 0) :
    (n*(n-1)*(n-2)*(n-3)*L^4/16*(V2/V0)) /
      (n*(n-1)*L^2/4*(V1/V0))^2 =
      ((n-2)*(n-3)/(n*(n-1))) / (V1^2/(V2*V0)) := by
  field_simp
  <;> ring

lemma label_pair_ratio_tendsto_one (n : ℕ → ℝ) (hn : Tendsto n atTop atTop) :
    Tendsto (fun g => (n g-2)*(n g-3)/(n g*(n g-1))) atTop (𝓝 1) := by
  have hi : Tendsto (fun g => (n g)⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero.comp hn
  have hlim : Tendsto (fun g => (1-2*(n g)⁻¹)*(1-3*(n g)⁻¹)/(1-(n g)⁻¹))
      atTop (𝓝 1) := by
    convert (((tendsto_const_nhds.sub (hi.const_mul 2)).mul
      (tendsto_const_nhds.sub (hi.const_mul 3))).div
      (tendsto_const_nhds.sub hi) (by norm_num : (1 : ℝ)-0 ≠ 0)) using 1 <;> norm_num
  apply hlim.congr'
  filter_upwards [hn.eventually_gt_atTop 0] with g hg
  field_simp
  <;> ring

/-- A positive multiplicative boundary error between 1 and exp(c L) vanishes
when the physical short-curve length L tends to zero. -/
lemma exponential_boundary_squeeze (L error : ℕ → ℝ) (c : ℝ)
    (hL : Tendsto L atTop (𝓝 0))
    (herror : ∀ᶠ g in atTop, 1 ≤ error g ∧ error g ≤ Real.exp (c*L g)) :
    Tendsto error atTop (𝓝 1) := by
  have hu : Tendsto (fun g => Real.exp (c*L g)) atTop (𝓝 1) := by
    have ht : Tendsto (fun g => c*L g) atTop (𝓝 0) := by simpa using hL.const_mul c
    simpa only [Real.exp_zero, Function.comp_def] using (Real.continuous_exp.tendsto 0).comp ht
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu
    (herror.mono fun _ h => h.1) (herror.mono fun _ h => h.2)

end WP.RandomGeometry
