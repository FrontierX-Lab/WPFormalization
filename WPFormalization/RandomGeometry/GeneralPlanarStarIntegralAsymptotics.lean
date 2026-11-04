import WPFormalization.RandomGeometry.GeneralPlanarStarIntegralBounds
import WPFormalization.RandomGeometry.GeneralPlanarStarPrefactor

/-! Fixed ordered planar types, at the original effective length scale.
All errors are absolute, including zero widths and vanishing moving weights. -/
noncomputable section
namespace WP.RandomGeometry
open MeasureTheory Set Filter
open scoped Topology

/-- Half-open physical windows at the exact primitive planar effective scale. -/
def generalPlanarStarScaledWindows (r : ℕ) (q : ℝ) (lo hi : Fin r → ℝ) :
    Fin r → Set ℝ := fun i => Ioc (lo i/Real.sqrt q) (hi i/Real.sqrt q)

lemma general_planar_star_scaled_window_weight (r : ℕ) (q : ℝ) (hq : 0 < q)
    (lo hi : Fin r → ℝ) (hab : ∀i,lo i ≤ hi i) :
    pantsWindowWeight r (generalPlanarStarScaledWindows r q lo hi) =
      ∏i,(((hi i)^2-(lo i)^2)/(2*q)) := by
  rw [pants_window_weight_eq_product]
  apply Finset.prod_congr rfl
  intro i _
  unfold generalPlanarStarScaledWindows
  rw [←intervalIntegral.integral_of_le
    (div_le_div_of_nonneg_right (hab i) (Real.sqrt_nonneg q)),integral_id]
  simp only [div_pow,Real.sq_sqrt hq.le]
  field_simp

lemma general_planar_star_scaled_window_base_identity (P : PsiTheory) (g n r : ℕ)
    (k : Fin r → ℕ) (hk : ∀i,2 ≤ k i) (hkn : (∑i,k i) ≤ n)
    (lo hi : Fin r → ℝ) (hab : ∀i,lo i ≤ hi i)
    (hq : 0 < primitivePlanarEffectiveScale g n) :
    generalPlanarStarWindowBase P g n r k
      (generalPlanarStarScaledWindows r (primitivePlanarEffectiveScale g n) lo hi) =
      generalPlanarStarBase P g n r k lo hi := by
  have hr : r ≤ ∑i,k i := by
    calc
      r = ∑_i : Fin r,1 := by simp
      _ ≤ ∑i,k i := Finset.sum_le_sum (fun i _ => by have := hk i;omega)
  have hm : n-(∑i,k i)+r=n-((∑i,k i)-r) := by omega
  unfold generalPlanarStarWindowBase generalPlanarStarBase
  rw [general_planar_star_scaled_window_weight r _ hq lo hi hab,hm]
  simp_rw [Finset.prod_div_distrib]
  ring

lemma general_planar_star_base_bounded (P : PsiTheory) (r : ℕ) (k : Fin r → ℕ)
    (hk : ∀i,2 ≤ k i) (lo hi : Fin r → ℝ) (n : ℕ → ℕ)
    (hn : Tendsto n atTop atTop) :
    IsBoundedUnder (· ≤ ·) atTop (fun g => ‖generalPlanarStarBase P g (n g) r k lo hi‖) := by
  have he := (general_planar_star_relative_error P r k n hn).norm.isBoundedUnder_le
  have hw := general_planar_star_weight_bounded P r k lo hi n hn
  obtain ⟨A,hA⟩ := he
  obtain ⟨B,hB⟩ := hw
  change ∀ᶠ g in atTop, ‖generalPlanarStarRelativeError P g (n g) r k‖ ≤ A at hA
  change ∀ᶠ g in atTop, ‖generalPlanarStarWeight P r k lo hi (primitiveSaddleX g (n g))‖ ≤ B at hB
  apply isBoundedUnder_of_eventually_le (a := max 0 A*max 0 B)
  filter_upwards [eventually_ge_atTop (1:ℕ),hn.eventually_ge_atTop 2,hA,hB] with g hg hng hAg hBg
  rw [general_planar_star_base_identity P g (n g) r k lo hi hg hng hk,norm_mul]
  exact mul_le_mul (hAg.trans (le_max_right 0 A)) (hBg.trans (le_max_right 0 B))
    (norm_nonneg _) (le_max_left 0 A)

/-- The physical boundary integral differs from its exact zero-boundary
prefactor by an amount tending to zero, for every fixed ordered list of leaf
sizes and every fixed nonnegative window, including windows of zero width. -/
theorem general_planar_star_scaled_window_boundary_error (P : PsiTheory) (r : ℕ)
    (k : Fin r → ℕ) (hk : ∀i,2 ≤ k i) (n : ℕ → ℕ)
    (hnfast : Tendsto (fun g : ℕ => (n g:ℝ)/Real.sqrt g) atTop atTop)
    (lo hi : Fin r → ℝ) (hlo : ∀i,0 ≤ lo i) (hab : ∀i,lo i ≤ hi i) :
    Tendsto (fun g => generalPlanarStarWindowCut P g (n g) r k
      (generalPlanarStarScaledWindows r (primitivePlanarEffectiveScale g (n g)) lo hi) -
      generalPlanarStarBase P g (n g) r k lo hi) atTop (𝓝 0) := by
  have hnreal : Tendsto (fun g => (n g:ℝ)) atTop atTop := by
    apply tendsto_atTop_mono' atTop _ hnfast
    filter_upwards [eventually_ge_atTop (1:ℕ)] with g hg
    have hgR : (1:ℝ) ≤ g := by exact_mod_cast hg
    have hs : 1 ≤ Real.sqrt (g:ℝ) :=
      (Real.le_sqrt (by norm_num) (by positivity)).2 (by nlinarith)
    exact div_le_self (by positivity) hs
  have hn := tendsto_natCast_atTop_iff.mp hnreal
  have hq := primitive_planar_scale_tendsto_atTop n hnfast
  let I := fun g => generalPlanarStarScaledWindows r (primitivePlanarEffectiveScale g (n g)) lo hi
  let B : ℝ := 1+∑i,hi i
  let cap : ℕ → ℝ := fun g => B/Real.sqrt (primitivePlanarEffectiveScale g (n g))
  have hhi : ∀i,0 ≤ hi i := fun i => (hlo i).trans (hab i)
  have hB (i : Fin r) : hi i ≤ B := by
    have hi' := Finset.single_le_sum (fun j _ => hhi j) (Finset.mem_univ i)
    dsimp [B]
    linarith
  have hcap : Tendsto cap atTop (𝓝 0) :=
    primitive_planar_rescaled_length_tendsto_zero n hnfast B
  have hId : ∀ᶠ g in atTop,
      generalPlanarStarWindowBase P g (n g) r k (I g)=generalPlanarStarBase P g (n g) r k lo hi := by
    filter_upwards [hn.eventually_ge_atTop (∑i,k i),hq.eventually_gt_atTop 0] with g hng hqg
    exact general_planar_star_scaled_window_base_identity P g (n g) r k hk hng lo hi hab hqg
  have hb := general_planar_star_base_bounded P r k hk lo hi n hn
  have hb' : IsBoundedUnder (· ≤ ·) atTop
      (fun g => ‖generalPlanarStarWindowBase P g (n g) r k (I g)‖) := by
    obtain ⟨M,hM⟩ := hb
    change ∀ᶠ g in atTop, ‖generalPlanarStarBase P g (n g) r k lo hi‖ ≤ M at hM
    apply isBoundedUnder_of_eventually_le (a := M)
    filter_upwards [hId,hM] with g hg hMg
    simpa only [hg] using hMg
  have ht := general_planar_star_window_cut_difference P r k hk n hn I cap hcap
    (Eventually.of_forall (fun _ _ => measurableSet_Ioc))
    (Eventually.of_forall (fun g i t ht => ⟨
      (div_nonneg (hlo i) (Real.sqrt_nonneg _)).trans ht.1.le,
      ht.2.trans (div_le_div_of_nonneg_right (hB i) (Real.sqrt_nonneg _))⟩)) hb'
  apply ht.congr'
  exact hId.mono fun g hg => by dsimp only; rw [hg]

/-- Complete fixed-type numerical main term at the exact effective scale.
The bounded saddle weight is allowed to vary with g and to tend to zero. -/
theorem general_planar_star_scaled_window_asymptotic (P : PsiTheory) (r : ℕ)
    (k : Fin r → ℕ) (hk : ∀i,2 ≤ k i) (n : ℕ → ℕ)
    (hnfast : Tendsto (fun g : ℕ => (n g:ℝ)/Real.sqrt g) atTop atTop)
    (lo hi : Fin r → ℝ) (hlo : ∀i,0 ≤ lo i) (hab : ∀i,lo i ≤ hi i) :
    Tendsto (fun g => generalPlanarStarWindowCut P g (n g) r k
      (generalPlanarStarScaledWindows r (primitivePlanarEffectiveScale g (n g)) lo hi) -
      generalPlanarStarWeight P r k lo hi (primitiveSaddleX g (n g))) atTop (𝓝 0) := by
  have ht := (general_planar_star_scaled_window_boundary_error P r k hk n hnfast lo hi hlo hab).add
    (general_planar_star_base_asymptotic_fast P r k lo hi hk n hnfast)
  simp only [add_zero] at ht
  simpa only [sub_add_sub_cancel] using ht

end WP.RandomGeometry
