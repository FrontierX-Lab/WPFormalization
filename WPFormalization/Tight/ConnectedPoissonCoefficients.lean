import WPFormalization.Tight.ConnectedGenusRatio

noncomputable section
set_option maxHeartbeats 1000000
namespace WP.TightConnected
open Set Filter
open scoped Topology

lemma positive_pgf_remainder_bound (a : ℕ → ℝ) (ha : ∀ i, 0 ≤ a i)
    (hmass : HasSum a 1) (z : ℝ) (hz : z ∈ Icc (0:ℝ) 1)
    (F : ℝ) (hF : HasSum (fun i => a i*z^i) F) (n : ℕ) :
    0 ≤ F - ∑ i ∈ Finset.range (n+1), a i*z^i ∧
      F - ∑ i ∈ Finset.range (n+1), a i*z^i ≤ z^(n+1) := by
  have hs := hF.summable.sum_add_tsum_nat_add (n+1)
  rw [hF.tsum_eq] at hs
  have hmassTail : Summable (fun i => a (i+(n+1))) :=
    (summable_nat_add_iff (n+1)).mpr hmass.summable
  have htail : Summable (fun i => a (i+(n+1))*z^(i+(n+1))) :=
    (summable_nat_add_iff (n+1)).mpr hF.summable
  have hmassTailLe : ∑' i, a (i+(n+1)) ≤ 1 := by
    have he := hmass.summable.sum_add_tsum_nat_add (n+1)
    rw [hmass.tsum_eq] at he
    have hnon : 0 ≤ ∑ i ∈ Finset.range (n+1), a i :=
      Finset.sum_nonneg (fun i _ => ha i)
    linarith
  have hnon : 0 ≤ ∑' i, a (i+(n+1))*z^(i+(n+1)) :=
    tsum_nonneg (fun i => mul_nonneg (ha _) (pow_nonneg hz.1 _))
  have hle : ∑' i, a (i+(n+1))*z^(i+(n+1)) ≤ z^(n+1) := by
    calc
      _ ≤ ∑' i, a (i+(n+1))*z^(n+1) :=
        htail.tsum_le_tsum (fun i => mul_le_mul_of_nonneg_left
          (pow_le_pow_of_le_one hz.1 hz.2 (by omega)) (ha _))
          (hmassTail.mul_right _)
      _ = (∑' i, a (i+(n+1)))*z^(n+1) := tsum_mul_right
      _ ≤ 1*z^(n+1) := mul_le_mul_of_nonneg_right hmassTailLe (pow_nonneg hz.1 _)
      _ = _ := one_mul _
  constructor <;> linarith

lemma positive_pgf_coefficient_distance (a : ℕ → ℝ) (ha : ∀ i, 0 ≤ a i)
    (hmass : HasSum a 1) (z : ℝ) (hz : z ∈ Ioc (0:ℝ) 1)
    (F : ℝ) (hF : HasSum (fun i => a i*z^i) F) (n : ℕ) :
    dist (a n) ((F - ∑ i ∈ Finset.range n, a i*z^i)/z^n) ≤ z := by
  have h := positive_pgf_remainder_bound a ha hmass z ⟨hz.1.le,hz.2⟩ F hF n
  rw [Finset.sum_range_succ] at h
  have hzn : 0 < z^n := pow_pos hz.1 n
  have hlo : 0 ≤ (F - ∑ i ∈ Finset.range n, a i*z^i)/z^n - a n := by
    apply (sub_nonneg.mpr ?_)
    apply (le_div_iff₀ hzn).mpr
    linarith [h.1]
  have hhi : (F - ∑ i ∈ Finset.range n, a i*z^i)/z^n - a n ≤ z := by
    apply (sub_le_iff_le_add).mpr
    apply (div_le_iff₀ hzn).mpr
    rw [pow_succ] at h
    nlinarith [h.2]
  rw [Real.dist_eq,abs_sub_comm,abs_of_nonneg hlo]
  exact hhi

lemma positive_pgf_coefficients_tendsto (a : ℕ → ℕ → ℝ) (b : ℕ → ℝ)
    (F : ℕ → ℝ → ℝ) (G : ℝ → ℝ)
    (ha : ∀ᶠ j in atTop, (∀ i,0≤a j i) ∧ HasSum (a j) 1 ∧
      ∀ z∈Icc (0:ℝ) 1, HasSum (fun i=>a j i*z^i) (F j z))
    (hb : (∀ i,0≤b i) ∧ HasSum b 1 ∧
      ∀ z∈Icc (0:ℝ) 1, HasSum (fun i=>b i*z^i) (G z))
    (hFG : ∀ z∈Ioo (0:ℝ) 1,Tendsto (fun j=>F j z) atTop (𝓝 (G z))) :
    ∀ n,Tendsto (fun j=>a j n) atTop (𝓝 (b n)) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    apply Metric.tendsto_atTop.mpr
    intro ε hε
    let z : ℝ := min (ε/8) (1/2)
    have hz : 0 < z := lt_min (by positivity) (by norm_num)
    have hz1 : z < 1 := (min_le_right _ _).trans_lt (by norm_num)
    have hzε : z ≤ ε/8 := min_le_left _ _
    have hprefix : Tendsto (fun j=>∑ i∈Finset.range n,a j i*z^i) atTop
        (𝓝 (∑ i∈Finset.range n,b i*z^i)) := by
      apply tendsto_finset_sum
      intro i hi
      exact (ih i (Finset.mem_range.mp hi)).mul_const _
    have hquot := ((hFG z ⟨hz,hz1⟩).sub hprefix).div_const (z^n)
    have hnear : ∀ᶠ j in atTop,
        dist ((F j z-∑ i∈Finset.range n,a j i*z^i)/z^n)
          ((G z-∑ i∈Finset.range n,b i*z^i)/z^n) < ε/2 := by
      exact hquot.eventually (Metric.ball_mem_nhds _ (by positivity))
    have he : ∀ᶠ j in atTop, dist (a j n) (b n) < ε := by
      filter_upwards [ha,hnear] with j hj hq
      have hda := positive_pgf_coefficient_distance (a j) hj.1 hj.2.1 z
        ⟨hz,hz1.le⟩ _ (hj.2.2 z ⟨hz.le,hz1.le⟩) n
      have hdb := positive_pgf_coefficient_distance b hb.1 hb.2.1 z
        ⟨hz,hz1.le⟩ _ (hb.2.2 z ⟨hz.le,hz1.le⟩) n
      have htri := dist_triangle4 (a j n)
        ((F j z-∑ i∈Finset.range n,a j i*z^i)/z^n)
        ((G z-∑ i∈Finset.range n,b i*z^i)/z^n) (b n)
      have hdb' : dist ((G z-∑ i∈Finset.range n,b i*z^i)/z^n) (b n) ≤ z := by
        simpa only [dist_comm] using hdb
      linarith
    exact eventually_atTop.mp he

end WP.TightConnected
