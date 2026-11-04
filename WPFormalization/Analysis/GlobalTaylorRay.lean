import WPFormalization.Analysis.UniformTaylorRemainder

/-! A fixed complex Cauchy circle and a true real-ray bound give a global Taylor remainder at every order. The constants precede the order and ray variable. -/
noncomputable section
namespace WP.Analysis
open Set
lemma complex_taylor_global_ray_bound (f : ℂ→ℂ) (R M T : ℝ) (hR : 0<R)
    (hM : 0≤M) (hT : 0≤T) (hf : DifferentiableOn ℂ f (Metric.closedBall 0 R))
    (hcircle : ∀z∈Metric.sphere (0:ℂ) R,‖f z‖≤M)
    (htail : ∀t:ℝ,R/2≤t → ‖f (t:ℂ)‖≤T) (N : ℕ) (t : ℝ) (ht : 0<t) :
    ‖f (t:ℂ)-(∑i∈Finset.range N,WP.coeff f i*(t:ℂ)^i)‖ ≤
      (T+2*M)*(2/R)^N*t^N := by
  have hnorm : ‖(t:ℂ)‖=t := by rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos ht]
  by_cases hsmall : t≤R/2
  · have hb := complex_taylor_remainder_bound f R M hR hM hf hcircle N (t:ℂ) (by rwa [hnorm])
    rw [hnorm] at hb
    apply hb.trans
    have hbase : t/R ≤ 2/R*t := by
      calc
        _ ≤ 2*(t/R) := by
          have h : 0≤t/R := by positivity
          linarith
        _ = _ := by ring
    calc
      _ ≤ (T+2*M)*(2/R*t)^N :=
        mul_le_mul (by linarith : 2*M≤T+2*M)
          (pow_le_pow_left₀ (by positivity) hbase N) (by positivity) (by positivity)
      _ = _ := by rw [mul_pow];ring
  · have hrt : R/2≤t := (lt_of_not_ge hsmall).le
    let Y : ℝ := 2*t/R
    have hY : 1≤Y := by dsimp [Y];apply (le_div_iff₀ hR).mpr;linarith
    have hY0 : 0≤Y := by linarith
    have hYN : (1:ℝ)≤Y^N := one_le_pow₀ hY
    have hgeo : (∑i∈Finset.range N,(1/2:ℝ)^i)≤2 := by
      have he := geom_sum_mul (1/2:ℝ) N
      norm_num at he
      nlinarith [pow_nonneg (by norm_num : (0:ℝ)≤1/2) N]
    have hi (i : ℕ) (hi : i∈Finset.range N) :
        ‖WP.coeff f i*(t:ℂ)^i‖≤M*Y^N*(1/2:ℝ)^i := by
      have hiN : i≤N := (Finset.mem_range.mp hi).le
      rw [norm_mul,norm_pow,hnorm]
      calc
        _ ≤ (M/R^i)*t^i := mul_le_mul_of_nonneg_right (coeff_norm_le_circle_bound f R M hR hf hcircle i) (by positivity)
        _ = M*Y^i*(1/2:ℝ)^i := by
          dsimp [Y]
          rw [div_pow,mul_pow,div_pow]
          field_simp
          ring
        _ ≤ _ := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hY hiN) hM) (by positivity)
    have hpoly : ‖∑i∈Finset.range N,WP.coeff f i*(t:ℂ)^i‖≤2*M*Y^N := by
      calc
        _ ≤ ∑i∈Finset.range N,‖WP.coeff f i*(t:ℂ)^i‖ := norm_sum_le _ _
        _ ≤ ∑i∈Finset.range N,M*Y^N*(1/2:ℝ)^i := Finset.sum_le_sum hi
        _ = (M*Y^N)*(∑i∈Finset.range N,(1/2:ℝ)^i) := by rw [Finset.mul_sum]
        _ ≤ (M*Y^N)*2 := mul_le_mul_of_nonneg_left hgeo (by positivity)
        _ = _ := by ring
    calc
      _ ≤ ‖f (t:ℂ)‖+‖∑i∈Finset.range N,WP.coeff f i*(t:ℂ)^i‖ := norm_sub_le _ _
      _ ≤ T+2*M*Y^N := add_le_add (htail t hrt) hpoly
      _ ≤ T*Y^N+2*M*Y^N := add_le_add (by nlinarith) le_rfl
      _ = _ := by dsimp [Y];rw [div_pow,mul_pow,div_pow];ring
end WP.Analysis
