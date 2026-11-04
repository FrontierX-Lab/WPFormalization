import WPFormalization.Analysis.BesselBounds
/-! The elementary sign estimates in Lemma 2.1, proved from the actual X
series. Exact alternating-series bounds give X>0, X''<0 and X'''>0 on
the required interval; an exact series identity gives X(y)=-y X''(y).
The complex zero enumeration and canonical product are separate obligations.
-/
noncomputable section
namespace WP
open Filter Set
open scoped Topology
lemma iteratedDeriv_iterated_X (n k : ℕ) :
    iteratedDeriv n (iteratedDeriv k X) = iteratedDeriv (n+k) X := by
  simp only [iteratedDeriv_eq_iterate,Function.iterate_add_apply]
lemma X_derivative_hasSum_real (k : ℕ) (hk : 1 ≤ k) (y : ℝ) :
    HasSum (fun n : ℕ => (-1:ℝ)^(n+k-1)*y^n/
      ((n.factorial:ℝ)*((n+k-1).factorial:ℝ))) ((iteratedDeriv k X (y:ℂ)).re) := by
  have hs : HasSum (fun n : ℕ => (((-1:ℝ)^(n+k-1)*y^n/
      ((n.factorial:ℝ)*((n+k-1).factorial:ℝ)):ℝ):ℂ)) (iteratedDeriv k X (y:ℂ)) := by
    convert Complex.hasSum_taylorSeries_of_entire (iteratedDeriv_X_differentiable k) 0 (y:ℂ) using 1
    ext n
    rw [iteratedDeriv_iterated_X,iteratedDeriv_X_zero (n+k) (by omega)]
    simp only [sub_zero,smul_eq_mul]
    push_cast
    ring
  simpa only [Complex.reCLM_apply,Complex.ofReal_re] using hs.mapL Complex.reCLM
lemma negative_second_hasSum (y : ℝ) :
    HasSum (fun n : ℕ => (-1:ℝ)^n*y^n/((n.factorial:ℝ)*((n+1).factorial:ℝ)))
      (-(iteratedDeriv 2 X (y:ℂ)).re) := by
  have hs := (X_derivative_hasSum_real 2 (by norm_num) y).neg
  convert hs using 1
  ext n
  rw [show n+2-1=n+1 by omega,pow_succ]
  ring
lemma third_X_hasSum (y : ℝ) :
    HasSum (fun n : ℕ => (-1:ℝ)^n*y^n/((n.factorial:ℝ)*((n+2).factorial:ℝ)))
      (iteratedDeriv 3 X (y:ℂ)).re := by
  convert X_derivative_hasSum_real 3 (by norm_num) y using 1
  ext n
  rw [show n+3-1=n+2 by omega,pow_add]
  norm_num
def besselMagnitude (b s : ℕ) (y : ℝ) (n : ℕ) : ℝ :=
  y^(n+s)/(((n+s).factorial:ℝ)*((n+s+b).factorial:ℝ))
lemma besselMagnitude_succ (b s n : ℕ) (y : ℝ) :
    besselMagnitude b s y (n+1) = besselMagnitude b s y n *
      (y/(((n:ℝ)+s+1)*((n:ℝ)+s+b+1))) := by
  dsimp [besselMagnitude]
  rw [show n+1+s=n+s+1 by omega,show n+s+1+b=n+s+b+1 by omega,
    Nat.factorial_succ,Nat.factorial_succ,pow_succ]
  push_cast
  have hn : ((n:ℝ)+s+1) ≠ 0 := by positivity
  have hb : ((n:ℝ)+s+b+1) ≠ 0 := by positivity
  have hf : ((n+s).factorial:ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (n+s)
  have hg : ((n+s+b).factorial:ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (n+s+b)
  field_simp
lemma besselMagnitude_antitone (b s : ℕ) (y : ℝ) (hy : 0 ≤ y)
    (hm : y ≤ ((s:ℝ)+1)*((s:ℝ)+b+1)) : Antitone (besselMagnitude b s y) := by
  apply antitone_nat_of_succ_le
  intro n
  rw [besselMagnitude_succ]
  apply mul_le_of_le_one_right (show 0 ≤ besselMagnitude b s y n by dsimp [besselMagnitude]; positivity)
  apply (div_le_one (by positivity : (0:ℝ)<((n:ℝ)+s+1)*((n:ℝ)+s+b+1))).2
  apply hm.trans
  nlinarith [Nat.cast_nonneg (α:=ℝ) n,Nat.cast_nonneg (α:=ℝ) s,Nat.cast_nonneg (α:=ℝ) b]
lemma second_X_cubic_bound (y : ℝ) (hy : y ∈ Icc 0 (5/2:ℝ)) :
    1-y/2+y^2/12-y^3/144 ≤ -(iteratedDeriv 2 X (y:ℂ)).re := by
  have ht : HasSum (fun n : ℕ => (-1:ℝ)^n*besselMagnitude 1 1 y n)
      (1+(iteratedDeriv 2 X (y:ℂ)).re) := by
    have hh := ((hasSum_nat_add_iff' 1).mpr (negative_second_hasSum y)).neg
    convert hh using 1
    · ext n
      dsimp [besselMagnitude]
      rw [pow_succ]
      ring
    · norm_num
  have ha := besselMagnitude_antitone 1 1 y hy.1 (by norm_num;linarith [hy.2])
  have hb := Antitone.tendsto_le_alternating_series ht.tendsto_sum_nat ha 1
  norm_num [besselMagnitude,Finset.sum_range_succ] at hb
  linarith
lemma bessel_cubic_pos (y : ℝ) (hy : y ∈ Icc 0 (5/2:ℝ)) :
    0 < 1-y/2+y^2/12-y^3/144 := by
  have hq : 0 ≤ 1/2-(y+5/2)/12+(y^2+y*(5/2)+(5/2)^2)/144 := by
    nlinarith [hy.1,hy.2,sq_nonneg y]
  have hh := mul_nonneg (sub_nonneg.mpr hy.2) hq
  nlinarith only [hh]
lemma second_X_neg_interval (y : ℝ) (hy : y ∈ Icc 0 (5/2:ℝ)) :
    (iteratedDeriv 2 X (y:ℂ)).re < 0 := by
  linarith [bessel_cubic_pos y hy,second_X_cubic_bound y hy]
lemma third_X_pos_interval (y : ℝ) (hy : y ∈ Icc 0 (5/2:ℝ)) :
    0 < (iteratedDeriv 3 X (y:ℂ)).re := by
  have ha := besselMagnitude_antitone 2 0 y hy.1 (by norm_num;linarith [hy.2])
  have hh : HasSum (fun n : ℕ => (-1:ℝ)^n*besselMagnitude 2 0 y n)
      (iteratedDeriv 3 X (y:ℂ)).re := by
    simpa only [besselMagnitude,Nat.add_zero,mul_div_assoc] using third_X_hasSum y
  have hb := Antitone.alternating_series_le_tendsto hh.tendsto_sum_nat ha 1
  norm_num [besselMagnitude,Finset.sum_range_succ] at hb
  linarith [hy.2]
lemma X_hasSum_real (y : ℝ) :
    HasSum (fun n : ℕ => (-1:ℝ)^n*y^(n+1)/
      ((n.factorial:ℝ)*((n+1).factorial:ℝ))) (XR y) := by
  have hs : HasSum (fun n : ℕ => (((-1:ℝ)^n*y^(n+1)/
      ((n.factorial:ℝ)*((n+1).factorial:ℝ)):ℝ):ℂ)) (X (y:ℂ)) := by
    have hh := (hasSum_nat_add_iff' 1).mpr
      (Complex.hasSum_taylorSeries_of_entire X_differentiable 0 (y:ℂ))
    convert hh using 1
    · ext n
      rw [iteratedDeriv_X_succ_zero]
      simp only [sub_zero,smul_eq_mul]
      push_cast
      ring
    · simp [X]
  simpa only [Complex.reCLM_apply,Complex.ofReal_re,XR] using hs.mapL Complex.reCLM
lemma XR_eq_neg_mul_second (y : ℝ) :
    XR y = y*(-(iteratedDeriv 2 X (y:ℂ)).re) := by
  have hh : HasSum (fun n : ℕ => (-1:ℝ)^n*y^(n+1)/
      ((n.factorial:ℝ)*((n+1).factorial:ℝ)))
      (y*(-(iteratedDeriv 2 X (y:ℂ)).re)) := by
    convert (negative_second_hasSum y).mul_left y using 1
    ext n
    rw [pow_succ]
    ring
  exact (X_hasSum_real y).unique hh
lemma XR_pos_interval (y : ℝ) (hy : y ∈ Ioc 0 (5/2:ℝ)) : 0 < XR y := by
  rw [XR_eq_neg_mul_second]
  exact mul_pos hy.1 (neg_pos.mpr (second_X_neg_interval y ⟨hy.1.le,hy.2⟩))
lemma XR_le_self_interval (y : ℝ) (hy : y ∈ Icc 0 (2:ℝ)) : XR y ≤ y := by
  have ha := besselMagnitude_antitone 1 0 y hy.1 (by norm_num;exact hy.2)
  have hh : HasSum (fun n : ℕ => (-1:ℝ)^n*besselMagnitude 1 0 y n)
      (-(iteratedDeriv 2 X (y:ℂ)).re) := by
    simpa only [besselMagnitude,Nat.add_zero,mul_div_assoc] using negative_second_hasSum y
  have hb := Antitone.tendsto_le_alternating_series hh.tendsto_sum_nat ha 0
  norm_num [besselMagnitude,Finset.sum_range_succ] at hb
  rw [XR_eq_neg_mul_second]
  exact (mul_le_mul_of_nonneg_left hb hy.1).trans_eq (mul_one y)
lemma bessel_signs_pi_interval :
    (∀ y : ℝ, y ∈ Ioc 0 (Real.pi^2/4) → 0 < XR y) ∧
    (∀ y : ℝ, y ∈ Icc 0 (Real.pi^2/4) →
      (iteratedDeriv 2 X y).re < 0 ∧ 0 < (iteratedDeriv 3 X y).re) ∧
    y₀ < 3/2 ∧ (∀ Y ∈ Icc 0 y₀, XR Y ≤ Y) := by
  have hp : Real.pi^2/4 < (5/2:ℝ) := by nlinarith [Real.pi_lt_d2,Real.pi_pos]
  refine ⟨?_,?_,y₀_lt_three_halves,?_⟩
  · intro y hy
    exact XR_pos_interval y ⟨hy.1,hy.2.trans hp.le⟩
  · intro y hy
    have hh : y ∈ Icc 0 (5/2:ℝ) := ⟨hy.1,hy.2.trans hp.le⟩
    exact ⟨second_X_neg_interval y hh,third_X_pos_interval y hh⟩
  · intro y hy
    exact XR_le_self_interval y ⟨hy.1,by linarith [hy.2,y₀_lt_three_halves]⟩
lemma second_X_neg_before (y : ℝ) (hy : y ≤ (5/2:ℝ)) :
    (iteratedDeriv 2 X (y:ℂ)).re < 0 := by
  by_cases h : 0 ≤ y
  · exact second_X_neg_interval y ⟨h,hy⟩
  have hn (n : ℕ) : 0 ≤ (-1:ℝ)^n*y^n/((n.factorial:ℝ)*((n+1).factorial:ℝ)) := by
    have he : (-1:ℝ)^n*y^n = (-y)^n := by rw [← mul_pow];congr 1;ring
    rw [he]
    exact div_nonneg (pow_nonneg (neg_nonneg.mpr (le_of_not_ge h)) n) (by positivity)
  have hs := negative_second_hasSum y
  have hb := hs.summable.le_tsum 0 (fun n _=> hn n)
  rw [hs.tsum_eq] at hb
  norm_num at hb
  linarith

end WP
