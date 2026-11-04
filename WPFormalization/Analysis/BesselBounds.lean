import WPFormalization.Analysis.RealBessel
/-! Exact alternating-series bounds for the actual Bessel derivative.
The first positive zero is below 3/2 by a strictly negative finite upper bound,
proved here from Mathlib's alternating-series estimate. -/
noncomputable section
namespace WP
open Filter Set
open scoped Topology
lemma derivX_hasSum_real (y : ℝ) :
    HasSum (fun n : ℕ => (-1:ℝ)^n*y^n/(n.factorial:ℝ)^2) (a y) := by
  have hf : Differentiable ℂ (deriv X) := by
    simpa only [iteratedDeriv_one] using iteratedDeriv_X_differentiable 1
  have hs : HasSum (fun n : ℕ => (((-1:ℝ)^n*y^n/(n.factorial:ℝ)^2:ℝ):ℂ))
      (deriv X y) := by
    convert Complex.hasSum_taylorSeries_of_entire hf 0 (y:ℂ) using 1
    ext n
    rw [← iteratedDeriv_succ',iteratedDeriv_X_succ_zero]
    simp only [sub_zero,smul_eq_mul]
    push_cast
    ring
  simpa only [Complex.reCLM_apply,Complex.ofReal_re,a] using hs.mapL Complex.reCLM
lemma a_three_halves_neg : a (3/2) < 0 := by
  let f : ℕ → ℝ := fun n => (3/2:ℝ)^(n+1)/((n+1).factorial:ℝ)^2
  have hrec (n : ℕ) : f (n+1) = f n*((3/2)/((n:ℝ)+2)^2) := by
    dsimp [f]
    rw [show n+1+1 = (n+1)+1 by omega,Nat.factorial_succ,pow_succ]
    push_cast
    have hn : (n:ℝ)+2 ≠ 0 := by positivity
    have hf : ((n+1).factorial:ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (n+1)
    field_simp
    <;> ring
  have hanti : Antitone f := by
    apply antitone_nat_of_succ_le
    intro n
    rw [hrec]
    apply mul_le_of_le_one_right (show 0 ≤ f n by dsimp [f]; positivity)
    apply (div_le_one (by positivity : (0:ℝ)<((n:ℝ)+2)^2)).2
    nlinarith [Nat.cast_nonneg (α:=ℝ) n]
  have htail : HasSum (fun n : ℕ => (-1:ℝ)^n*f n) (1-a (3/2)) := by
    have hh := ((hasSum_nat_add_iff' 1).mpr (derivX_hasSum_real (3/2))).neg
    convert hh using 1
    · ext n
      dsimp [f]
      rw [pow_succ]
      ring
    · norm_num
  have hb := Antitone.alternating_series_le_tendsto htail.tendsto_sum_nat hanti 2
  norm_num [f,Finset.sum_range_succ] at hb
  linarith
lemma y₀_lt_three_halves : y₀ < 3/2 := by
  have hc : Continuous a := by
    unfold a
    have hd : Continuous (deriv X) := by
      simpa only [iteratedDeriv_one] using (iteratedDeriv_X_differentiable 1).continuous
    exact Complex.continuous_re.comp (hd.comp Complex.continuous_ofReal)
  obtain ⟨t,ht,hat⟩ := intermediate_value_Icc' (by norm_num : (0:ℝ)≤3/2) hc.continuousOn
    (show (0:ℝ)∈Icc (a (3/2)) (a 0) from ⟨a_three_halves_neg.le,by rw [a_zero]; norm_num⟩)
  have ht0 : 0 < t := lt_of_le_of_ne ht.1 (by
    intro he
    have he' : t = 0 := he.symm
    subst t
    simpa [a_zero] using hat)
  have htl : t < 3/2 := lt_of_le_of_ne ht.2 (by intro he; rw [he] at hat; exact (ne_of_lt a_three_halves_neg) hat)
  have htroot : deriv X (t:ℂ) = 0 := by rw [derivX_ofReal,hat]; rfl
  exact lt_of_le_of_lt (csInf_le ⟨0,fun y hy=>hy.1.le⟩ ⟨ht0,htroot⟩) htl
end WP
