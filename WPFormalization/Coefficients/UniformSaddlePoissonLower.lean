import WPFormalization.Analysis.PoissonNormalizer
/-! Faithful uniform saddle estimate for the actual unscaled H(0) kernel: PoissonLower. -/
noncomputable section
namespace WP.Coefficients
open WP.Analysis WP.HigherOrder
lemma finite_positive_sequence_lower (f:ℕ→ℝ)(hf:∀n,0<f n)(N:ℕ):
    ∃c:ℝ,0<c∧∀n≤ N,c≤ f n:=by
  induction N with
  | zero=>
    refine ⟨f 0,hf 0,?_⟩
    intro n hn
    have he:n=0:=by omega
    simpa only[he] using (le_refl (f 0))
  | succ N ih=>
    obtain ⟨c,hc,hbound⟩:=ih
    refine ⟨min c (f (N+1)),lt_min hc (hf _),?_⟩
    intro n hn
    by_cases hn':n≤ N
    · exact (min_le_left _ _).trans (hbound n hn')
    · have he:n=N+1:=by omega
      simpa only[he] using min_le_right c (f (N+1))
lemma poissonCenter_polynomial_lower :
    ∃c:ℝ,0<c∧∀m:ℕ,c/((m:ℝ)+1)≤ poissonCenter m:=by
  obtain ⟨C,B,c,H,hC,hB,hc,hH,herr⟩:=poissonNormalizer_gevrey_one
  let H₁:ℝ:=max 1 (max H (2*C*B))
  have hH₁:0<H₁:=lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  let N:ℕ:=Nat.ceil H₁
  have hH₁N:H₁≤(N:ℝ):=Nat.le_ceil H₁
  have hpc:∀m:ℕ,0<poissonCenter m:=by
    intro m
    cases m with
    | zero=> simp [poissonCenter]
    | succ m=>unfold poissonCenter;positivity
  obtain ⟨d,hd,hfinite⟩:=finite_positive_sequence_lower
    (fun m=>poissonCenter m*((m:ℝ)+1)) (fun m=>mul_pos (hpc m) (by positivity)) N
  let C₀:ℝ:=Real.sqrt (2*Real.pi)
  have hC₀:0<C₀:=Real.sqrt_pos.2 (by positivity)
  refine ⟨min d (1/(2*C₀)),lt_min hd (by positivity),?_⟩
  intro m
  apply (div_le_iff₀ (by positivity:(0:ℝ)<(m:ℝ)+1)).mpr
  by_cases hm:m≤ N
  · exact (min_le_left _ _).trans (hfinite m hm)
  · have hNm:(N:ℝ)≤ m:=by exact_mod_cast (show N≤ m by omega)
    have hmH:H₁≤ m:=hH₁N.trans hNm
    have hm1:1≤(m:ℝ):=(le_max_left _ _).trans hmH
    have hmpos:0<(m:ℝ):=zero_lt_one.trans_le hm1
    have hH:H≤(m:ℝ):=((le_max_left _ _).trans (le_max_right _ _)).trans hmH
    have hCB:2*C*B≤(m:ℝ):=((le_max_right _ _).trans (le_max_right _ _)).trans hmH
    have he:=herr 0 m hH (by simpa only[Nat.cast_zero] using (mul_pos hc hmpos).le)
    simp only[inversePowerTruncation,Finset.sum_range_one,PowerSeries.coeff_zero_eq_constantCoeff,
      poissonStirlingSeries_constant,pow_zero,div_one,Nat.zero_add,pow_one,
      Nat.factorial_one,Nat.cast_one,mul_one] at he
    have hCBhalf:C*B/(m:ℝ)≤1/2:=(div_le_iff₀ hmpos).mpr (by nlinarith)
    have hlo:1/2≤ poissonNormalizer m:=by linarith [neg_le_of_abs_le he]
    have hmnat:1≤ m:=by exact_mod_cast hm1
    rw[poissonNormalizer_nat m hmnat] at hlo
    have hsqrt:Real.sqrt (2*Real.pi*(m:ℝ))≤ C₀*((m:ℝ)+1):=by
      rw[Real.sqrt_mul (by positivity:(0:ℝ)≤2*Real.pi)]
      apply mul_le_mul_of_nonneg_left _ (le_of_lt hC₀)
      apply (Real.sqrt_le_iff).mpr
      constructor
      · positivity
      · nlinarith
    have hlo':1/2≤ C₀*(poissonCenter m*((m:ℝ)+1)):=
      hlo.trans (by nlinarith [mul_le_mul_of_nonneg_right hsqrt (hpc m).le])
    apply (min_le_right _ _).trans
    apply (div_le_iff₀ (by positivity:0<2*C₀)).mpr
    nlinarith
end WP.Coefficients
