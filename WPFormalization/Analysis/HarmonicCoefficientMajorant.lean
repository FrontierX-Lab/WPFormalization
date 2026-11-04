import WPFormalization.Analysis.HarmonicEstimates
import WPFormalization.Analysis.HarmonicMass
import WPFormalization.Intersection.CriticalCoefficient
/-! A uniform geometric coefficient majorant for the actual harmonic kernel.
The probability normalization bounds inverse coefficients using the positive
constant mass. A coefficientwise power comparison with the genuine geometric
series then gives B^m (h)_m / m! for every natural power h. -/
noncomputable section
namespace WP.Analysis
open PowerSeries Set

lemma affineInverse_coeff_complex (B:ℝ)(h m:ℕ):
    WP.coeff (fun z:ℂ=>(1-(B:ℂ)*z)⁻¹^h) m=
      (((h.ascFactorial m:ℝ)*B^m/m.factorial:ℝ):ℂ) := by
  unfold WP.coeff
  rw[iteratedDeriv_affine_inv_pow]
  simp only[mul_zero,sub_zero,one_zpow,mul_one]
  push_cast
  rfl
lemma affineInverse_coeff_real (B:ℝ)(h m:ℕ):
    realCoeff (fun z:ℂ=>(1-(B:ℂ)*z)⁻¹^h) m=(h.ascFactorial m:ℝ)*B^m/m.factorial := by
  unfold realCoeff
  rw[affineInverse_coeff_complex,Complex.ofReal_re]
lemma affineInverse_realCoefficients (B:ℝ):RealCoefficients (fun z:ℂ=>(1-(B:ℂ)*z)⁻¹) := by
  intro n
  have he:=affineInverse_coeff_complex B 1 n
  simp only[pow_one] at he
  rw[he,Complex.ofReal_im]
lemma real_powerSeries_power_mono (f g:PowerSeries ℝ)
    (hf:∀m,0≤PowerSeries.coeff m f)(hfg:∀m,PowerSeries.coeff m f≤PowerSeries.coeff m g):
    ∀h m:ℕ,0≤PowerSeries.coeff m (f^h) ∧PowerSeries.coeff m (f^h)≤PowerSeries.coeff m (g^h) := by
  intro h
  induction h with
  | zero =>
    intro m
    constructor
    · rw[pow_zero,PowerSeries.coeff_one]
      split_ifs <;> norm_num
    · rfl
  | succ h ih =>
    intro m
    rw[pow_succ,pow_succ,PowerSeries.coeff_mul,PowerSeries.coeff_mul]
    constructor
    · apply Finset.sum_nonneg
      intro p hp
      exact mul_nonneg (ih p.1).1 (hf p.2)
    · apply Finset.sum_le_sum
      intro p hp
      exact mul_le_mul (ih p.1).2 (hfg p.2) (hf p.2) ((ih p.1).1.trans (ih p.1).2)

lemma harmonicCoeff_one_zero (Y:ℝ)(hY:Y∈Icc 0 y₀):harmonicCoeff Y 1 0=1 := by
  simp[harmonicCoeff,realCoeff,WP.coeff,barH_zero Y hY]
lemma harmonicCoeff_one_geometric_majorant:∃B:ℝ,1≤B ∧∀Y∈Icc (0:ℝ) y₀,∀m:ℕ,harmonicCoeff Y 1 m≤B^m := by
  obtain ⟨c,C,t,hc,hC,ht,hbound⟩:=harmonic_uniform_bounds
  let B:=max 1 (1/c)
  refine ⟨B,le_max_left _ _,?_⟩
  intro Y hY m
  by_cases hm:m=0
  · subst m
    rw[harmonicCoeff_one_zero Y hY,pow_zero]
  have hb:c≤(barH Y 1).re:=by
    have hh:=(hbound Y hY).1
    simpa [harmonicMass,realCoeff,WP.coeff,harmonicPGF,barH_zero Y hY] using hh
  have hp:harmonicMass Y m≤1:=by
    have hs:=harmonicMass_hasSum Y hY
    have hh:=hs.summable.le_tsum m (fun n _=>(harmonicMass_pos Y hY n).le)
    simpa only[hs.tsum_eq] using hh
  have hma:harmonicMass Y m=(barH Y 1).re*harmonicCoeff Y 1 m:=by
    unfold harmonicMass harmonicCoeff
    rw[harmonicPGF_eq_real_mul_inv,realCoeff_const_mul]
    simp only[pow_one]
  have ha:0≤harmonicCoeff Y 1 m:=(harmonicCoeff_pos Y 1 m (by omega) hY).le
  have hprod:c*harmonicCoeff Y 1 m≤1:=
    (mul_le_mul_of_nonneg_right hb ha).trans (by rw[←hma];exact hp)
  calc harmonicCoeff Y 1 m≤1/c:=(le_div_iff₀ hc).mpr (by nlinarith)
       _≤B:=le_max_right _ _
       _≤B^m:=le_self_pow₀ (le_max_left _ _) hm

lemma harmonicCoeff_uniform_majorant:∃B:ℝ,1≤B ∧∀Y∈Icc (0:ℝ) y₀,∀h m:ℕ,
    harmonicCoeff Y h m≤(h.ascFactorial m:ℝ)*B^m/m.factorial := by
  obtain ⟨B,hB,hbound⟩:=harmonicCoeff_one_geometric_majorant
  refine ⟨B,hB,?_⟩
  intro Y hY h m
  let f:=realTaylor (fun z:ℂ=>(barH Y z)⁻¹)
  let g:=realTaylor (fun z:ℂ=>(1-(B:ℂ)*z)⁻¹)
  have hf:∀n,0≤PowerSeries.coeff n f:=by
    intro n
    simpa only[f,realTaylor_coeff,harmonicCoeff,pow_one] using (harmonicCoeff_pos Y 1 n (by omega) hY).le
  have hg (n:ℕ):PowerSeries.coeff n g=B^n:=by
    dsimp only[g]
    rw[realTaylor_coeff]
    have he:=affineInverse_coeff_real B 1 n
    simp only[pow_one,Nat.one_ascFactorial] at he
    rw[he]
    have hn:(n.factorial:ℝ)≠0:=by exact_mod_cast n.factorial_ne_zero
    field_simp
  have hfg:∀n,PowerSeries.coeff n f≤PowerSeries.coeff n g:=by
    intro n
    rw[hg]
    simpa only[f,realTaylor_coeff,harmonicCoeff,pow_one] using hbound Y hY n
  have hpow:=(real_powerSeries_power_mono f g hf hfg h m).2
  have hL:harmonicCoeff Y h m=PowerSeries.coeff m (f^h):=by
    rw[harmonicCoeff_eq_formal Y hY]
    dsimp[f]
    rw[realTaylor_inv ((barH_differentiable Y).analyticAt 0) (by rw[barH_zero Y hY];norm_num) (barH_realCoefficients Y)]
  have hR:PowerSeries.coeff m (g^h)=(h.ascFactorial m:ℝ)*B^m/m.factorial:=by
    have hA:AnalyticAt ℂ (fun z:ℂ=>(1-(B:ℂ)*z)⁻¹) 0:=by
      apply AnalyticAt.inv
      · fun_prop
      · norm_num
    rw[←realTaylor_pow hA (affineInverse_realCoefficients B) h]
    simpa only[realTaylor_coeff] using affineInverse_coeff_real B h m
  rw[←hL,hR] at hpow
  exact hpow
end WP.Analysis
