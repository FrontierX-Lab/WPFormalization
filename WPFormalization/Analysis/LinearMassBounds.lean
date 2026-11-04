import WPFormalization.Analysis.HarmonicSumProbability
import WPFormalization.Analysis.KernelMomentBounds
import WPFormalization.Statements.Comparison
import WPFormalization.Analysis.ThetaNonnegative

/-! Uniform linear mass bounds for the actual harmonic model, including the
closed parameter interval and all admissible degree tuples. -/
noncomputable section
namespace WP.Analysis
open Set
lemma linearQ_nonnegative (Y:ℝ) (h m l:ℕ) (hh:2≤h) (hY:Y∈Icc 0 y₀):
    0≤linearQ Y h m l := by
  unfold linearQ
  exact div_nonneg (mul_nonneg (theta_nonneg Y hY l)
    (harmonicCoeff_pos Y (h-1) (m-l) (by omega) hY).le)
    (harmonicCoeff_pos Y h m (by omega) hY).le
lemma linearS0_large_parameter_bound (Y:ℝ) (h m:ℕ) (hh:2≤h)
    (hY:Y∈Icc 0 y₀) (hL:(6:ℝ)≤3*h-2*m):
    linearS₀ Y h m≤6*h/(3*h-2*m) := by
  have hhR:(2:ℝ)≤h:=by exact_mod_cast hh
  have hden:0<3*((h:ℝ)-1):=by linarith
  have hLpos:0<3*(h:ℝ)-2*m:=by linarith
  have hsmall:0<(3*(h:ℝ)-2*m-3)/(3*((h:ℝ)-1)):=div_pos (by linarith) hden
  have hlower:(3*(h:ℝ)-2*m-3)/(3*((h:ℝ)-1))*linearS₀ Y h m≤1 := by
    rw [linearS₀,Finset.mul_sum]
    calc
      _ ≤ ∑l∈Finset.range (m+1),linearQ Y h m l*(1-2*((m:ℝ)-l)/(3*((h:ℝ)-1))) := by
        apply Finset.sum_le_sum
        intro l hl
        have hlR:0≤(l:ℝ):=Nat.cast_nonneg _
        have hx:(3*(h:ℝ)-2*m-3)/(3*((h:ℝ)-1))≤1-2*((m:ℝ)-l)/(3*((h:ℝ)-1)) := by
          have hd:3*((h:ℝ)-1)≠0:=hden.ne'
          have hh1:(h:ℝ)-1≠0:=by linarith
          have he:1-2*((m:ℝ)-l)/(3*((h:ℝ)-1))=
              (3*(h:ℝ)-2*m-3+2*l)/(3*((h:ℝ)-1)) := by
            field_simp [hd,hh1]
            <;> ring
          rw [he]
          exact div_le_div_of_nonneg_right (by linarith) hden.le
        nlinarith [mul_le_mul_of_nonneg_right hx (linearQ_nonnegative Y h m l hh hY)]
      _ = 1:=mass_identity Y h m hh hY
  have hS:linearS₀ Y h m≤3*((h:ℝ)-1)/(3*h-2*m-3) := by
    have hb:linearS₀ Y h m≤1/((3*(h:ℝ)-2*m-3)/(3*((h:ℝ)-1))):=
      (le_div_iff₀ hsmall).2 (by nlinarith [hlower])
    simpa only [one_div,inv_div] using hb
  refine hS.trans ?_
  apply (div_le_div_iff₀ (by linarith :0<3*(h:ℝ)-2*m-3) hLpos).2
  nlinarith [mul_nonneg (show 0≤(h:ℝ) by positivity) (show 0≤3*(h:ℝ)-2*m-6 by linarith)]
end WP.Analysis

namespace WP.Analysis
open Set
lemma linearQ_probability (Y:ℝ)(h m l:ℕ)(hh:2≤h)(hY:Y∈Icc 0 y₀):
    linearQ Y h m l = theta Y l*(barH Y 1).re*
      harmonicSumMass Y (h-1) (m-l)/harmonicSumMass Y h m := by
  rw [linearQ,harmonicSumMass_eq_normalized_coeff Y hY,
    harmonicSumMass_eq_normalized_coeff Y hY]
  have hb:(barH Y 1).re≠0:=(barH_one_re_pos Y hY).ne'
  have hA:harmonicCoeff Y h m≠0:=(harmonicCoeff_pos Y h m (by omega) hY).ne'
  have hh':h=h-1+1:=by omega
  have hpow:(barH Y 1).re^h=(barH Y 1).re^(h-1)*(barH Y 1).re:=by
    nth_rw 1 [hh']
    rw [pow_succ]
  rw [hpow]
  field_simp

lemma partial_convolution_mass_le_one (Y:ℝ)(h m:ℕ)(hh:0<h)(hY:Y∈Icc 0 y₀):
    (∑l∈Finset.range (m+1),harmonicSumMass Y h (m-l))≤1 := by
  have he:(∑l∈Finset.range (m+1),harmonicSumMass Y h (m-l))=
      ∑l∈Finset.range (m+1),harmonicSumMass Y h l := by
    exact Finset.sum_range_reflect (fun l=>harmonicSumMass Y h l) (m+1)
  rw [he]
  have hs:=harmonicSumMass_hasSum Y hY h
  exact hs.tsum_eq ▸ hs.summable.sum_le_tsum _ (fun l _=>(harmonicSumMass_pos Y hY h l hh).le)

lemma linearS0_probability_bound (Y:ℝ)(h m:ℕ)(hh:2≤h)(hY:Y∈Icc 0 y₀)
    (C:ℝ)(hC:0≤C)(ht:∀l,theta Y l≤C):
    linearS₀ Y h m≤C/harmonicSumMass Y h m := by
  have hp:=harmonicSumMass_pos Y hY h m (by omega)
  have hb:=barH_one_re_pos Y hY
  have hb1:=barH_one_re_le_one Y hY
  apply (le_div_iff₀ hp).2
  unfold linearS₀
  rw [Finset.sum_mul]
  calc
    _ = (barH Y 1).re*∑l∈Finset.range (m+1),theta Y l*harmonicSumMass Y (h-1) (m-l) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro l hl
      rw [linearQ_probability Y h m l hh hY,div_mul_cancel₀ _ hp.ne']
      ring
    _ ≤ (barH Y 1).re*(C*∑l∈Finset.range (m+1),harmonicSumMass Y (h-1) (m-l)) := by
      apply mul_le_mul_of_nonneg_left _ hb.le
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum (fun l _=>mul_le_mul_of_nonneg_right (ht l)
        (harmonicSumMass_pos Y hY (h-1) (m-l) (by omega)).le)
    _ ≤ (barH Y 1).re*C := by
      apply mul_le_mul_of_nonneg_left _ hb.le
      nlinarith [partial_convolution_mass_le_one Y (h-1) m (by omega) hY]
    _ ≤ C := by nlinarith
end WP.Analysis
namespace WP.Analysis
open Set
lemma linearS0_uniform_square_root : ∃C:ℝ,0<C ∧∀h m:ℕ,2≤h→2*m+1≤3*h→
    ∀Y∈Icc (0:ℝ) y₀,linearS₀ Y h m≤C*Real.sqrt (h:ℝ) := by
  obtain ⟨T,hT⟩:=theta_uniform_bound
  let B:=max T 1
  have hB:0<B:=lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have ht:∀Y∈Icc (0:ℝ) y₀,∀l,theta Y l≤B:=
    fun Y hY l=>(hT Y hY l).trans (le_max_left _ _)
  obtain ⟨c,hc,H,hcentral⟩:=harmonicSumMass_central_lower 1 zero_le_one
  let N:=max H 36
  obtain ⟨d,hd,hfinite⟩:=harmonicSumMass_finite_lower N (2*N) (by dsimp[N];omega)
  let C:=6+B/c+B/d
  have hBc:0<B/c:=div_pos hB hc
  have hBd:0<B/d:=div_pos hB hd
  have hC:0<C:=by dsimp[C];linarith
  refine ⟨C,hC,?_⟩
  intro h m hh hm Y hY
  have hr:0<Real.sqrt (h:ℝ):=Real.sqrt_pos.mpr (by exact_mod_cast (show 0<h by omega))
  have hr1:1≤Real.sqrt (h:ℝ):=by
    calc (1:ℝ)=Real.sqrt 1:=by norm_num
         _ ≤ _:=Real.sqrt_le_sqrt (by exact_mod_cast (show 1≤h by omega))
  have hr2:(Real.sqrt (h:ℝ))^2=h:=Real.sq_sqrt (Nat.cast_nonneg _)
  have hprob:=linearS0_probability_bound Y h m hh hY B hB.le (ht Y hY)
  by_cases hhN:h<N
  · have hmN:m≤2*N:=by omega
    have hpLower:=hfinite h (by omega) (by omega) m hmN Y hY
    have hbound:linearS₀ Y h m≤B/d:=hprob.trans
      (div_le_div_of_nonneg_left hB.le hd hpLower)
    calc _ ≤ B/d:=hbound
         _ ≤ (B/d)*Real.sqrt (h:ℝ):=by nlinarith
         _ ≤ C*Real.sqrt (h:ℝ):=by dsimp[C];nlinarith
  · have hhH:H≤h:=by dsimp[N] at hhN;omega
    have hh36:36≤h:=by dsimp[N] at hhN;omega
    have hmR:2*(m:ℝ)+1≤3*h:=by exact_mod_cast hm
    by_cases hL:3*(h:ℝ)-2*m≤Real.sqrt (h:ℝ)
    · have hcentralArg:|(m:ℝ)-3*(h:ℝ)/2|≤1*Real.sqrt (h:ℝ):=by
        rw [abs_of_nonpos (by linarith : (m:ℝ)-3*(h:ℝ)/2≤0)]
        nlinarith
      have hpLower:=hcentral h hhH (by omega) Y hY m hcentralArg
      have hbound:linearS₀ Y h m≤B/(c/Real.sqrt (h:ℝ)):=hprob.trans
        (div_le_div_of_nonneg_left hB.le (div_pos hc hr) hpLower)
      calc _ ≤ B/(c/Real.sqrt (h:ℝ)):=hbound
           _ = (B/c)*Real.sqrt (h:ℝ):=by field_simp <;> ring
           _ ≤ C*Real.sqrt (h:ℝ):=by dsimp[C];nlinarith
    · have hr6:6≤Real.sqrt (h:ℝ):=by
        calc (6:ℝ)=Real.sqrt 36:=by norm_num
             _ ≤ _:=Real.sqrt_le_sqrt (by exact_mod_cast hh36)
      have hL6:6≤3*(h:ℝ)-2*m:=by linarith
      have hbound:=linearS0_large_parameter_bound Y h m hh hY hL6
      calc _ ≤ 6*h/(3*(h:ℝ)-2*m):=hbound
           _ ≤ 6*Real.sqrt (h:ℝ):=by
             apply (div_le_iff₀ (by linarith :0<3*(h:ℝ)-2*m)).2
             nlinarith
           _ ≤ C*Real.sqrt (h:ℝ):=by dsimp[C];nlinarith
end WP.Analysis
namespace WP.Analysis
open Set
lemma deficit_parameter_identity (g:ℕ)(d:List ℕ)(hh:2≤complexity g d.length)
    (hn:1≤d.length)(hd:d.sum≤dimension g d.length):
    2*deficit g d+2*d.sum+d.length=3*complexity g d.length := by
  unfold deficit dimension complexity at *
  omega

end WP.Analysis
namespace WP
open Analysis

/- Eq.4.21; L=2D+n and the constants are uniform also in the marking count. -/
/- Blueprint label(s): eq:H22
Paper v3: 4.21 [PDF 23]
Status: STATEMENT_FORMALIZED (proofs pending)
-/
@[blueprint "eq:H22"]
theorem linear_mass_bounds : ∃ C : ℝ, 0 < C ∧
    ∀ g : ℕ, ∀ d : List ℕ, 2 ≤ complexity g d.length → 1 ≤ d.length →
    d.sum ≤ dimension g d.length → ∀ Y ∈ Set.Icc 0 y₀,
      linearS₀ Y (complexity g d.length) (deficit g d) ≤ C*Real.sqrt (complexity g d.length) ∧
      (6 ≤ 2*d.sum+d.length →
        linearS₀ Y (complexity g d.length) (deficit g d) ≤
          C*(complexity g d.length)/(2*(d.sum : ℝ)+d.length)) := by
  obtain ⟨B,hB,hbound⟩:=linearS0_uniform_square_root
  let C:=max B 6
  refine ⟨C,lt_of_lt_of_le hB (le_max_left _ _),?_⟩
  intro g d hh hn hd Y hY
  have he:=deficit_parameter_identity g d hh hn hd
  have heR:2*(deficit g d:ℝ)+2*d.sum+d.length=3*complexity g d.length:=by exact_mod_cast he
  have hm:2*deficit g d+1≤3*complexity g d.length:=by omega
  constructor
  · exact (hbound _ _ hh hm Y hY).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.sqrt_nonneg _))
  · intro hL
    have hLR:(6:ℝ)≤2*d.sum+d.length:=by exact_mod_cast hL
    have hlarge:=linearS0_large_parameter_bound Y _ _ hh hY (show (6:ℝ)≤3*complexity g d.length-2*deficit g d by linarith)
    have hden:3*(complexity g d.length:ℝ)-2*deficit g d=2*d.sum+d.length:=by linarith
    rw [hden] at hlarge
    exact hlarge.trans (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_right B 6) (Nat.cast_nonneg _)) (by linarith))
end WP
