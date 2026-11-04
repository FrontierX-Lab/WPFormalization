import WPFormalization.Analysis.TerminalUpper
import WPFormalization.Intersection.TerminalLower
import WPFormalization.Statements.Comparison

noncomputable section
namespace WP

/- Lemma 5.2, all three clauses. -/
/- Blueprint label(s): lem:terminal
Paper v3: 5.2 [PDF 24]
Status: INTERFACE_STATEMENT; geometric realization BLOCKED
-/
@[blueprint "lem:terminal"]
theorem terminal_bounds (P : PsiTheory) :
    ∃ cψ Cψ c C : ℝ, 0 < cψ ∧ 0 < Cψ ∧ 0 < c ∧ 0 < C ∧
    (∀ g : ℕ, ∀ d : List ℕ, Stable g d.length → d.sum = dimension g d.length →
      cψ*(2/3 : ℝ)^(zeros d) ≤ pureC P g d ∧ pureC P g d ≤ Cψ*2^(zeros d)) ∧
    (∀ g : ℕ, ∀ d : List ℕ, 1 ≤ d.length → Stable g d.length →
      d.sum ≤ dimension g d.length → ∀ Y ∈ Set.Icc 0 y₀,
        (Terminal g d → c*Real.exp (-C*zeros d) ≤ ratio P g d Y) ∧
        ratio P g d Y ≤ Real.exp (C*complexity g d.length)) := by
  obtain ⟨cL,CL,hcL,hCL,hLower⟩:=terminal_ratio_lower P
  obtain ⟨B,hB,hUpper⟩:=Analysis.ratio_uniform_global_upper P
  let C:=max CL B
  have hC:0<C:=lt_of_lt_of_le hCL (le_max_left _ _)
  refine ⟨1/6,1,cL,C,by norm_num,by norm_num,hcL,hC,?_,?_⟩
  · intro g d hs hd
    have hp:=pureC_zero_bounds P g d hs hd
    simpa only [zeros,←count_zero_filter_length,one_mul] using hp
  · intro g d hn hs hd Y hY
    constructor
    · intro ht
      have hl:=hLower g d hn hs hd Y hY ht
      have hcompare:cL*Real.exp (-C*(zeros d:ℝ)) ≤ cL*Real.exp (-CL*(d.count 0:ℝ)):=by
        apply mul_le_mul_of_nonneg_left _ hcL.le
        apply Real.exp_le_exp.mpr
        have hcnt:zeros d=d.count 0:=by rw[zeros,←count_zero_filter_length]
        rw [hcnt]
        have hle:CL ≤ C:=le_max_left _ _
        nlinarith [show 0 ≤ (d.count 0:ℝ) from Nat.cast_nonneg _]
      exact hcompare.trans hl
    · exact (hUpper g d hs hd Y hY).trans (Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_right (le_max_right _ _) (Nat.cast_nonneg _)))


end WP
