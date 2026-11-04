import WPFormalization.Analysis.HarmonicSumProbability
import WPFormalization.Analysis.HarmonicMass
noncomputable section
namespace WP.Analysis
open Set
lemma harmonicCoeff_add_convolution (Y:ℝ)(hY:Y∈Icc 0 y₀)(h₁ h₂ m:ℕ):
    (∑k∈Finset.range (m+1),harmonicCoeff Y h₁ k*harmonicCoeff Y h₂ (m-k))=
      harmonicCoeff Y (h₁+h₂) m:=by
  simp_rw [harmonicCoeff_eq_formal Y hY]
  rw [pow_add,PowerSeries.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
lemma harmonicCoeff_uniform_first_three : ∃c:ℝ,0<c ∧ c ≤ 1 ∧
    ∀Y∈Icc (0:ℝ) y₀,∀m:ℕ,m ≤ 2→c ≤ harmonicCoeff Y 1 m:=by
  obtain ⟨c,hc,hbound⟩:=harmonicSumMass_finite_lower 1 2 (by omega)
  refine ⟨min c 1,lt_min hc zero_lt_one,min_le_right _ _,?_⟩
  intro Y hY m hm
  have hl:=hbound 1 (by omega) (by omega) m hm Y hY
  rw [harmonicSumMass_eq_normalized_coeff Y hY,pow_one] at hl
  have hb:=barH_one_re_le_one Y hY
  have hp:0 ≤ harmonicCoeff Y 1 m:=(harmonicCoeff_pos Y 1 m (by omega) hY).le
  exact (min_le_left _ _).trans (hl.trans (by nlinarith))
lemma harmonicCoeff_uniform_exponential_lower : ∃c:ℝ,0<c ∧ c ≤ 1 ∧
    ∀h:ℕ,1 ≤ h→∀m:ℕ,m ≤ 2*h→∀Y∈Icc (0:ℝ) y₀,c^h ≤ harmonicCoeff Y h m:=by
  obtain ⟨c,hc,hc1,hbase⟩:=harmonicCoeff_uniform_first_three
  refine ⟨c,hc,hc1,?_⟩
  intro h
  induction h with
  | zero => intro hh;omega
  | succ h ih =>
    intro hh m hm Y hY
    by_cases hh0:h=0
    · subst h
      simpa only [zero_add,pow_one] using hbase Y hY m (by simpa using hm)
    · have hhpos:1 ≤ h:=by omega
      let j:=min m 2
      have hjm:j ≤ m:=min_le_left _ _
      have hj2:j ≤ 2:=min_le_right _ _
      have hmj:m-j ≤ 2*h:=by dsimp[j];omega
      have hlo:=ih hhpos (m-j) hmj Y hY
      have hfirst:=hbase Y hY j hj2
      have hsingle:harmonicCoeff Y 1 j*harmonicCoeff Y h (m-j) ≤ harmonicCoeff Y (1+h) m:=by
        rw [←harmonicCoeff_add_convolution Y hY]
        apply Finset.single_le_sum (f:=fun k=>harmonicCoeff Y 1 k*harmonicCoeff Y h (m-k)) (a:=j)
        · intro k hk
          exact mul_nonneg (harmonicCoeff_pos Y 1 k (by omega) hY).le
            (harmonicCoeff_pos Y h (m-k) (by omega) hY).le
        · exact Finset.mem_range.mpr (by omega)
      have hprod:c*c^h ≤ harmonicCoeff Y 1 j*harmonicCoeff Y h (m-j):=
        mul_le_mul hfirst hlo (pow_nonneg hc.le _) (harmonicCoeff_pos Y 1 j (by omega) hY).le
      simpa only [pow_succ,mul_comm c,add_comm 1 h] using hprod.trans hsingle
end WP.Analysis
