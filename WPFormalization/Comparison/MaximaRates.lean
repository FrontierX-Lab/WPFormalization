import WPFormalization.Comparison.TypedStates
import WPFormalization.Weighted.ModelValidity
import WPFormalization.Comparison.ClippedMaxima
import WPFormalization.Comparison.RecordGrowth
import WPFormalization.Analysis.TerminalUpper
import WPFormalization.Intersection.ProfileMonotone
noncomputable section
namespace WP
lemma clippedWeight_ge_one (c:ℝ)(d:List ℕ):1 ≤ clippedWeight c d:=by
  rw [clippedWeight_phi]
  have hp:(1:ℝ) ≤ 4^(zeros d):=one_le_pow₀ (by norm_num)
  have hφ:=clippedPhi_ge_one c (inactive d)
  nlinarith
lemma clippedComplexityMaximum_nonneg (P:PsiTheory)(c:ℝ)(h:ℕ):
    0 ≤ clippedComplexityMaximum P c h:=by
  by_cases hh:h=0
  · subst h;rw[clippedComplexityMaximum_zero]
  · obtain ⟨g,d,hn,hs,hd,he,Y,hY,hmax⟩:=clippedComplexityMaximum_attained P c h (by omega)
    rw [hmax]
    unfold ratio
    exact div_nonneg (div_nonneg (normalized_nonneg_nonempty P g d hn Y hY)
      (model_pos g d Y hs hY).le) (clippedWeight_pos c d).le
lemma clippedComplexityMaximum_rates_nonempty (P:PsiTheory)(c:ℝ):
    (Analysis.exponentialRates (clippedComplexityMaximum P c)).Nonempty:=by
  obtain ⟨C,hC,hbound⟩:=Analysis.ratio_uniform_global_upper P
  refine ⟨C,hC.le,1,by norm_num,?_⟩
  intro h
  simp only[one_mul]
  by_cases hh:h=0
  · subst h
    rw [clippedComplexityMaximum_zero]
    positivity
  · obtain ⟨g,d,hn,hs,hd,he,Y,hY,hmax⟩:=clippedComplexityMaximum_attained P c h (by omega)
    rw [hmax]
    have hR:0 ≤ ratio P g d Y:=by
      unfold ratio
      exact div_nonneg (normalized_nonneg_nonempty P g d hn Y hY) (model_pos g d Y hs hY).le
    calc
      _ ≤ ratio P g d Y:=div_le_self hR (clippedWeight_ge_one c d)
      _ ≤ Real.exp (C*complexity g d.length):=hbound g d hs hd Y hY
      _ = _:=by rw[he]
end WP
namespace WP
lemma exists_pivot_choice (d:List ℕ)(hn:1 ≤ d.length):
    ∃p:ℕ,∃t:List ℕ,d.Perm (p::t) ∧ PivotChoice p t:=by
  by_cases hbig:∃k∈d,2 ≤ k
  · obtain ⟨k,hk,hk2⟩:=hbig
    exact ⟨k,d.erase k,List.perm_cons_erase hk,Or.inl hk2⟩
  · by_cases hone:1∈d
    · refine ⟨1,d.erase 1,List.perm_cons_erase hone,Or.inr (Or.inl ⟨rfl,?_⟩)⟩
      intro k hk
      have hn2:¬2 ≤ k:=fun h=>hbig ⟨k,List.mem_of_mem_erase hk,h⟩
      omega
    · have hz:∀k∈d,k=0:=by
        intro k hk
        have hn2:¬2 ≤ k:=fun h=>hbig ⟨k,hk,h⟩
        have hn1:k≠1:=fun h=>hone (h▸hk)
        omega
      cases d with
      | nil => simp at hn
      | cons p t =>
        have hp:p=0:=hz p (by simp)
        subst p
        exact ⟨0,t,List.Perm.refl _,Or.inr (Or.inr ⟨rfl,fun k hk=>hz k (by simp[hk])⟩)⟩
end WP
