import WPFormalization.HigherOrder.FirstOrderRemainder
import WPFormalization.Statements.RecursiveRemainderTarget
/-! Exact actual-state predicates used in the all-order remainder induction.
They include all stable positive-complexity states, genus zero and invalid degree tuples.
The final conversion preserves the frozen target and only doubles the common numerical constant. -/

noncomputable section
namespace WP.HigherOrder
open Set PowerSeries

def ProfileOrderRemainderBound (P:PsiTheory) (M L:ℕ) (E:ℝ) : Prop :=
  ∀g:ℕ,∀d:List ℕ,1 ≤ d.length→Stable g d.length→1 ≤ complexity g d.length→
  ∀Y∈Icc (0:ℝ) y₀,
  |profile P g d Y-truncationValue (formalProfile P Y d) L (1/(complexity g d.length:ℝ))| ≤
    E*profileOrderWeight (M:ℝ) L d^(2*L)/(complexity g d.length:ℝ)^L

def ScalarOrderRemainderBound (f:ℕ→ℕ→ℝ→ℝ) (F:ℝ→ℕ→Series)
    (allowed:ℕ→Prop) (M L:ℕ) (E:ℝ) : Prop :=
  ∀g p:ℕ,allowed p→1 ≤ p→Stable g p→1 ≤ complexity g p→∀Y∈Icc (0:ℝ) y₀,
  |f g p Y-truncationValue (F Y p) L (1/(complexity g p:ℝ))| ≤
    E*scalarOrderWeight (M:ℝ) L p^(2*L)/(complexity g p:ℝ)^L

def RemainderStageBound (P:PsiTheory) (M:ℕ) (s:Fin 4) (L:ℕ) (E:ℝ) : Prop :=
  match s.val with
  | 0=>ProfileOrderRemainderBound P M L E
  | 1=>ScalarOrderRemainderBound (cuspCorrection P) (formalCusp P) (fun _=>True) M L E
  | 2=>ScalarOrderRemainderBound (genusCorrection P) (formalGenus P) (fun p=>2 ≤ p) M L E
  | _=>ScalarOrderRemainderBound (genusCorrection P) (formalGenus P) (fun p=>p=1) M L E

lemma profileOrderRemainderBound_mono (P:PsiTheory) (M L:ℕ) :
    Monotone (ProfileOrderRemainderBound P M L) :=by
  intro a b hab ha g d hd hs hh Y hY
  apply (ha g d hd hs hh Y hY).trans
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right hab (by unfold profileOrderWeight;positivity)) (by positivity)

lemma scalarOrderRemainderBound_mono (f:ℕ→ℕ→ℝ→ℝ) (F:ℝ→ℕ→Series)
    (allowed:ℕ→Prop) (M L:ℕ) : Monotone (ScalarOrderRemainderBound f F allowed M L) :=by
  intro a b hab ha g p hp' hp hs hh Y hY
  apply (ha g p hp' hp hs hh Y hY).trans
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right hab (by unfold scalarOrderWeight;positivity)) (by positivity)

lemma remainderStageBound_mono (P:PsiTheory) (M:ℕ) (s:Fin 4) (L:ℕ) :
    Monotone (RemainderStageBound P M s L) :=by
  fin_cases s
  · exact profileOrderRemainderBound_mono P M L
  all_goals exact scalarOrderRemainderBound_mono _ _ _ M L

lemma canonical_first_order_stage_bounds (P:PsiTheory) :
    ∃C:ℝ,∃M₀:ℕ,0<C ∧ 2 ≤ M₀ ∧∀M:ℕ,M₀ ≤ M→∀s,RemainderStageBound P M s 1 C :=by
  obtain ⟨C,M₀,hC,hM₀,hfirst⟩:=canonical_first_order_remainder P
  refine ⟨C,M₀,hC,hM₀,?_⟩
  intro M hM s
  obtain ⟨hp,hs⟩:=hfirst M hM
  have hp':ProfileOrderRemainderBound P M 1 C:=by
    intro g d hd hst hh Y hY
    simpa only[truncationValue,Finset.sum_range_one,formalProfile,PowerSeries.coeff_mk,
      profileCoefficient_zero,pow_zero,mul_one,Nat.mul_one,pow_one] using hp g d hd hst hh Y hY
  have hc':ScalarOrderRemainderBound (cuspCorrection P) (formalCusp P) (fun _=>True) M 1 C:=by
    intro g p _ hp hst hh Y hY
    have h:|cuspCorrection P g p Y-1| ≤ C*scalarOrderWeight (M:ℝ) 1 p^2/(complexity g p:ℝ):=
      (le_add_of_nonneg_right (abs_nonneg _)).trans (hs g p hp hst hh Y hY)
    simpa only[truncationValue,Finset.sum_range_one,formalCusp,PowerSeries.coeff_mk,
      cuspCoefficient_zero,pow_zero,mul_one,Nat.mul_one,pow_one] using h
  have hg':∀allowed:ℕ→Prop,ScalarOrderRemainderBound (genusCorrection P) (formalGenus P) allowed M 1 C:=by
    intro allowed g p _ hp hst hh Y hY
    have h:|genusCorrection P g p Y-1| ≤ C*scalarOrderWeight (M:ℝ) 1 p^2/(complexity g p:ℝ):=
      (le_add_of_nonneg_left (abs_nonneg _)).trans (hs g p hp hst hh Y hY)
    simpa only[truncationValue,Finset.sum_range_one,formalGenus,PowerSeries.coeff_mk,
      genusCoefficient_zero,pow_zero,mul_one,Nat.mul_one,pow_one] using h
  fin_cases s
  · exact hp'
  · exact hc'
  · exact hg' _
  · exact hg' _

lemma truncationValue_at_inverse (f:Series) (L:ℕ) (h:ℝ) :
    truncationValue f L (1/h)=∑j∈Finset.range L,PowerSeries.coeff j f/h^j:=by
  simp only[truncationValue,div_pow,one_pow,mul_one_div]

lemma uniformRecursiveRemainderTarget_of_stage_bounds (P:PsiTheory)
    (C B:ℝ) (M:ℕ) (hC:0<C) (hB:0<B) (hM:2 ≤ M)
    (hs:∀L:ℕ,1 ≤ L→∀s,RemainderStageBound P M s L (C*B^L)) :
    UniformRecursiveRemainderTarget P:=by
  refine ⟨2*C,B,M,by positivity,hB,hM,?_,?_⟩
  · intro g d hd hst hh L hL Y hY
    have hp:=hs L hL 0 g d hd hst hh Y hY
    rw[truncationValue_at_inverse] at hp
    simp only[formalProfile,PowerSeries.coeff_mk] at hp
    apply hp.trans
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by nlinarith[pow_pos hB L] : C*B^L ≤ 2*C*B^L)
        (by unfold profileOrderWeight;positivity)) (by positivity)
  · intro g p hp hst hh L hL Y hY
    have hc:=hs L hL 1 g p trivial hp hst hh Y hY
    have hg:|genusCorrection P g p Y-truncationValue (formalGenus P Y p) L (1/(complexity g p:ℝ))| ≤
        C*B^L*scalarOrderWeight (M:ℝ) L p^(2*L)/(complexity g p:ℝ)^L:=by
      by_cases he:p=1
      · exact hs L hL 3 g p he hp hst hh Y hY
      · exact hs L hL 2 g p (by omega) hp hst hh Y hY
    have hsum:=add_le_add hc hg
    rw[truncationValue_at_inverse,truncationValue_at_inverse] at hsum
    simp only[formalCusp,formalGenus,PowerSeries.coeff_mk] at hsum
    exact hsum.trans_eq (by ring)
end WP.HigherOrder
