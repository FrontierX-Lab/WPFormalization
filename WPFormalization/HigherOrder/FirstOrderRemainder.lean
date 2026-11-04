import WPFormalization.HigherOrder.LargeWeightScales
import WPFormalization.HigherOrder.SmallWeightRegion
/-! The complete order-one base of C.3, with one constant for every
stable positive-marking state and every nonnegative degree tuple.
The small-weight region uses the actual growing-marking C.6 theorem;
the complementary region uses the actual C.4 large-weight bound.
Invalid tuples and g=0 scalar states are included. No arbitrary-order
remainder recurrence or path compatibility is asserted here. -/
noncomputable section
open Set
namespace WP.HigherOrder
lemma canonical_first_order_remainder (P:PsiTheory) :
    ∃C:ℝ,∃M₀:ℕ,0<C ∧ 2 ≤ M₀ ∧∀M:ℕ,M₀ ≤ M→
    (∀g:ℕ,∀d:List ℕ,1 ≤ d.length→Stable g d.length→1 ≤ complexity g d.length→
      ∀Y∈Icc (0:ℝ) y₀,
      |profile P g d Y-1| ≤ C*profileOrderWeight (M:ℝ) 1 d^2/(complexity g d.length:ℝ)) ∧
    (∀g p:ℕ,1 ≤ p→Stable g p→1 ≤ complexity g p→∀Y∈Icc (0:ℝ) y₀,
      |cuspCorrection P g p Y-1|+|genusCorrection P g p Y-1| ≤
        C*scalarOrderWeight (M:ℝ) 1 p^2/(complexity g p:ℝ)) :=by
  obtain ⟨C,hC,H,hfirst⟩:=growing_marking_first_order P 4 (by norm_num)
  let δ:ℝ:=1/((H:ℝ)+2)
  have hden:0<(H:ℝ)+2:=by positivity
  have hδ:0<δ:=by dsimp[δ];positivity
  have hδ1:δ ≤ 1:=by dsimp[δ];exact (div_le_one hden).2 (by linarith[Nat.cast_nonneg (α:=ℝ) H])
  obtain ⟨Cl,Bl,M₀,hCl,hBl,hM₀,hlarge⟩:=canonical_large_weight_remainders_all_scales P δ hδ
  have hparent (g p:ℕ) (hp:1 ≤ p) (hh:1 ≤ complexity g p) (S:ℝ)
      (hS:(p:ℝ)+2 ≤ S) (hsmall:S^2/(complexity g p:ℝ)<δ) :
      H ≤ complexity g p ∧ (p:ℝ) ≤ 4*Real.sqrt (complexity g p:ℝ):=by
    have hhR:(0:ℝ)<complexity g p:=by exact_mod_cast (show 0<complexity g p by omega)
    have hS1:1 ≤ S:=by
      have hpR:(1:ℝ) ≤ p:=by exact_mod_cast hp
      linarith
    have hSq:1 ≤ S^2:=by nlinarith
    have hprod:S^2*((H:ℝ)+2)<(complexity g p:ℝ):=by
      simpa only[one_mul] using (div_lt_div_iff₀ hhR hden).mp hsmall
    have hH:((H:ℝ)+2)<(complexity g p:ℝ):=lt_of_le_of_lt (by nlinarith) hprod
    have hHnat:H ≤ complexity g p:=by exact_mod_cast (by linarith:H ≤ (complexity g p:ℝ))
    have hroot:=(small_weight_child_geometry (complexity g p:ℝ) S (complexity g p:ℝ) p 1 p
      hhR hp (by omega) (by simpa only[Nat.cast_one,mul_one] using hS)
      (hsmall.trans_le hδ1) (by norm_num) (by omega)).2
    exact ⟨hHnat,hroot⟩
  refine ⟨Cl*Bl+C,M₀,by positivity,hM₀,?_⟩
  intro M hM
  have hMtwo:2 ≤ M:=hM₀.trans hM
  have hMR:(2:ℝ) ≤ M:=by exact_mod_cast hMtwo
  obtain ⟨hlargeP,hlargeS⟩:=hlarge M hM
  constructor
  · intro g d hd hs hh Y hY
    have hhR:(0:ℝ)<complexity g d.length:=by exact_mod_cast (show 0<complexity g d.length by omega)
    have hS0:0 ≤ profileOrderWeight (M:ℝ) 1 d:=by unfold profileOrderWeight;positivity
    by_cases hδlarge:δ ≤ profileOrderWeight (M:ℝ) 1 d^2/(complexity g d.length:ℝ)
    · have hhg:=hlargeP g d hd hs hh 1 (by omega) Y hY hδlarge
      simp only[Finset.sum_range_one,pow_zero,div_one,profileCoefficient_zero,pow_one,Nat.mul_one] at hhg
      exact hhg.trans (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)) hhR.le)
    · have hsmall:=lt_of_not_ge hδlarge
      have hS:(d.length:ℝ)+2 ≤ profileOrderWeight (M:ℝ) 1 d:=by
        unfold profileOrderWeight
        simp only[Nat.cast_one,mul_one]
        linarith[Nat.cast_nonneg (α:=ℝ) d.sum]
      obtain ⟨hH,hpRoot⟩:=hparent g d.length hd hh _ hS hsmall
      obtain ⟨hprofile,hscalar⟩:=hfirst g d.length hd hH hpRoot Y hY
      have hpf:=hprofile d rfl
      rw[abs_sub_comm,abs_of_nonneg hpf.1]
      apply (hpf.2.trans (min_le_right _ _)).trans
      apply div_le_div_of_nonneg_right _ hhR.le
      have hD:(d.sum:ℝ) ≤ profileOrderWeight (M:ℝ) 1 d:=by
        unfold profileOrderWeight
        simp only[Nat.cast_one,mul_one]
        linarith[Nat.cast_nonneg (α:=ℝ) d.length]
      have hDp:(d.sum:ℝ)+d.length+1 ≤ profileOrderWeight (M:ℝ) 1 d:=by
        unfold profileOrderWeight
        simp only[Nat.cast_one,mul_one]
        linarith
      have hprod:=(mul_le_mul hD hDp (by positivity:(0:ℝ) ≤ (d.sum:ℝ)+d.length+1) hS0)
      have hCp:=mul_le_mul_of_nonneg_left hprod hC.le
      have hrest:=mul_le_mul_of_nonneg_right (show C ≤ Cl*Bl+C by nlinarith[mul_pos hCl hBl]) (sq_nonneg (profileOrderWeight (M:ℝ) 1 d))
      nlinarith
  · intro g p hp hs hh Y hY
    have hhR:(0:ℝ)<complexity g p:=by exact_mod_cast (show 0<complexity g p by omega)
    have hS0:0 ≤ scalarOrderWeight (M:ℝ) 1 p:=by unfold scalarOrderWeight;positivity
    by_cases hδlarge:δ ≤ scalarOrderWeight (M:ℝ) 1 p^2/(complexity g p:ℝ)
    · have hhg:=hlargeS g p hp hs hh 1 (by omega) Y hY hδlarge
      simp only[Finset.sum_range_one,pow_zero,div_one,cuspCoefficient_zero,genusCoefficient_zero,pow_one,Nat.mul_one] at hhg
      exact hhg.trans (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)) hhR.le)
    · have hsmall:=lt_of_not_ge hδlarge
      have hS:(p:ℝ)+2 ≤ scalarOrderWeight (M:ℝ) 1 p:=by
        unfold scalarOrderWeight
        simp only[Nat.cast_one,mul_one]
        linarith
      obtain ⟨hH,hpRoot⟩:=hparent g p hp hh _ hS hsmall
      have he:=(hfirst g p hp hH hpRoot Y hY).2
      apply he.trans
      apply div_le_div_of_nonneg_right _ hhR.le
      have hp1:(1:ℝ) ≤ p:=by exact_mod_cast hp
      have hS1:1 ≤ scalarOrderWeight (M:ℝ) 1 p:=by linarith
      have hpoly:(p:ℝ)+1 ≤ scalarOrderWeight (M:ℝ) 1 p^2:=by nlinarith
      have hc:=mul_le_mul_of_nonneg_left hpoly hC.le
      have hl:=mul_le_mul_of_nonneg_right (show C ≤ Cl*Bl+C by nlinarith[mul_pos hCl hBl]) (sq_nonneg (scalarOrderWeight (M:ℝ) 1 p))
      exact hc.trans hl
end WP.HigherOrder
