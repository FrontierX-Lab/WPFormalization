import WPFormalization.Statements.CoefficientBounds
import WPFormalization.Marked.UniformCorrectionBounds
/-! The actual large-weight branch of the finite-genus remainders in C.3.
All three errors use the actual canonical coefficients and common C/B/M,
chosen before genus, marking count, degree tuple, order and parameter.
The hypothesis δ≥δ₀ selects this branch; the small-weight remainder
induction, arbitrary-path compatibility and finite-data closure are separate. -/
noncomputable section
namespace WP.HigherOrder

lemma finite_expansion_large_weight_bound (x:ℝ) (a:ℕ→ℝ) (L:ℕ)
    (X C B δ₀ δ:ℝ) (hX:0 ≤ X) (hC:0 ≤ C) (hB:0 ≤ B) (hδ₀:0<δ₀) (hδ:δ₀ ≤ δ)
    (hx:|x| ≤ X) (ha:∀j:ℕ,j<L→|a j| ≤ C*B^j*δ^j) :
    |x-∑j∈Finset.range L,a j| ≤
      (X+C)*(2*max B δ₀⁻¹)^L*δ^L := by
  let R:=max B δ₀⁻¹
  have hR0:0 ≤ R:=hB.trans (le_max_left _ _)
  have hδ0:0 ≤ δ:=hδ₀.le.trans hδ
  have hRδ:1 ≤ R*δ:=by
    have hh:=mul_le_mul_of_nonneg_right (le_max_right B δ₀⁻¹) hδ₀.le
    have hh':=mul_le_mul_of_nonneg_left hδ hR0
    rw[inv_mul_cancel₀ hδ₀.ne'] at hh
    exact hh.trans hh'
  have hp:1 ≤ (R*δ)^L:=one_le_pow₀ hRδ
  have hterm (j:ℕ) (hj:j∈Finset.range L) : |a j| ≤ C*(R*δ)^L:=by
    have hpow:(B*δ)^j ≤ (R*δ)^L:=
      (pow_le_pow_left₀ (mul_nonneg hB hδ0)
        (mul_le_mul_of_nonneg_right (le_max_left _ _) hδ0) j).trans
          (pow_le_pow_right₀ hRδ (Finset.mem_range.mp hj).le)
    calc |a j| ≤ C*B^j*δ^j:=ha j (Finset.mem_range.mp hj)
      _=C*(B*δ)^j:=by rw[mul_pow];ring
      _ ≤ _:=mul_le_mul_of_nonneg_left hpow hC
  have hL:(L:ℝ) ≤ (2:ℝ)^L:=by exact_mod_cast (Nat.le_of_lt L.lt_two_pow_self)
  have hTwo:1 ≤ (2:ℝ)^L:=one_le_pow₀ (by norm_num)
  have hConst:X+(L:ℝ)*C ≤ (X+C)*(2:ℝ)^L:=by
    have hhX:=mul_le_mul_of_nonneg_left hTwo hX
    have hhC:=mul_le_mul_of_nonneg_right hL hC
    nlinarith
  calc
    _ ≤ |x|+|∑j∈Finset.range L,a j|:=abs_sub _ _
    _ ≤ X+∑j∈Finset.range L,|a j|:=add_le_add hx (Finset.abs_sum_le_sum_abs _ _)
    _ ≤ X+∑j∈Finset.range L,C*(R*δ)^L:=add_le_add_right (Finset.sum_le_sum hterm) X
    _=X+(L:ℝ)*(C*(R*δ)^L):=by simp only[Finset.sum_const,Finset.card_range,nsmul_eq_mul]
    _ ≤ (X+(L:ℝ)*C)*(R*δ)^L:=by
      have hh:=mul_le_mul_of_nonneg_left hp hX
      nlinarith
    _ ≤ ((X+C)*(2:ℝ)^L)*(R*δ)^L:=mul_le_mul_of_nonneg_right hConst (pow_nonneg (mul_nonneg hR0 hδ0) _)
    _=_:=by dsimp[R];rw[mul_pow,mul_pow];ring
lemma canonical_real_coefficient_bounds (P:PsiTheory) :
    ∃ C B:ℝ, ∃ M:ℕ,0<C ∧ 0<B ∧ 2 ≤ M ∧
    (∀j:ℕ,∀d:List ℕ,1 ≤ d.length→∀Y∈Set.Icc (0:ℝ) y₀,
      |profileCoefficient P Y d j| ≤ C*B^j*profileOrderWeight (M:ℝ) j d^(2*j)) ∧
    (∀j p:ℕ,1 ≤ p→∀Y∈Set.Icc (0:ℝ) y₀,
      |cuspCoefficient P Y p j|+|genusCoefficient P Y p j| ≤
        C*B^j*scalarOrderWeight (M:ℝ) j p^(2*j)) := by
  obtain ⟨Ω,R,C,B,M,hΩ,hΩv,hcover,hC,hB,hM,hR,hunit,hraw,hR0,hR',hkernel,
      hprofA,hscalA,hprofR,hscalR,hprofB,hscalB⟩ :=
    ComplexCanonical.canonicalCoefficientBoundsTarget_proof P
  refine ⟨C,B,M,hC,hB,hM,?_,?_⟩
  · intro j d hd Y hY
    have hh:=hprofB j d hd (Y:ℂ) (hcover Y hY)
    rw[hprofR j d hd Y hY,Complex.norm_real,Real.norm_eq_abs] at hh
    exact hh
  · intro j p hp Y hY
    have hh:=hscalB j p hp (Y:ℂ) (hcover Y hY)
    rw[(hscalR j p hp Y hY).1,(hscalR j p hp Y hY).2,
      Complex.norm_real,Complex.norm_real,Real.norm_eq_abs,Real.norm_eq_abs] at hh
    exact hh

lemma profile_truncation_term_bound (P:PsiTheory) (Y:ℝ) (d:List ℕ)
    (C B M h:ℝ) (L j:ℕ) (hC:0 ≤ C) (hB:0 ≤ B) (hM:0 ≤ M) (hh:0<h) (hj:j ≤ L)
    (hcoef:|profileCoefficient P Y d j| ≤ C*B^j*profileOrderWeight M j d^(2*j)) :
    |profileCoefficient P Y d j/h^j| ≤ C*B^j*(profileOrderWeight M L d^2/h)^j := by
  have hSj:profileOrderWeight M j d ≤ profileOrderWeight M L d:=by
    have hjR:(j:ℝ) ≤ L:=by exact_mod_cast hj
    have hm:=mul_le_mul_of_nonneg_left hjR hM
    unfold profileOrderWeight
    linarith
  have hS0:0 ≤ profileOrderWeight M j d:=by unfold profileOrderWeight;positivity
  have hS:profileOrderWeight M j d^(2*j) ≤ profileOrderWeight M L d^(2*j):=
    pow_le_pow_left₀ hS0 hSj _
  rw[abs_div,abs_of_pos (pow_pos hh j),div_pow,←pow_mul]
  calc
    _ ≤ (C*B^j*profileOrderWeight M j d^(2*j))/h^j:=
      div_le_div_of_nonneg_right hcoef (pow_nonneg hh.le j)
    _ ≤ (C*B^j*profileOrderWeight M L d^(2*j))/h^j:=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hS (mul_nonneg hC (pow_nonneg hB _)))
        (pow_nonneg hh.le j)
    _=_:=by ring

lemma profile_large_weight_remainder (P:PsiTheory) (δ₀:ℝ) (hδ₀:0<δ₀) :
    ∃ C B:ℝ, ∃ M:ℕ,0<C ∧ 0<B ∧ 2 ≤ M ∧
      ∀g:ℕ,∀d:List ℕ,1 ≤ d.length→Stable g d.length→1 ≤ complexity g d.length→
      ∀L:ℕ,1 ≤ L→∀Y∈Set.Icc (0:ℝ) y₀,
      δ₀ ≤ profileOrderWeight (M:ℝ) L d^2/(complexity g d.length:ℝ)→
      |profile P g d Y-∑j∈Finset.range L,profileCoefficient P Y d j/(complexity g d.length:ℝ)^j| ≤
        C*B^L*profileOrderWeight (M:ℝ) L d^(2*L)/(complexity g d.length:ℝ)^L := by
  obtain ⟨C,B,M,hC,hB,hM,hcoef,hscalar⟩:=canonical_real_coefficient_bounds P
  refine ⟨1+C,2*max B δ₀⁻¹,M,by positivity,by positivity,hM,?_⟩
  intro g d hd hs hh L hL Y hY hδ
  have hhR:(0:ℝ)<complexity g d.length:=by exact_mod_cast (show 0<complexity g d.length by omega)
  have hp:|profile P g d Y| ≤ 1:=by
    obtain ⟨hn,hp⟩:=(profile_monotone P g d hs 0 (by omega) Y hY).2
    simpa only[abs_of_nonneg hn] using hp
  have hg:=finite_expansion_large_weight_bound (profile P g d Y)
    (fun j=>profileCoefficient P Y d j/(complexity g d.length:ℝ)^j) L
    1 C B δ₀ (profileOrderWeight (M:ℝ) L d^2/(complexity g d.length:ℝ))
    (by norm_num) hC.le hB.le hδ₀ hδ hp
    (fun j hj=>profile_truncation_term_bound P Y d C B (M:ℝ) _ L j hC.le hB.le
      (Nat.cast_nonneg _) hhR hj.le (hcoef j d hd Y hY))
  simpa only[div_pow,←pow_mul,mul_div_assoc] using hg
lemma scalar_truncation_term_bound (u C B M h:ℝ) (p L j:ℕ)
    (hC:0 ≤ C) (hB:0 ≤ B) (hM:0 ≤ M) (hh:0<h) (hj:j ≤ L)
    (hcoef:|u| ≤ C*B^j*scalarOrderWeight M j p^(2*j)) :
    |u/h^j| ≤ C*B^j*(scalarOrderWeight M L p^2/h)^j := by
  have hSj:scalarOrderWeight M j p ≤ scalarOrderWeight M L p:=by
    have hjR:(j:ℝ) ≤ L:=by exact_mod_cast hj
    have hm:=mul_le_mul_of_nonneg_left hjR hM
    unfold scalarOrderWeight
    linarith
  have hS0:0 ≤ scalarOrderWeight M j p:=by unfold scalarOrderWeight;positivity
  have hS:scalarOrderWeight M j p^(2*j) ≤ scalarOrderWeight M L p^(2*j):=
    pow_le_pow_left₀ hS0 hSj _
  rw[abs_div,abs_of_pos (pow_pos hh j),div_pow,←pow_mul]
  calc
    _ ≤ (C*B^j*scalarOrderWeight M j p^(2*j))/h^j:=
      div_le_div_of_nonneg_right hcoef (pow_nonneg hh.le j)
    _ ≤ (C*B^j*scalarOrderWeight M L p^(2*j))/h^j:=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hS (mul_nonneg hC (pow_nonneg hB _)))
        (pow_nonneg hh.le j)
    _=_:=by ring

lemma canonical_large_weight_remainders (P:PsiTheory) (δ₀:ℝ) (hδ₀:0<δ₀) :
    ∃ C B:ℝ, ∃ M:ℕ,0<C ∧ 0<B ∧ 2 ≤ M ∧
      (∀g:ℕ,∀d:List ℕ,1 ≤ d.length→Stable g d.length→1 ≤ complexity g d.length→
      ∀L:ℕ,1 ≤ L→∀Y∈Set.Icc (0:ℝ) y₀,
      δ₀ ≤ profileOrderWeight (M:ℝ) L d^2/(complexity g d.length:ℝ)→
      |profile P g d Y-∑j∈Finset.range L,profileCoefficient P Y d j/(complexity g d.length:ℝ)^j| ≤
        C*B^L*profileOrderWeight (M:ℝ) L d^(2*L)/(complexity g d.length:ℝ)^L) ∧
      (∀g p:ℕ,1 ≤ p→Stable g p→1 ≤ complexity g p→
      ∀L:ℕ,1 ≤ L→∀Y∈Set.Icc (0:ℝ) y₀,
      δ₀ ≤ scalarOrderWeight (M:ℝ) L p^2/(complexity g p:ℝ)→
      |cuspCorrection P g p Y-∑j∈Finset.range L,cuspCoefficient P Y p j/(complexity g p:ℝ)^j|+
      |genusCorrection P g p Y-∑j∈Finset.range L,genusCoefficient P Y p j/(complexity g p:ℝ)^j| ≤
        C*B^L*scalarOrderWeight (M:ℝ) L p^(2*L)/(complexity g p:ℝ)^L) := by
  obtain ⟨C,B,M,hC,hB,hM,hcoef,hscalar⟩:=canonical_real_coefficient_bounds P
  obtain ⟨X₀,hX₀,hXbound⟩:=scalar_corrections_abs_uniform P
  let X:=max 1 X₀
  have hX:0<X:=lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  let B':=2*max B δ₀⁻¹
  have hB':0<B':=by dsimp[B'];positivity
  refine ⟨2*(X+C),B',M,by positivity,hB',hM,?_,?_⟩
  · intro g d hd hs hh L hL Y hY hδ
    have hhR:(0:ℝ)<complexity g d.length:=by exact_mod_cast (show 0<complexity g d.length by omega)
    have hp:|profile P g d Y| ≤ X:=by
      obtain ⟨hn,hp⟩:=(profile_monotone P g d hs 0 (by omega) Y hY).2
      rw[abs_of_nonneg hn]
      exact hp.trans (le_max_left _ _)
    have hg:=finite_expansion_large_weight_bound (profile P g d Y)
      (fun j=>profileCoefficient P Y d j/(complexity g d.length:ℝ)^j) L
      X C B δ₀ (profileOrderWeight (M:ℝ) L d^2/(complexity g d.length:ℝ))
      hX.le hC.le hB.le hδ₀ hδ hp
      (fun j hj=>profile_truncation_term_bound P Y d C B (M:ℝ) _ L j hC.le hB.le
        (Nat.cast_nonneg _) hhR hj.le (hcoef j d hd Y hY))
    have hhg:(X+C)*B'^L*(profileOrderWeight (M:ℝ) L d^2/(complexity g d.length:ℝ))^L ≤
        (2*(X+C))*B'^L*(profileOrderWeight (M:ℝ) L d^2/(complexity g d.length:ℝ))^L:=by
      apply mul_le_mul_of_nonneg_right
      · apply mul_le_mul_of_nonneg_right (by linarith) (pow_nonneg hB'.le _)
      · positivity
    exact (hg.trans hhg).trans_eq (by rw[div_pow,←pow_mul];ring)
  · intro g p hp hs hh L hL Y hY hδ
    have hhR:(0:ℝ)<complexity g p:=by exact_mod_cast (show 0<complexity g p by omega)
    have hx:=hXbound g p hp hs Y hY
    have hcX:|cuspCorrection P g p Y| ≤ X:=
      (le_add_of_nonneg_right (abs_nonneg _)).trans (hx.trans (le_max_right _ _))
    have hgX:|genusCorrection P g p Y| ≤ X:=
      (le_add_of_nonneg_left (abs_nonneg _)).trans (hx.trans (le_max_right _ _))
    have hcCoef (j:ℕ):|cuspCoefficient P Y p j| ≤ C*B^j*scalarOrderWeight (M:ℝ) j p^(2*j):=
      (le_add_of_nonneg_right (abs_nonneg _)).trans (hscalar j p hp Y hY)
    have hgCoef (j:ℕ):|genusCoefficient P Y p j| ≤ C*B^j*scalarOrderWeight (M:ℝ) j p^(2*j):=
      (le_add_of_nonneg_left (abs_nonneg _)).trans (hscalar j p hp Y hY)
    have hc:=finite_expansion_large_weight_bound (cuspCorrection P g p Y)
      (fun j=>cuspCoefficient P Y p j/(complexity g p:ℝ)^j) L
      X C B δ₀ (scalarOrderWeight (M:ℝ) L p^2/(complexity g p:ℝ))
      hX.le hC.le hB.le hδ₀ hδ hcX
      (fun j hj=>scalar_truncation_term_bound _ C B (M:ℝ) _ p L j hC.le hB.le
        (Nat.cast_nonneg _) hhR hj.le (hcCoef j))
    have hg:=finite_expansion_large_weight_bound (genusCorrection P g p Y)
      (fun j=>genusCoefficient P Y p j/(complexity g p:ℝ)^j) L
      X C B δ₀ (scalarOrderWeight (M:ℝ) L p^2/(complexity g p:ℝ))
      hX.le hC.le hB.le hδ₀ hδ hgX
      (fun j hj=>scalar_truncation_term_bound _ C B (M:ℝ) _ p L j hC.le hB.le
        (Nat.cast_nonneg _) hhR hj.le (hgCoef j))
    exact (add_le_add hc hg).trans_eq (by rw[div_pow,←pow_mul];dsimp[B'];ring)
end WP.HigherOrder
