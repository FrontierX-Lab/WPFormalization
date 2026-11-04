import WPFormalization.HigherOrder.RatioRemainderPairing
import WPFormalization.HigherOrder.RatioFactorEncoding
import WPFormalization.Marked.UniformCorrectionBounds
/-! Exact C.14 finite-product remainders retain the full parent loss
prefactor. The actual scalar suffix is uniformly bounded using the proved
all-marking corrections. The remaining inputs are individual previous-order
scalar errors and finite known prefix coefficients; this supporting theorem
assumes no whole ratio remainder and uses no product of unknown errors. -/
noncomputable section
namespace WP.HigherOrder
open Set PowerSeries

lemma ratio_inverse_linear_abs_bound (L:ℕ)(hL:1 ≤ L)(c S h:ℝ)(hc:|c| ≤ L)
    (hS:2*(L:ℝ) ≤ S)(hh:0<h)(hsmall:S^2/h ≤ 1) : |(1-c/h)⁻¹| ≤ 2 := by
  have hLR:(1:ℝ) ≤ L := by exact_mod_cast hL
  have hS1:1 ≤ S := by linarith
  have hhSq:S^2 ≤ h := (div_le_one hh).mp hsmall
  have hxhalf:|c|/h ≤ 1/2 := (div_le_iff₀ hh).mpr (by nlinarith [abs_nonneg c])
  have hcx:c/h ≤ |c|/h := div_le_div_of_nonneg_right (le_abs_self c) hh.le
  have hd:1/2 ≤ 1-c/h := by linarith
  have hd0:0<1-c/h := by linarith
  rw [abs_inv,abs_of_pos hd0]
  simpa only [one_div] using (one_div_le hd0 (by norm_num:(0:ℝ)<2)).mpr hd

lemma actualLargeRatioFactor_abs_uniform (P:PsiTheory) :
    ∃V:ℝ,0<V ∧ 1 ≤ V ∧ ∀g p j s L:ℕ,∀Y∈Icc (0:ℝ) y₀,∀S:ℝ,
      j ≤ g → s<p → Stable (g-j) (p-s) → 1 ≤ L → 2*j+s ≤ L →
      2*(L:ℝ) ≤ S → S^2/(complexity g p:ℝ) ≤ 1 →
      ∀i<(2*j+s)+j,|actualLargeRatioFactor P g p j s Y i| ≤ V := by
  obtain ⟨X,hX,hScalar⟩:=scalar_corrections_abs_uniform P
  refine ⟨max 1 (2*X),lt_of_lt_of_le zero_lt_one (le_max_left _ _),le_max_left _ _,?_⟩
  intro g p j s L Y hY S hj hs hstable hL hr hS hsmall i hi
  have hp:1 ≤ p := by omega
  have hparent:Stable g p := by unfold Stable at *;omega
  have hh:0<(complexity g p:ℝ) := by
    have hn:0<complexity g p := by unfold complexity Stable at *;omega
    exact_mod_cast hn
  by_cases hir:i<2*j+s
  · rw [actualLargeRatioFactor,ite_eq_left hir,div_eq_mul_inv,abs_mul]
    have hκ:|cuspCorrection P (g-j) (p-s+i) Y| ≤ X := by
      have he:=hScalar (g-j) (p-s+i) (by omega) (by unfold Stable at *;omega) Y hY
      linarith [abs_nonneg (genusCorrection P (g-j) (p-s+i) Y)]
    have hc:|((2*j+s-i:ℕ):ℝ)| ≤ L := by
      rw [abs_of_nonneg (Nat.cast_nonneg _)]
      exact_mod_cast (show 2*j+s-i ≤ L by omega)
    have hd:=ratio_inverse_linear_abs_bound L hL ((2*j+s-i:ℕ):ℝ) S (complexity g p:ℝ) hc hS hh hsmall
    apply (mul_le_mul hκ hd (abs_nonneg _) hX.le).trans
    exact (show X*2 ≤ 2*X by nlinarith).trans (le_max_right _ _)
  · rw [actualLargeRatioFactor,ite_eq_right hir]
    have hb:i-(2*j+s)<j := by omega
    have he:=hScalar (g-(i-(2*j+s))) (p+2*(i-(2*j+s))) (by omega)
      (by unfold Stable at *;omega) Y hY
    have hΓ:|genusCorrection P (g-(i-(2*j+s))) (p+2*(i-(2*j+s))) Y| ≤ X := by
      linarith [abs_nonneg (cuspCorrection P (g-(i-(2*j+s))) (p+2*(i-(2*j+s))) Y)]
    exact hΓ.trans ((show X ≤ 2*X by linarith).trans (le_max_right _ _))

lemma large_component_ratio_remainder_scaled (P:PsiTheory)(g p j s L:ℕ)(F:HierarchyJet)
    (Y:ℝ)(hY:Y∈Icc (0:ℝ) y₀)(hj:j ≤ g)(hs:s<p)(hstable:Stable (g-j) (p-s))
    (hr:2*j+s<L)(S V:ℝ)(hS:0 ≤ S)(hV:0 ≤ V)(e E:ℕ→ℕ→ℝ)
    (he:∀a i,0 ≤ e a i)(hE:∀a i,0 ≤ E a i)
    (hX:∀a<(2*j+s)+j,|actualLargeRatioFactor P g p j s Y a| ≤ V)
    (hcoeff:∀a<(2*j+s)+j,∀i<L-(2*j+s),
      |PowerSeries.coeff i (∏k∈Finset.range a,formalLargeRatioFactor F p j s k)| ≤ e a i*S^(2*i))
    (herr:∀a<(2*j+s)+j,∀m:ℕ,1 ≤ m → m ≤ L-(2*j+s) →
      |actualLargeRatioFactor P g p j s Y a-
        truncationValue (formalLargeRatioFactor F p j s a) m (1/(complexity g p:ℝ))| ≤
        E a m*S^(2*m)/(complexity g p:ℝ)^m) :
    |W P (g-j) (p-s) Y/W P g p Y-
      truncationValue (ratioSeries Y F p j s) L (1/(complexity g p:ℝ))| ≤
      (|A Y|^(2*j+s)*S^(2*(L-(2*j+s)))/(complexity g p:ℝ)^L)*
        (∑a∈Finset.range ((2*j+s)+j),∑i∈Finset.range (L-(2*j+s)),
          e a i*E a (L-(2*j+s)-i)*V^(((2*j+s)+j)-(a+1))) := by
  have hh:0<(complexity g p:ℝ) := by
    have hn:0<complexity g p := by unfold complexity Stable at *;omega
    exact_mod_cast hn
  have hq:1 ≤ L-(2*j+s) := by omega
  have hb:=finite_product_remainder_scaled_bound
    (actualLargeRatioFactor P g p j s Y) (formalLargeRatioFactor F p j s) e E
    ((2*j+s)+j) (L-(2*j+s)) hq S (complexity g p:ℝ) V hS hh hV he hE hX hcoeff herr
  rw [actualLargeRatioFactor_product,formalLargeRatioFactor_product] at hb
  have hp:=large_component_product_remainder_pairing P g p j s L F 1 1 hr.le Y hY hj hs hstable
  simp only [mul_one] at hp
  rw [hp]
  apply (mul_le_mul_of_nonneg_left hb (by positivity:0 ≤ |A Y|^(2*j+s)/(complexity g p:ℝ)^(2*j+s))).trans_eq
  have hpow:(complexity g p:ℝ)^(2*j+s)*(complexity g p:ℝ)^(L-(2*j+s))=(complexity g p:ℝ)^L := by
    rw [←pow_add,Nat.add_sub_of_le hr.le]
  rw [←hpow]
  ring

end WP.HigherOrder
