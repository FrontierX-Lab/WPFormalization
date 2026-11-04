import WPFormalization.Tight.SeparatingPositiveProduct
import WPFormalization.Tight.ConnectedCoefficientAlgebra

noncomputable section
namespace WP.TightSeparating
open Set

def cutProductMass (P : PsiTheory) {Q : ℕ} (gs ps : Fin Q → ℕ)
    (L : (i : Fin Q) → Fin (ps i) → ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  realCoeff (cutProductG P gs ps L) n*x^n/(cutProductG P gs ps L x).re

lemma cutProductG_real_positive (P : PsiTheory) {Q : ℕ} (gs ps : Fin Q → ℕ)
    (hp : ∀ i, 1 ≤ ps i) (hs : ∀ i, Stable (gs i) (ps i))
    (L : (i : Fin Q) → Fin (ps i) → ℝ) (x : ℝ) (hx : x ∈ Ico (0 : ℝ) xCritical) :
    0 < (cutProductG P gs ps L x).re := by
  have hY := (inverseY_branch x hx).1
  have he : cutProductG P gs ps L x =
      (∏ i, tightShiftedPolynomial P (gs i) (ps i) (inverseY x) (L i) : ℝ) := by
    unfold cutProductG
    simp_rw [TightMoments.momentTightG_ofReal P _ _ _ x hx]
    exact (map_prod Complex.ofRealHom _ _).symm
  rw [he,Complex.ofReal_re]
  exact Finset.prod_pos (fun i _ => tightShiftedPolynomial_pos P _ _ (hp i) (hs i) _ hY _)

/-- Original F.5 for the actual cut-product numerator, with the derivative used
only in the unmarked denominator. No protected cusp is inserted in a tight factor. -/
lemma cutProduct_coefficient_ratio_derivative_mass (P : PsiTheory) (g : ℕ)
    (hsg : Stable g 1) {Q : ℕ} (gs ps : Fin Q → ℕ)
    (hp : ∀ i, 1 ≤ ps i) (hs : ∀ i, Stable (gs i) (ps i))
    (L : (i : Fin Q) → Fin (ps i) → ℝ) (n : ℕ) (hn : 1 ≤ n)
    (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) xCritical)
    (hm : cuspMass P g 1 (n-1) x ≠ 0) :
    realCoeff (cutProductG P gs ps L) n/realCoeff (Phi P g) n =
      ((n : ℝ)/x)*((cutProductG P gs ps L x).re/markedF P g 1 x)*
        (cutProductMass P gs ps L n x/cuspMass P g 1 (n-1) x) := by
  have hF : markedF P g 1 x ≠ 0 :=
    (markedF_positive_cusp_weight P g 1 (by omega) hsg x ⟨hx.1.le,hx.2⟩).ne'
  have hG : (cutProductG P gs ps L x).re ≠ 0 :=
    (cutProductG_real_positive P gs ps hp hs L x ⟨hx.1.le,hx.2⟩).ne'
  have hc : realCoeff (iteratedDeriv 1 (Phi P g)) (n-1)=(n : ℝ)*realCoeff (Phi P g) n := by
    rw [iteratedDeriv_one,TightConnected.connected_realCoeff_deriv]
    have he : n-1+1=n := by omega
    rw [he]
    have hnc : ((n-1 : ℕ) : ℝ)+1=(n : ℝ) := by exact_mod_cast he
    rw [hnc]
  have hc0 : realCoeff (Phi P g) n ≠ 0 := by
    intro hz
    apply hm
    unfold cuspMass
    rw [hc,hz,mul_zero,zero_mul,zero_div]
  have hxp : x^(n-1) ≠ 0 := pow_ne_zero _ hx.1.ne'
  have hnp : (n : ℝ) ≠ 0 := by exact_mod_cast (show n≠0 by omega)
  have hxpow : x^n=x^(n-1)*x := by rw [←pow_succ];congr 1;omega
  unfold cutProductMass cuspMass
  rw [hc,hxpow]
  field_simp [hF,hG,hc0,hxp,hnp,hx.1.ne']
  <;> ring

/-- The fixed-cusp branch uses the original unmarked probability directly,
so it includes n=0 and requires no derivative at index -1. -/
lemma cutProduct_coefficient_ratio_le_of_unmarked_mass (P : PsiTheory) (g : ℕ)
    {Q : ℕ} (gs ps : Fin Q → ℕ)
    (hp : ∀ i, 1 ≤ ps i) (hs : ∀ i, Stable (gs i) (ps i))
    (L : (i : Fin Q) → Fin (ps i) → ℝ) (n : ℕ)
    (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) xCritical)
    (hF : 0 < markedF P g 0 x) (d : ℝ) (hd : 0 < d)
    (hm : d ≤ realCoeff (Phi P g) n*x^n/markedF P g 0 x) :
    realCoeff (cutProductG P gs ps L) n/realCoeff (Phi P g) n ≤
      (1/d)*((cutProductG P gs ps L x).re/markedF P g 0 x) := by
  have hxp : 0 < x^n := pow_pos hx.1 _
  have hden : 0 < realCoeff (Phi P g) n := by
    have hh := (le_div_iff₀ hF).mp hm
    exact pos_of_mul_pos_left ((mul_pos hd hF).trans_le hh) hxp.le
  have hnum := cutProductG_coefficient_le_value P gs ps hp hs L x ⟨hx.1.le,hx.2⟩ n
  have hval := cutProductG_real_positive P gs ps hp hs L x ⟨hx.1.le,hx.2⟩
  have hmass := (le_div_iff₀ hF).mp hm
  apply (div_le_iff₀ hden).mpr
  apply (mul_le_mul_iff_left₀ hxp).mp
  calc
    _ ≤ (cutProductG P gs ps L x).re := hnum
    _ ≤ ((1/d)*((cutProductG P gs ps L x).re/markedF P g 0 x)*
        realCoeff (Phi P g) n)*x^n := by
      have hh := mul_le_mul_of_nonneg_left hmass
        (show 0 ≤ (cutProductG P gs ps L x).re/(d*markedF P g 0 x) by positivity)
      convert hh using 1 <;> field_simp <;> ring

end WP.TightSeparating
