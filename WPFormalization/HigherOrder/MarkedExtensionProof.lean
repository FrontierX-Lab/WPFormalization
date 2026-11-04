import WPFormalization.HigherOrder.ExtensionDefinitions
import WPFormalization.HigherOrder.LogMarkedComplexGevrey
import WPFormalization.Analysis.ComplexFiniteExpGevreyTwo
/-! The actual logarithmic and marked coefficient families share one complex
Gevrey-two extension. Finite exponentiation preserves the prescribed real jets. -/

noncomputable section
namespace WP.HigherOrder
open Set PowerSeries
lemma markedCoefficient_common_complex_gevrey_two (P:PsiTheory) (p:ℕ) (hp:1 ≤ p):
    ∃C B:ℝ,0<C ∧ 0<B ∧
      GevreyExtensionPair (logarithmicMarkedCoefficient P p) (markedCoefficient P p) C B:=by
  obtain ⟨Ω,C,B,hΩ,hΩv,hcover,hC,hB,F,hF⟩:=logarithmicMarkedCoefficient_common_complex_gevrey_two P p hp
  let G:ℕ→ℂ→ℂ:=fun j z=>if j=0 then 0 else F j z
  have hGa:∀j:ℕ,AnalyticOnNhd ℂ (G j) Ω:=by
    intro j
    by_cases hj:j=0
    · simp only[G,hj,ite_true];exact analyticOnNhd_const
    · simpa only[G,ite_eq_right hj] using (hF j).1
  have hGr:∀j:ℕ,∀Y∈Icc (0:ℝ) y₀,G j (Y:ℂ)=(logarithmicMarkedCoefficient P p j Y:ℂ):=by
    intro j Y hY
    by_cases hj:j=0
    · subst j;simp[G,logarithmicMarkedCoefficient]
    · simpa only[G,ite_eq_right hj] using (hF j).2.1 Y hY
  have hGb:∀j:ℕ,∀z∈Ω,‖G j z‖ ≤ C*B^j*(j.factorial:ℝ)^2:=by
    intro j z hz
    by_cases hj:j=0
    · simp only[G,hj,ite_true,norm_zero]
      positivity
    · simpa only[G,ite_eq_right hj] using (hF j).2.2 z hz
  let S:ℂ→PowerSeries ℂ:=fun z=>PowerSeries.mk (fun j=>G j z)
  have hS0:∀z∈Ω,PowerSeries.constantCoeff (S z)=0:=by intro z hz;simp[S,G]
  have hSa:∀j:ℕ,AnalyticOnNhd ℂ (fun z=>PowerSeries.coeff j (S z)) Ω:=by
    intro j
    simpa only[S,PowerSeries.coeff_mk] using hGa j
  have hSb:∀j:ℕ,∀z∈Ω,‖PowerSeries.coeff j (S z)‖ ≤ C*B^j*(j.factorial:ℝ)^2:=by
    intro j z hz
    simpa only[S,PowerSeries.coeff_mk] using hGb j z hz
  obtain ⟨hLa,hLb⟩:=Analysis.finiteExpComplex_family_gevreyTwo Ω S C B hC.le hB hS0 hSa hSb
  let L:ℕ→ℂ→ℂ:=fun j z=>PowerSeries.coeff j (Analysis.finiteExpComplex (S z))
  let B₁:=8*B*(Real.exp 1)^2
  have hB₁:0<B₁:=by dsimp[B₁];positivity
  let C':=C+Real.exp (2*C)
  let B':=B+B₁
  have hC':0<C':=by dsimp[C'];positivity
  have hB':0<B':=by dsimp[B'];positivity
  refine ⟨C',B',hC',hB',Ω,G,L,hΩ,hcover,?_,?_,?_⟩
  · intro j
    exact ⟨hGa j,hLa j⟩
  · intro j Y hY
    refine ⟨hGr j Y hY,?_⟩
    let fr:=markedLogSeries P p Y
    have he:∀i:ℕ,i ≤ j→PowerSeries.coeff i (S (Y:ℂ))=((PowerSeries.coeff i fr:ℝ):ℂ):=by
      intro i hi
      simpa only[S,PowerSeries.coeff_mk,fr,markedLogSeries] using hGr i Y hY
    exact Analysis.finiteExpComplex_coeff_of_real_jets (S (Y:ℂ)) fr j he
  · intro j z hz
    have hga:=hGb j z hz
    have hla:=hLb j z hz
    have hb₀:B^j ≤ B'^j:=pow_le_pow_left₀ hB.le (by dsimp[B'];linarith) _
    have hb₁:B₁^j ≤ B'^j:=pow_le_pow_left₀ hB₁.le (by dsimp[B'];linarith) _
    have hca:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hb₀ hC.le) (sq_nonneg (j.factorial:ℝ))
    have hcl:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hb₁ (Real.exp_pos (2*C)).le) (sq_nonneg (j.factorial:ℝ))
    apply (add_le_add hga hla).trans
    exact (add_le_add hca hcl).trans_eq (by dsimp[C'];ring)
end WP.HigherOrder
