import WPFormalization.Marked.ExternalStringProfile
import WPFormalization.Volumes.BoundaryPolynomial
noncomputable section
namespace WP.BoundaryConvolution
open Set
/-- Literal (a,b) insertion weight of Eq.9.26 with t_i=L_i²/(4π²). -/
def boundaryInsertionTerm {p : ℕ} (t : Fin p → ℝ) (Y : ℝ)
    (a b : Fin p → ℕ) : ℝ :=
  ∏ i, (t i)^(a i+b i) * Y^(a i) * r Y^(b i) /
    ((a i).factorial * (a i+b i).factorial * (oddFactorial (b i):ℝ))

lemma boundaryInsertionTerm_hasSum (p : ℕ) (t : Fin p → ℝ) (ht : ∀ i, 0 ≤ t i)
    (Y : ℝ) (hY : Y ∈ Ico 0 y₀) (b : Fin p → ℕ) :
    HasSum (fun a : Fin p → ℕ => boundaryInsertionTerm t Y a b) (boundaryProfileWeight t Y b) := by
  let f : Fin p → ℕ → ℝ := fun i a => (t i)^(a+b i) * Y^a * r Y^(b i) /
    (a.factorial * (a+b i).factorial * (oddFactorial (b i):ℝ))
  have hs (i : Fin p) : HasSum (f i)
      (r Y^(b i)/(oddFactorial (b i):ℝ) * realTranslationWeight (t i) (b i) Y) := by
    have hk := (translationKernel_real_hasSum (b i) ((t i)*Y)).mul_left
      (r Y^(b i)/(oddFactorial (b i):ℝ)*(t i)^(b i))
    convert hk using 1
    · ext a
      dsimp only [f]
      rw [mul_pow,pow_add]
      ring
    · simp [realTranslationWeight,translationWeight,←Complex.ofReal_pow,Complex.mul_re]
      <;>ring
  have hn (i : Fin p) (a : ℕ) : 0 ≤ f i a := by
    dsimp only [f]
    apply div_nonneg
    · exact mul_nonneg (mul_nonneg (pow_nonneg (ht i) _) (pow_nonneg hY.1 _)) (pow_nonneg (r_pos Y hY).le _)
    · positivity
  have hsum := summable_fin_tuple_product p f (fun i => (hs i).summable) hn
  convert hsum.hasSum using 1
  · rfl
  · rw [tsum_fin_tuple_product p f (fun i => (hs i).summable) hn]
    simp only [fun i => (hs i).tsum_eq]
    rfl

/-- The original double insertion series, with invalid b states exactly zero.
The canonical profiles and every factorial/power are the actual definitions. -/
lemma stringBoundaryAmplitude_double_series (P : PsiTheory) (g : ℕ) {p : ℕ} (hp : 1 ≤ p)
    (hs : Stable g p) (t : Fin p → ℝ) (ht : ∀ i, 0 ≤ t i)
    (Y : ℝ) (hY : Y ∈ Ico 0 y₀) :
    stringBoundaryAmplitude P g t 0 Y / shifted P g (List.replicate p 0) Y =
      ∑' b : Fin p → ℕ, ∑' a : Fin p → ℕ,
        profile P g (List.ofFn b) Y * boundaryInsertionTerm t Y a b := by
  rw [stringBoundaryAmplitude_ratio_tsum P g hp hs t Y hY]
  apply tsum_congr
  intro b
  exact ((boundaryInsertionTerm_hasSum p t ht Y hY b).mul_left
    (profile P g (List.ofFn b) Y)).tsum_eq.symm
end WP.BoundaryConvolution
