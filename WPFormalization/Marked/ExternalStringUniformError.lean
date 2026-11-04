import WPFormalization.Marked.ExternalStringUniformMoments
import WPFormalization.Analysis.BoundaryFactorSeries
noncomputable section
namespace WP.BoundaryConvolution
open Set
lemma stringBoundaryAmplitude_uniform_real_axis
    (P : PsiTheory) (p : ℕ) (hp : 1 ≤ p) (L₀ : ℝ) (hL₀ : 0 ≤ L₀) :
    ∃ C : ℝ, 0 < C ∧ ∀ g : ℕ, 1 ≤ g → ∀ Y ∈ Ico 0 y₀,
      ∀ L : Fin p → ℝ, (∀ i, L i ∈ Icc 0 L₀) →
      |stringBoundaryAmplitude P g (fun i => (L i)^2/(4*Real.pi^2)) 0 Y /
        (shifted P g (List.replicate p 0) Y * ∏ i, boundaryFactor Y (L i)) - 1| ≤ C/g := by
  let t₀ : ℝ := L₀^2/(4*Real.pi^2)
  have ht₀ : 0 ≤ t₀ := by dsimp [t₀];positivity
  obtain ⟨C,hC,herr⟩ := stringBoundaryAmplitude_profile_relative_error P p hp
  obtain ⟨M,hM,hmoment⟩ := boundaryProfileWeight_uniform_moments p hp t₀ ht₀
  refine ⟨C*M,mul_pos hC hM,?_⟩
  intro g hg Y hY L hL
  let t : Fin p → ℝ := fun i => (L i)^2/(4*Real.pi^2)
  have ht (i : Fin p) : t i ∈ Icc 0 t₀ := by
    refine ⟨by dsimp [t];positivity,?_⟩
    have hsq : (L i)^2 ≤ L₀^2 := by nlinarith [(hL i).1,(hL i).2]
    exact div_le_div_of_nonneg_right hsq (by positivity)
  have hm := hmoment Y hY t ht
  let w : Fin p → ℕ → ℝ := fun i b => r Y^b/(oddFactorial b:ℝ)*realTranslationWeight (t i) b Y
  have hs (i : Fin p) : HasSum (w i) (boundaryFactor Y (L i)) := Analysis.boundaryFactor_realTranslationWeight_hasSum Y (L i) hY
  have hwn (i : Fin p) (b : ℕ) : 0 ≤ w i b :=
    mul_nonneg (div_nonneg (pow_nonneg (r_pos Y hY).le _) (Nat.cast_nonneg _))
      (realTranslationWeight_nonneg (t i) (ht i).1 b Y hY.1)
  have hbprod : HasSum (boundaryProfileWeight t Y) (∏ i, boundaryFactor Y (L i)) := by
    have hsum := summable_fin_tuple_product p w (fun i => (hs i).summable) hwn
    have he : boundaryProfileWeight t Y = fun b => ∏ i, w i (b i) := rfl
    rw [he]
    convert hsum.hasSum using 1
    rw [tsum_fin_tuple_product p w (fun i => (hs i).summable) hwn]
    simp only [fun i => (hs i).tsum_eq]
  have hB : 1 ≤ ∏ i, boundaryFactor Y (L i) :=
    Finset.one_le_prod₀ (fun i _ => one_le_boundaryFactor Y (L i))
  have he := herr g hg t (fun i => (ht i).1) Y hY (∏ i, boundaryFactor Y (L i))
    (∑' b : Fin p → ℕ, boundaryProfileMoment b * boundaryProfileWeight t Y b) hB hbprod hm.2.1.hasSum
  apply he.trans
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hm.2.2 hC.le) (Nat.cast_nonneg g)
end WP.BoundaryConvolution
