import WPFormalization.Marked.ExternalStringMoments
import WPFormalization.Analysis.BoundaryFactorMoments
noncomputable section
namespace WP.BoundaryConvolution
open Set
lemma boundaryProfileWeight_uniform_moments (p : ℕ) (hp : 1 ≤ p) (t₀ : ℝ) (ht₀ : 0 ≤ t₀) :
    ∃ M : ℝ, 0 < M ∧ ∀ Y ∈ Ico 0 y₀, ∀ t : Fin p → ℝ, (∀ i, t i ∈ Icc 0 t₀) →
      Summable (boundaryProfileWeight t Y) ∧
      Summable (fun b => boundaryProfileMoment b * boundaryProfileWeight t Y b) ∧
      (∑' b : Fin p → ℕ, boundaryProfileMoment b * boundaryProfileWeight t Y b) ≤ M := by
  obtain ⟨H,hH,hbound⟩ := Analysis.boundary_degree_weight_moment_uniform t₀ ht₀
  have hpR : (0:ℝ) < p := by exact_mod_cast (by omega : 0 < p)
  refine ⟨(p:ℝ)^2*H*(H+1)^p,by positivity,?_⟩
  intro Y hY t ht
  let w : Fin p → ℕ → ℝ := fun i k => r Y^k / (oddFactorial k:ℝ) * realTranslationWeight (t i) k Y
  have hwn (i : Fin p) (k : ℕ) : 0 ≤ w i k := by
    exact mul_nonneg (div_nonneg (pow_nonneg (r_pos Y hY).le _) (Nat.cast_nonneg _))
      (realTranslationWeight_nonneg (t i) (ht i).1 k Y hY.1)
  have hs (i : Fin p) : Summable (fun k : ℕ => ((k:ℝ)+1)^2*w i k) := by
    simpa only [w,realTranslationWeight] using (hbound Y hY (t i) (ht i)).1
  have hb (i : Fin p) : (∑' k : ℕ, ((k:ℝ)+1)^2*w i k) ≤ H := by
    simpa only [w,realTranslationWeight] using (hbound Y hY (t i) (ht i)).2
  have he : boundaryProfileWeight t Y = fun b => ∏ i, w i (b i) := rfl
  rw [he]
  exact boundary_tuple_square_moment_bound hp w hwn hs H hH.le hb
end WP.BoundaryConvolution
