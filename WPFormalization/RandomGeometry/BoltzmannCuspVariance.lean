import WPFormalization.RandomGeometry.BoltzmannCuspMoments
import WPFormalization.RandomGeometry.BoltzmannCuspQuantitative
noncomputable section
namespace WP.BoltzmannCusp
open Set MeasureTheory ProbabilityTheory
lemma unmarked_cusp_ratio_error_weight (P:PsiTheory) :
    ∃ C:ℝ,0<C ∧ ∃ N:ℕ,∀ g≥N,∀ x∈Ico (0:ℝ) xCritical,
      |x*markedF P g 1 x/markedF P g 0 x-(complexity g 0:ℝ)*Psi x|≤C*Psi x := by
  obtain ⟨C,hC,N,hN⟩ := unmarked_cusp_ratio_error P
  refine ⟨C,hC,N,?_⟩
  intro g hg x hx
  have hy:=inverseY_branch x hx
  simpa only [hy.2] using hN g hg (inverseY x) hy.1

lemma law_mean_error (P:PsiTheory) :
    ∃ C:ℝ,0<C ∧ ∃ N:ℕ,∀ g≥N,∀ (hg:2≤g) (hf0:0 < markedF P g 0 0),
      ∀ (x:ℝ) (hx:x∈Ico (0:ℝ) xCritical),∀ (hfx:0 < markedF P g 0 x),
      |(∫n:ℕ,(n:ℝ) ∂(law P g hg hf0 x hx hfx:Measure ℕ))-
        (complexity g 0:ℝ)*Psi x|≤C*Psi x := by
  obtain ⟨C,hC,N,hN⟩ := unmarked_cusp_ratio_error_weight P
  refine ⟨C,hC,N,?_⟩
  intro g hg hg2 hf0 x hx hfx
  rw [law_mean]
  exact hN g hg x hx

lemma law_variance_upper (P:PsiTheory) :
    ∃ C:ℝ,0<C ∧ ∃ N:ℕ,∀ g≥N,∀ (hg:2≤g) (hf0:0 < markedF P g 0 0),
      ∀ (x:ℝ) (hx:x∈Ico (0:ℝ) xCritical),∀ (hfx:0 < markedF P g 0 x),
      variance (fun n:ℕ=>(n:ℝ)) (law P g hg hf0 x hx hfx:Measure ℕ)
        ≤C*(g:ℝ)*(Psi x+(Psi x)^2) := by
  obtain ⟨C₀,hC₀,N₀,h₀⟩ := unmarked_cusp_ratio_error_weight P
  obtain ⟨C₁,hC₁,N₁,h₁⟩ := (marked_ratios P).1 1 (by omega)
  refine ⟨(2+C₀)*(2+C₀+C₁),by positivity,N₀+N₁+3,?_⟩
  intro g hg hg2 hf0 x hx hfx
  have hF₁ : 0 < markedF P g 1 x :=
    markedF_positive_cusp_weight P g 1 (by omega) (by unfold Stable;omega) x hx
  have hy:=inverseY_branch x hx
  have hnext := h₁ g (by omega) (inverseY x) hy.1
  rw [hy.2] at hnext
  have hc : (complexity g 1:ℝ)=(complexity g 0:ℝ)+1 := by
    exact_mod_cast (show complexity g 1=complexity g 0+1 by unfold complexity;omega)
  rw [hc] at hnext
  have hmain := variance_scalar_bound (g:ℝ) (complexity g 0:ℝ) (Psi x)
    (x*markedF P g 1 x/markedF P g 0 x) (x*markedF P g 2 x/markedF P g 1 x)
    C₀ C₁ (by exact_mod_cast (show 1≤g by omega)) (Nat.cast_nonneg _)
    (by exact_mod_cast (show complexity g 0≤2*g by unfold complexity;omega))
    (psi_nonneg x hx) (div_nonneg (mul_nonneg hx.1 hF₁.le) hfx.le)
    hC₀ hC₁ (h₀ g (by omega) x hx) hnext
  rw [law_variance]
  convert hmain using 1
  field_simp [hF₁.ne',hfx.ne']
  <;>ring

lemma law_chebyshev (P:PsiTheory) (g:ℕ) (hg:2≤g) (hf0:0 < markedF P g 0 0)
    (x:ℝ) (hx:x∈Ico 0 xCritical) (hfx:0 < markedF P g 0 x) (c:ℝ) (hc:0<c) :
    (law P g hg hf0 x hx hfx:Measure ℕ)
      {n:ℕ|c≤|(n:ℝ)-x*markedF P g 1 x/markedF P g 0 x|}≤
      ENNReal.ofReal (variance (fun n:ℕ=>(n:ℝ)) (law P g hg hf0 x hx hfx:Measure ℕ)/c^2) := by
  simpa only [law_mean] using meas_ge_le_variance_div_sq (law_memLp_count P g hg hf0 x hx hfx) hc
end WP.BoltzmannCusp
