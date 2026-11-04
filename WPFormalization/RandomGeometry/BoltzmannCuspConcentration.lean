import WPFormalization.RandomGeometry.BoltzmannCuspUniform
noncomputable section
namespace WP.BoltzmannCusp
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology
lemma law_diverging_mean_tail (P:PsiTheory) :
    ∃ C:ℝ,0<C ∧ ∀ ε:ℝ,0<ε → ∃ N:ℕ,∀ g≥N,
      ∀ (hg:2≤g) (hf0:0 < markedF P g 0 0),∀ (x:ℝ) (hx:x∈Ico (0:ℝ) xCritical),
      ∀ (hfx:0 < markedF P g 0 x),0<Psi x →
      (law P g hg hf0 x hx hfx:Measure ℕ)
        {n:ℕ|ε≤|(n:ℝ)/((complexity g 0:ℝ)*Psi x)-1|}≤
          ENNReal.ofReal ((C/ε^2)*(1/((complexity g 0:ℝ)*Psi x)+1/(g:ℝ))) := by
  obtain ⟨Cb,hCb,Nb,hbias⟩ := law_mean_error P
  obtain ⟨Cv,hCv,Nv,hvar⟩ := law_variance_upper P
  refine ⟨4*Cv,by positivity,?_⟩
  intro ε hε
  obtain ⟨Nε,hNε⟩ := exists_nat_gt (2*Cb/ε)
  refine ⟨Nb+Nv+Nε+3,?_⟩
  intro g hg hg2 hf0 x hx hfx hψ
  have hGH : (g:ℝ)≤(complexity g 0:ℝ) := by
    exact_mod_cast (show g≤complexity g 0 by unfold complexity;omega)
  apply measure_scaled_event_le _ (law_memLp_count P g hg2 hf0 x hx hfx)
    (g:ℝ) (complexity g 0:ℝ) (Psi x) ε Cb Cv
    (by exact_mod_cast (show 0<g by omega)) hGH hψ hε hCv.le
    (hbias g (by omega) hg2 hf0 x hx hfx) _ (hvar g (by omega) hg2 hf0 x hx hfx)
  have hn : 2*Cb/ε≤(g:ℝ) := hNε.le.trans (by exact_mod_cast (show Nε≤g by omega))
  have hh := (div_le_iff₀ hε).mp hn
  nlinarith

lemma law_mean_bounded_of_model_mean_bounded (P:PsiTheory) :
    ∃ C:ℝ,0<C ∧ ∃ N:ℕ,∀ g≥N,∀ (hg:2≤g) (hf0:0 < markedF P g 0 0),
      ∀ (x:ℝ) (hx:x∈Ico (0:ℝ) xCritical),∀ (hfx:0 < markedF P g 0 x),
      ∀ M:ℝ,0≤M → (complexity g 0:ℝ)*Psi x≤M →
      (∫n:ℕ,(n:ℝ) ∂(law P g hg hf0 x hx hfx:Measure ℕ))≤C*M := by
  obtain ⟨C,hC,N,hN⟩ := law_mean_error P
  refine ⟨1+C,by linarith,N+2,?_⟩
  intro g hg hg2 hf0 x hx hfx M hM hmean
  have herr := (abs_sub_le_iff.mp (hN g (by omega) hg2 hf0 x hx hfx)).1
  have hp:=psi_nonneg x hx
  have hh : (1:ℝ)≤(complexity g 0:ℝ) := by
    exact_mod_cast (show 1≤complexity g 0 by unfold complexity;omega)
  have hpsi : Psi x≤M := by nlinarith
  nlinarith

lemma law_bounded_mean_tail (P:PsiTheory) :
    ∃ C:ℝ,0<C ∧ ∃ N:ℕ,∀ g≥N,∀ (hg:2≤g) (hf0:0 < markedF P g 0 0),
      ∀ (x:ℝ) (hx:x∈Ico (0:ℝ) xCritical),∀ (hfx:0 < markedF P g 0 x),
      ∀ M:ℝ,0≤M → (complexity g 0:ℝ)*Psi x≤M → ∀ R:ℝ,0<R →
      (law P g hg hf0 x hx hfx:Measure ℕ) {n:ℕ|R≤(n:ℝ)}≤ENNReal.ofReal (C*M/R) := by
  obtain ⟨C,hC,N,hN⟩ := law_mean_bounded_of_model_mean_bounded P
  refine ⟨C,hC,N,?_⟩
  intro g hg hg2 hf0 x hx hfx M hM hmean R hR
  exact (measure_nat_markov _ (law_integrable_count P g hg2 hf0 x hx hfx) R hR).trans
    (ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right (hN g hg hg2 hf0 x hx hfx M hM hmean) hR.le))
end WP.BoltzmannCusp
