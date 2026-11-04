import WPFormalization.RandomGeometry.BoltzmannCuspVariance
import WPFormalization.RandomGeometry.BoltzmannCuspProbabilityCore
import WPFormalization.RandomGeometry.BoltzmannCuspScaleCore
noncomputable section
namespace WP.BoltzmannCusp
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology
lemma law_density_bias_error (P:PsiTheory) :
    ∃ C:ℝ,0<C ∧ ∃ N:ℕ,∀ g≥N,∀ (hg:2≤g) (hf0:0 < markedF P g 0 0),
      ∀ (x:ℝ) (hx:x∈Ico (0:ℝ) xCritical),∀ (hfx:0 < markedF P g 0 x),
      |(∫n:ℕ,(n:ℝ) ∂(law P g hg hf0 x hx hfx:Measure ℕ))-2*(g:ℝ)*Psi x|≤C*Psi x := by
  obtain ⟨C,hC,N,hN⟩ := law_mean_error P
  refine ⟨C+2,by linarith,N,?_⟩
  intro g hg hg2 hf0 x hx hfx
  have hc : (complexity g 0:ℝ)=2*(g:ℝ)-2 := by
    unfold complexity
    rw [Nat.cast_sub (by omega)]
    push_cast
    ring
  have hm:=hN g hg hg2 hf0 x hx hfx
  have hp:=psi_nonneg x hx
  calc
    |(∫n:ℕ,(n:ℝ) ∂(law P g hg2 hf0 x hx hfx:Measure ℕ))-2*(g:ℝ)*Psi x|=
        |((∫n:ℕ,(n:ℝ) ∂(law P g hg2 hf0 x hx hfx:Measure ℕ))-(complexity g 0:ℝ)*Psi x)-2*Psi x| := by
      rw [hc];congr 1;ring
    _≤|(∫n:ℕ,(n:ℝ) ∂(law P g hg2 hf0 x hx hfx:Measure ℕ))-(complexity g 0:ℝ)*Psi x|+|2*Psi x| := abs_sub _ _
    _≤C*Psi x+2*Psi x := by rw [abs_of_nonneg (by positivity : 0≤2*Psi x)];gcongr
    _=(C+2)*Psi x := by ring

lemma law_compactified_density_tail (P:PsiTheory) :
    ∃ C:ℝ,0<C ∧ ∀ ε:ℝ,0<ε → ∃ N:ℕ,∀ g≥N,
      ∀ (hg:2≤g) (hf0:0 < markedF P g 0 0),∀ (x:ℝ) (hx:x∈Ico (0:ℝ) xCritical),
      ∀ (hfx:0 < markedF P g 0 x),
      (law P g hg hf0 x hx hfx:Measure ℕ)
        {n:ℕ|ε≤|(1+(n:ℝ)/(g:ℝ))/(1+2*Psi x)-1|}≤ENNReal.ofReal (C/(ε^2*(g:ℝ))) := by
  obtain ⟨Cb,hCb,Nb,hbias⟩ := law_density_bias_error P
  obtain ⟨Cv,hCv,Nv,hvar⟩ := law_variance_upper P
  refine ⟨Cv,hCv,?_⟩
  intro ε hε
  obtain ⟨Nε,hNε⟩ := exists_nat_gt (Cb/ε)
  refine ⟨Nb+Nv+Nε+3,?_⟩
  intro g hg hg2 hf0 x hx hfx
  apply measure_relative_event_le _ (law_memLp_count P g hg2 hf0 x hx hfx)
    (g:ℝ) (Psi x) ε Cb Cv (by exact_mod_cast (show 0<g by omega))
    (psi_nonneg x hx) hε hCb.le hCv.le (hbias g (by omega) hg2 hf0 x hx hfx) _
    (hvar g (by omega) hg2 hf0 x hx hfx)
  have hn : Cb/ε≤(g:ℝ) := hNε.le.trans (by exact_mod_cast (show Nε≤g by omega))
  exact (div_le_iff₀ hε).mp hn |>.trans_eq (by ring)

lemma law_scale_tail (P:PsiTheory) (ε:ℝ) (hε:0<ε) :
    ∃ C:ℝ,0<C ∧ ∃ N:ℕ,∀ g≥N,∀ (hg:2≤g) (hf0:0 < markedF P g 0 0),
      ∀ (x:ℝ) (hx:x∈Ico (0:ℝ) xCritical),∀ (hfx:0 < markedF P g 0 x),
      (law P g hg hf0 x hx hfx:Measure ℕ)
        {n:ℕ|ε≤|tightScale ((n:ℝ)/(g:ℝ))/tightParameterScale (inverseY x)-1|}≤
          ENNReal.ofReal (C/(g:ℝ)) := by
  let δ:=min (1/8:ℝ) (ε/16)
  have hδ : 0<δ := lt_min (by norm_num) (by positivity)
  have hδ₁ : δ≤1/8 := min_le_left _ _
  have hδ₂ : δ≤ε/16 := min_le_right _ _
  obtain ⟨C,hC,hbound⟩ := law_compactified_density_tail P
  obtain ⟨N,hN⟩ := hbound δ hδ
  refine ⟨C/δ^2,by positivity,N,?_⟩
  intro g hg hg2 hf0 x hx hfx
  have hp:=psi_nonneg x hx
  have hbase := TightConnected.connected_tightParameterScale_eq_density x hx
  calc
    (law P g hg2 hf0 x hx hfx:Measure ℕ)
        {n:ℕ|ε≤|tightScale ((n:ℝ)/(g:ℝ))/tightParameterScale (inverseY x)-1|}≤
      (law P g hg2 hf0 x hx hfx:Measure ℕ)
        {n:ℕ|δ≤|(1+(n:ℝ)/(g:ℝ))/(1+2*Psi x)-1|} := by
      apply measure_mono
      intro n hn
      by_contra hn'
      have hlt : |(1+(n:ℝ)/(g:ℝ))/(1+2*Psi x)-1|<δ := lt_of_not_ge hn'
      have hrel := density_relative_scale ((n:ℝ)/(g:ℝ)) (2*Psi x) (by positivity) (by positivity)
        (hlt.le.trans (hδ₁.trans (by norm_num)))
      rw [hbase] at hn
      change ε≤|tightScale ((n:ℝ)/(g:ℝ))/tightScale (2*Psi x)-1| at hn
      linarith
    _≤ENNReal.ofReal (C/(δ^2*(g:ℝ))) := hN g hg hg2 hf0 x hx hfx
    _=ENNReal.ofReal ((C/δ^2)/(g:ℝ)) := by congr 1;ring
end WP.BoltzmannCusp
