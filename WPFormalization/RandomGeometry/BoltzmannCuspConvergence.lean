import WPFormalization.RandomGeometry.BoltzmannCuspConcentration
noncomputable section
namespace WP.BoltzmannCusp
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology

def zeroLaw : ProbabilityMeasure ℕ := ⟨Measure.dirac 0,inferInstance⟩

/-- Explicit finite-prefix extension. Whenever the normalized coefficients are
valid, this is exactly their probability law. All sufficiently large genera
are valid uniformly in the entire physical weight interval. -/
def extendedLaw (P:PsiTheory) (g:ℕ) (x:ℝ) : ProbabilityMeasure ℕ :=
  if h : 2≤g ∧ 0 < markedF P g 0 0 ∧ x∈Ico (0:ℝ) xCritical ∧ 0 < markedF P g 0 x then
    law P g h.1 h.2.1 x h.2.2.1 h.2.2.2
  else zeroLaw

lemma extendedLaw_eq_law (P:PsiTheory) (g:ℕ) (hg:2≤g) (hf0:0 < markedF P g 0 0)
    (x:ℝ) (hx:x∈Ico (0:ℝ) xCritical) (hfx:0 < markedF P g 0 x) :
    extendedLaw P g x=law P g hg hf0 x hx hfx := by
  have ha : 2≤g ∧ 0 < markedF P g 0 0 ∧ x∈Ico (0:ℝ) xCritical ∧ 0 < markedF P g 0 x := ⟨hg,hf0,hx,hfx⟩
  rw [extendedLaw,dif_pos ha]

lemma extendedLaw_original_weights_eventually (P:PsiTheory) :
    ∃ G:ℕ,∀ g≥G,∀ x∈Ico (0:ℝ) xCritical,∀ n:ℕ,
      (extendedLaw P g x:Measure ℕ) {n}=ENNReal.ofReal (weight P g x n) := by
  obtain ⟨G,hG⟩ := TightConnected.connected_unmarked_positive_eventually P
  refine ⟨G+2,?_⟩
  intro g hg x hx n
  rw [extendedLaw_eq_law P g (by omega)
    (hG g (by omega) 0 ⟨le_rfl,Analysis.xCritical_pos_parameter⟩) x hx (hG g (by omega) x hx)]
  exact law_singleton _ _ _ _ _ _ _ _

lemma extendedLaw_zero (P:PsiTheory) (g:ℕ) :
    (extendedLaw P g 0:Measure ℕ)=Measure.dirac 0 := by
  by_cases h : 2≤g ∧ 0 < markedF P g 0 0 ∧ (0:ℝ)∈Ico 0 xCritical ∧ 0 < markedF P g 0 0
  · rw [extendedLaw_eq_law P g h.1 h.2.1 0 h.2.2.1 h.2.2.2]
    exact law_zero P g h.1 h.2.1
  · rw [extendedLaw,dif_neg h]
    rfl

lemma extendedLaw_pgf_eventually (P:PsiTheory) :
    ∃ G:ℕ,∀ g≥G,∀ x∈Ico (0:ℝ) xCritical,∀ z∈Icc (0:ℝ) 1,
      Integrable (fun n:ℕ=>z^n) (extendedLaw P g x:Measure ℕ) ∧
      (∫n:ℕ,z^n ∂(extendedLaw P g x:Measure ℕ))=markedF P g 0 (x*z)/markedF P g 0 x := by
  obtain ⟨G,hG⟩ := TightConnected.connected_unmarked_positive_eventually P
  refine ⟨G+2,?_⟩
  intro g hg x hx z hz
  rw [extendedLaw_eq_law P g (by omega)
    (hG g (by omega) 0 ⟨le_rfl,Analysis.xCritical_pos_parameter⟩) x hx (hG g (by omega) x hx)]
  exact law_pgf _ _ _ _ _ _ _ z hz

lemma extendedLaw_scale_in_probability (P:PsiTheory) (gs:ℕ→ℕ)
    (hg:Tendsto gs atTop atTop) (xs:ℕ→ℝ) (hx:∀j,xs j∈Ico (0:ℝ) xCritical)
    (ε:ℝ) (hε:0<ε) :
    Tendsto (fun j=>(extendedLaw P (gs j) (xs j):Measure ℕ)
      {n:ℕ|ε≤|tightScale ((n:ℝ)/(gs j:ℝ))/tightParameterScale (inverseY (xs j))-1|})
      atTop (𝓝 0) := by
  obtain ⟨C,hC,N,hN⟩ := law_scale_tail P ε hε
  obtain ⟨G,hG⟩ := TightConnected.connected_unmarked_positive_eventually P
  have ht : Tendsto (fun j=>ENNReal.ofReal (C/(gs j:ℝ))) atTop (𝓝 0) := by
    have he := ENNReal.continuous_ofReal.continuousAt.tendsto.comp
      ((tendsto_natCast_atTop_atTop.comp hg).const_div_atTop C)
    simpa only [ENNReal.ofReal_zero,Function.comp_def] using he
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds ht
    (Eventually.of_forall fun _=>bot_le) _
  filter_upwards [hg.eventually_ge_atTop (N+G+2)] with j hj
  rw [extendedLaw_eq_law P (gs j) (by omega)
    (hG (gs j) (by omega) 0 ⟨le_rfl,Analysis.xCritical_pos_parameter⟩) (xs j) (hx j)
    (hG (gs j) (by omega) (xs j) (hx j))]
  exact hN (gs j) (by omega) _ _ (xs j) (hx j) _
end WP.BoltzmannCusp
namespace WP.BoltzmannCusp
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology
lemma extendedLaw_mean_error (P:PsiTheory) :
    ∃ C:ℝ,0<C ∧ ∃ N:ℕ,∀ g≥N,∀ x∈Ico (0:ℝ) xCritical,
      Integrable (fun n:ℕ=>(n:ℝ)) (extendedLaw P g x:Measure ℕ) ∧
      |(∫n:ℕ,(n:ℝ) ∂(extendedLaw P g x:Measure ℕ))-(complexity g 0:ℝ)*Psi x|≤C*Psi x := by
  obtain ⟨C,hC,N,hN⟩ := law_mean_error P
  obtain ⟨G,hG⟩ := TightConnected.connected_unmarked_positive_eventually P
  refine ⟨C,hC,N+G+2,?_⟩
  intro g hg x hx
  rw [extendedLaw_eq_law P g (by omega)
    (hG g (by omega) 0 ⟨le_rfl,Analysis.xCritical_pos_parameter⟩) x hx (hG g (by omega) x hx)]
  exact ⟨law_integrable_count _ _ _ _ _ _ _,hN g (by omega) _ _ x hx _⟩

lemma extendedLaw_count_concentration (P:PsiTheory) (gs:ℕ→ℕ)
    (hg:Tendsto gs atTop atTop) (xs:ℕ→ℝ) (hx:∀j,xs j∈Ico (0:ℝ) xCritical)
    (hmean:Tendsto (fun j=>(complexity (gs j) 0:ℝ)*Psi (xs j)) atTop atTop)
    (ε:ℝ) (hε:0<ε) :
    Tendsto (fun j=>(extendedLaw P (gs j) (xs j):Measure ℕ)
      {n:ℕ|ε≤|(n:ℝ)/((complexity (gs j) 0:ℝ)*Psi (xs j))-1|}) atTop (𝓝 0) := by
  obtain ⟨C,hC,hbound⟩ := law_diverging_mean_tail P
  obtain ⟨N,hN⟩ := hbound ε hε
  obtain ⟨G,hG⟩ := TightConnected.connected_unmarked_positive_eventually P
  have ht : Tendsto (fun j=>ENNReal.ofReal ((C/ε^2)*
      (1/((complexity (gs j) 0:ℝ)*Psi (xs j))+1/(gs j:ℝ)))) atTop (𝓝 0) := by
    have hν := hmean.const_div_atTop (1:ℝ)
    have hgg := (tendsto_natCast_atTop_atTop.comp hg).const_div_atTop (1:ℝ)
    have he := ENNReal.continuous_ofReal.continuousAt.tendsto.comp ((hν.add hgg).const_mul (C/ε^2))
    simpa only [zero_add,mul_zero,ENNReal.ofReal_zero,Function.comp_def] using he
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds ht
    (Eventually.of_forall fun _=>bot_le) _
  filter_upwards [hg.eventually_ge_atTop (N+G+2),hmean.eventually_gt_atTop 0] with j hj hν
  have hp : 0<Psi (xs j) := by
    have hh : 0≤(complexity (gs j) 0:ℝ) := Nat.cast_nonneg _
    by_contra hp
    have := mul_nonpos_of_nonneg_of_nonpos hh (le_of_not_gt hp)
    linarith
  rw [extendedLaw_eq_law P (gs j) (by omega)
    (hG (gs j) (by omega) 0 ⟨le_rfl,Analysis.xCritical_pos_parameter⟩) (xs j) (hx j)
    (hG (gs j) (by omega) (xs j) (hx j))]
  exact hN (gs j) (by omega) _ _ (xs j) (hx j) _ hp

lemma extendedLaw_bounded_mean_tight (P:PsiTheory) (gs:ℕ→ℕ)
    (hg:Tendsto gs atTop atTop) (xs:ℕ→ℝ) (hx:∀j,xs j∈Ico (0:ℝ) xCritical)
    (M:ℝ) (hM:0≤M)
    (hmean:∀ᶠj in atTop,(complexity (gs j) 0:ℝ)*Psi (xs j)≤M)
    (ε:ℝ) (hε:0<ε) :
    ∃ R:ℝ,0<R ∧ ∀ᶠj in atTop,
      (extendedLaw P (gs j) (xs j):Measure ℕ) {n:ℕ|R≤(n:ℝ)}≤ENNReal.ofReal ε := by
  obtain ⟨C,hC,N,hN⟩ := law_bounded_mean_tail P
  obtain ⟨G,hG⟩ := TightConnected.connected_unmarked_positive_eventually P
  let R:ℝ:=(C*M+1)/ε
  have hR:0<R := by dsimp only [R];positivity
  refine ⟨R,hR,?_⟩
  filter_upwards [hg.eventually_ge_atTop (N+G+2),hmean] with j hj hν
  rw [extendedLaw_eq_law P (gs j) (by omega)
    (hG (gs j) (by omega) 0 ⟨le_rfl,Analysis.xCritical_pos_parameter⟩) (xs j) (hx j)
    (hG (gs j) (by omega) (xs j) (hx j))]
  apply (hN (gs j) (by omega) _ _ (xs j) (hx j) _ M hM hν R hR).trans
  apply ENNReal.ofReal_le_ofReal
  apply (div_le_iff₀ hR).mpr
  have hh : ε*R=C*M+1 := by dsimp only [R];field_simp
  linarith
end WP.BoltzmannCusp
namespace WP.BoltzmannCusp
open Set MeasureTheory
lemma extendedLaw_integrable_of_bound (P:PsiTheory) (g:ℕ) (x:ℝ)
    (f:ℕ→ℝ) (B:ℝ) (hB:∀n,|f n|≤B) :
    Integrable f (extendedLaw P g x:Measure ℕ) := by
  apply Integrable.of_bound (measurable_of_countable f).aestronglyMeasurable B
  exact ae_of_all _ fun n=>by simpa only [Real.norm_eq_abs] using hB n
lemma extendedLaw_integral_eventually (P:PsiTheory) :
    ∃ G:ℕ,∀ g≥G,∀ x∈Ico (0:ℝ) xCritical,∀ f:ℕ→ℝ,
      (∫n:ℕ,f n ∂(extendedLaw P g x:Measure ℕ))=∑'n,weight P g x n*f n := by
  obtain ⟨G,hG⟩ := TightConnected.connected_unmarked_positive_eventually P
  refine ⟨G+2,?_⟩
  intro g hg x hx f
  rw [extendedLaw_eq_law P g (by omega)
    (hG g (by omega) 0 ⟨le_rfl,Analysis.xCritical_pos_parameter⟩) x hx (hG g (by omega) x hx)]
  exact law_integral _ _ _ _ _ _ _ f
end WP.BoltzmannCusp
