import WPFormalization.Probability.PointMeasureDefinitions
/-! A local varying-probability-space Slutsky theorem on metric spaces.
The proof uses Mathlib's bounded-Lipschitz weak convergence criterion and an
explicit exceptional-event integral bound. No additive structure on the
observable space, fixed source probability space, or external probability
input is needed. Eventual hypotheses are handled by a cofinal shift. -/
noncomputable section
namespace WP.Probability
open MeasureTheory Set Filter
open scoped ENNReal Topology

lemma integral_abs_le_of_small_exception {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → ℝ) (hi : Integrable f μ)
    (B : Set Ω) (hB : NullMeasurableSet B μ) (M δ : ℝ)
    (hδ : 0≤δ) (hbound : ∀ω,|f ω|≤M)
    (hsmall : ∀ω,ω∉B→|f ω|≤δ) :
    |∫ω,f ω ∂μ|≤δ+M*μ.real B := by
  have hinorm : Integrable (fun ω => |f ω|) μ := by
    simpa only [Real.norm_eq_abs] using hi.norm
  calc
    |∫ω,f ω ∂μ| ≤ ∫ω,|f ω| ∂μ := by simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm f
    _ = (∫ω in Bᶜ,|f ω| ∂μ)+(∫ω in B,|f ω| ∂μ) := by
      exact (integral_add_compl₀ hB.compl hi.norm).symm.trans (by simp)
    _ ≤ (∫_ in Bᶜ,δ ∂μ)+(∫_ in B,M ∂μ) := by
      apply add_le_add
      · exact setIntegral_mono_on₀ hinorm.integrableOn integrableOn_const hB.compl hsmall
      · exact setIntegral_mono hinorm.integrableOn integrableOn_const hbound
    _ = δ*μ.real Bᶜ+M*μ.real B := by simp [integral_const,smul_eq_mul,mul_comm]
    _ ≤ δ+M*μ.real B := by
      gcongr
      grw [measureReal_le_one,mul_one]

lemma lawConverges_prodMk_const {Ω : ℕ → Type*} [∀j,MeasurableSpace (Ω j)]
    {E : Type*} [PseudoMetricSpace E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E]
    {S : Type*} [PseudoMetricSpace S] [MeasurableSpace S] [BorelSpace S]
    [SecondCountableTopology S] {Ωlimit : Type*} [MeasurableSpace Ωlimit]
    (μ : (j : ℕ) → Measure (Ω j)) [∀j,IsProbabilityMeasure (μ j)]
    (X : (j : ℕ) → Ω j → E) (R : (j : ℕ) → Ω j → S)
    (Q : Measure Ωlimit) [IsProbabilityMeasure Q] (Z : Ωlimit → E) (c : S)
    (hX : ∀j,AEMeasurable (X j) (μ j)) (hR : ∀j,AEMeasurable (R j) (μ j))
    (hZ : AEMeasurable Z Q) (hLaw : LawConverges μ X Q Z)
    (hconv : ∀δ>0,Tendsto (fun j => (μ j).real {ω | δ≤dist (R j ω) c}) atTop (𝓝 0)) :
    LawConverges μ (fun j ω => (X j ω,R j ω)) Q (fun ω => (Z ω,c)) := by
  have hpair : ∀j,AEMeasurable (fun ω => (X j ω,R j ω)) (μ j) :=
    fun j => (hX j).prodMk (hR j)
  have hZc : AEMeasurable (fun ω => (Z ω,c)) Q := hZ.prodMk aemeasurable_const
  apply (lawConverges_iff_tendstoInDistribution μ _ Q _ hpair hZc).mpr
  refine ⟨hpair,hZc,?_⟩
  apply tendsto_iff_forall_lipschitz_integral_tendsto.mpr
  rintro F hFbounded ⟨L,hFlip⟩
  let fbc : BoundedContinuousFunction (E×S) ℝ := {
    toFun := F
    continuous_toFun := hFlip.continuous
    map_bounded' := hFbounded }
  let fbase : BoundedContinuousFunction E ℝ := {
    toFun := fun x => F (x,c)
    continuous_toFun := hFlip.continuous.comp (continuous_id.prodMk continuous_const)
    map_bounded' := by obtain ⟨M,hM⟩ := hFbounded;exact ⟨M,fun x y=>hM (x,c) (y,c)⟩ }
  have hbase := hLaw fbase
  change Tendsto (fun j => ∫ω,F (X j ω,c) ∂μ j) atTop
    (𝓝 (∫ω,F (Z ω,c) ∂Q)) at hbase
  have hiR (j : ℕ) : Integrable (fun ω => F (X j ω,R j ω)) (μ j) :=
    Integrable.of_bound (hFlip.continuous.measurable.comp_aemeasurable (hpair j)).aestronglyMeasurable
      ‖fbc‖ (ae_of_all _ fun ω => fbc.norm_coe_le_norm _)
  have hiC (j : ℕ) : Integrable (fun ω => F (X j ω,c)) (μ j) :=
    Integrable.of_bound (hFlip.continuous.measurable.comp_aemeasurable
      ((hX j).prodMk aemeasurable_const)).aestronglyMeasurable
      ‖fbc‖ (ae_of_all _ fun ω => fbc.norm_coe_le_norm _)
  obtain ⟨M,hM⟩ := hFbounded
  have hdiff : Tendsto (fun j => (∫ω,F (X j ω,R j ω) ∂μ j)-
      (∫ω,F (X j ω,c) ∂μ j)) atTop (𝓝 0) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    let δ : ℝ := ε/((L:ℝ)+1)
    have hδ : 0<δ := by dsimp [δ];positivity
    have hlim : (L:ℝ)*δ<ε := by
      dsimp [δ]
      rw [←mul_div_assoc]
      apply (div_lt_iff₀ (by positivity : 0<(L:ℝ)+1)).mpr
      nlinarith
    have ht := ((hconv δ hδ).const_mul M).const_add ((L:ℝ)*δ)
    have he : ∀ᶠj in atTop,(L:ℝ)*δ+M*(μ j).real {ω | δ≤dist (R j ω) c}<ε := by
      have ht' : Tendsto (fun j => (L:ℝ)*δ+M*(μ j).real {ω | δ≤dist (R j ω) c})
          atTop (𝓝 ((L:ℝ)*δ)) := by simpa only [mul_zero,add_zero] using ht
      exact ht'.eventually_lt_const hlim
    filter_upwards [he] with j hj
    have hb := integral_abs_le_of_small_exception (μ j)
      (fun ω => F (X j ω,R j ω)-F (X j ω,c)) ((hiR j).sub (hiC j))
      {ω | δ≤dist (R j ω) c}
      (nullMeasurableSet_le aemeasurable_const
        ((hR j).dist aemeasurable_const)) M ((L:ℝ)*δ)
      (by positivity)
      (fun ω => by simpa only [Real.dist_eq] using hM (X j ω,R j ω) (X j ω,c))
      (fun ω hω => by
        have hsmall : dist (R j ω) c≤δ := le_of_lt (not_le.mp hω)
        have hd : dist (X j ω,R j ω) (X j ω,c)≤δ := by
          simp only [Prod.dist_eq,dist_self]
          exact max_le hδ.le hsmall
        simpa only [Real.dist_eq] using hFlip.dist_le_mul_of_le hd)
    rw [integral_sub (hiR j) (hiC j)] at hb
    simpa only [Real.dist_eq,sub_zero] using lt_of_le_of_lt hb hj
  have ht := hdiff.add hbase
  have hmap (j : ℕ) : (∫x,F x ∂(μ j).map (fun ω => (X j ω,R j ω)))=
      ∫ω,F (X j ω,R j ω) ∂μ j := integral_map (hpair j) hFlip.continuous.aestronglyMeasurable
  have hmapQ : (∫x,F x ∂Q.map (fun ω => (Z ω,c)))=∫ω,F (Z ω,c) ∂Q :=
    integral_map hZc hFlip.continuous.aestronglyMeasurable
  simpa only [ProbabilityMeasure.coe_mk,hmap,hmapQ,fbase,sub_add_cancel,zero_add] using ht

lemma lawConverges_prodMk_const_eventually {Ω : ℕ → Type*} [∀j,MeasurableSpace (Ω j)]
    {E : Type*} [PseudoMetricSpace E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E]
    {S : Type*} [PseudoMetricSpace S] [MeasurableSpace S] [BorelSpace S]
    [SecondCountableTopology S] {Ωlimit : Type*} [MeasurableSpace Ωlimit]
    (μ : (j : ℕ) → Measure (Ω j))
    (X : (j : ℕ) → Ω j → E) (R : (j : ℕ) → Ω j → S)
    (Q : Measure Ωlimit) [IsProbabilityMeasure Q] (Z : Ωlimit → E) (c : S)
    (hprob : ∀ᶠj in atTop,IsProbabilityMeasure (μ j))
    (hX : ∀ᶠj in atTop,AEMeasurable (X j) (μ j))
    (hR : ∀ᶠj in atTop,AEMeasurable (R j) (μ j))
    (hZ : AEMeasurable Z Q) (hLaw : LawConverges μ X Q Z)
    (hconv : ∀δ>0,Tendsto (fun j => (μ j).real {ω | δ≤dist (R j ω) c}) atTop (𝓝 0)) :
    LawConverges μ (fun j ω => (X j ω,R j ω)) Q (fun ω => (Z ω,c)) := by
  obtain ⟨N,hN⟩ := eventually_atTop.mp (hprob.and (hX.and hR))
  let μ' : (j : ℕ) → Measure (Ω (j+N)) := fun j => μ (j+N)
  let : ∀j,IsProbabilityMeasure (μ' j) := fun j => (hN (j+N) (by omega)).1
  have hs := lawConverges_prodMk_const μ' (fun j => X (j+N)) (fun j => R (j+N)) Q Z c
    (fun j => (hN (j+N) (by omega)).2.1)
    (fun j => (hN (j+N) (by omega)).2.2) hZ
    (fun f => (hLaw f).comp (tendsto_add_atTop_nat N))
    (fun δ hδ => (hconv δ hδ).comp (tendsto_add_atTop_nat N))
  intro f
  exact (tendsto_add_atTop_iff_nat N).mp (hs f)

lemma lawConverges_continuous_comp {Ω : ℕ → Type*} [∀j,MeasurableSpace (Ω j)]
    {E F : Type*} [TopologicalSpace E] [TopologicalSpace F]
    {Ωlimit : Type*} [MeasurableSpace Ωlimit]
    (μ : (j : ℕ) → Measure (Ω j)) (X : (j : ℕ) → Ω j → E)
    (Q : Measure Ωlimit) (Z : Ωlimit → E) (f : E → F) (hf : Continuous f)
    (hLaw : LawConverges μ X Q Z) :
    LawConverges μ (fun j ω => f (X j ω)) Q (fun ω => f (Z ω)) := by
  intro h
  exact hLaw (h.compContinuous ⟨f,hf⟩)

end WP.Probability
