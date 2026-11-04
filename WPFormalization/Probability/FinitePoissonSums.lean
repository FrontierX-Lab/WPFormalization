import WPFormalization.Probability.LawConvergenceBadEvent

noncomputable section
universe u v w z
namespace WP.Probability
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal NNReal

theorem lawConverges_continuous_map {E : Type u} [TopologicalSpace E]
    {F : Type v} [TopologicalSpace F] {Ω : ℕ → Type w} [∀j,MeasurableSpace (Ω j)]
    {Ω0 : Type z} [MeasurableSpace Ω0] (μ : (j:ℕ)→Measure (Ω j))
    (X : (j:ℕ)→Ω j→E) (Q : Measure Ω0) (Z : Ω0→E)
    (h : LawConverges μ X Q Z) (f : E→F) (hf : Continuous f) :
    LawConverges μ (fun j ω => f (X j ω)) Q (fun ω => f (Z ω)) := by
  intro b
  exact h (b.compContinuous ⟨f,hf⟩)

lemma poissonMeasure_zero_eq_dirac : poissonMeasure 0=Measure.dirac 0 := by
  apply Measure.ext_of_singleton
  intro n
  cases n with
  | zero => simp [poissonMeasure_singleton]
  | succ n => simp [poissonMeasure_singleton]

lemma independent_poisson_finset_sum {Ω : Type*} [MeasurableSpace Ω]
    {ι : Type*} [DecidableEq ι] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ι→Ω→ℕ) (r : ι→ℝ≥0) (hX : ∀i,Measurable (X i))
    (hi : iIndepFun X μ) (hr : ∀i,HasLaw (X i) (poissonMeasure (r i)) μ)
    (s : Finset ι) : HasLaw (fun ω => ∑i∈s,X i ω) (poissonMeasure (∑i∈s,r i)) μ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    constructor
    · simpa only [Finset.sum_empty] using (measurable_const : Measurable (fun _:Ω=>(0:ℕ))).aemeasurable
    · simp [Measure.map_const,poissonMeasure_zero_eq_dirac]
  | @insert a s ha ih =>
    have ih' : HasLaw (∑j∈s,X j) (poissonMeasure (∑j∈s,r j)) μ := by
      convert ih using 1
      funext ω
      simp only [Finset.sum_apply]
    have hsum := (hi.indepFun_finsetSum_of_notMem hX ha).symm.hasLaw_add_poissonMeasure (hr a) ih'
    convert hsum using 1
    · funext ω
      simp only [Finset.sum_insert ha,Pi.add_apply,Finset.sum_apply]
    · simp only [Finset.sum_insert ha]

lemma poisson_sum_hasLaw {K:ℕ} (r : Fin K→ℝ≥0) :
    HasLaw (fun z:Fin K→ℕ => ∑i,z i) (poissonMeasure (∑i,r i)) (productPoissonMeasure r) := by
  apply independent_poisson_finset_sum
  · intro i; exact measurable_pi_apply i
  · exact iIndepFun_pi (fun _ => measurable_id.aemeasurable)
  · intro i
    exact (measurePreserving_eval (fun i=>poissonMeasure (r i)) i).hasLaw

/-- Summing each finite block of independent Poisson coordinates gives independent
Poisson coordinates with the summed rates. Empty blocks and zero rates are included. -/
lemma poisson_block_sums_hasLaw {d K:ℕ} (r : Fin d→Fin K→ℝ≥0) :
    HasLaw (fun z:Fin d→Fin K→ℕ => fun i=>∑k,z i k)
      (productPoissonMeasure (fun i=>∑k,r i k))
      (Measure.pi (fun i=>productPoissonMeasure (r i))) := by
  let f : (Fin K→ℕ)→ℕ := fun z=>∑k,z k
  have hmeas : Measurable f := by fun_prop
  refine ⟨(Measurable.of_eval (fun i=>hmeas.comp (measurable_pi_apply i))).aemeasurable,?_⟩
  exact (measurePreserving_pi (fun i=>productPoissonMeasure (r i))
    (fun i=>poissonMeasure (∑k,r i k))
    (fun i=>⟨hmeas,(poisson_sum_hasLaw (r i)).map_eq⟩)).map_eq

/-- Finite sums of coordinates preserve count-vector weak limits. -/
theorem lawConverges_poisson_block_sums {d K:ℕ} {Ω:ℕ→Type*}
    [∀j,MeasurableSpace (Ω j)] (μ:(j:ℕ)→Measure (Ω j))
    (X:(j:ℕ)→Ω j→Fin d→Fin K→ℕ) (r:Fin d→Fin K→ℝ≥0)
    (h : LawConverges μ X (Measure.pi (fun i=>productPoissonMeasure (r i))) id) :
    LawConverges μ (fun j ω i=>∑k,X j ω i k)
      (productPoissonMeasure (fun i=>∑k,r i k)) id := by
  have hm := lawConverges_continuous_map μ X _ id h
    (fun z:Fin d→Fin K→ℕ => fun i=>∑k,z i k) continuous_of_discreteTopology
  intro b
  have hb : (∫z:Fin d→Fin K→ℕ,b (fun i=>∑k,z i k) ∂Measure.pi (fun i=>productPoissonMeasure (r i))) =
      (∫z,b z ∂productPoissonMeasure (fun i=>∑k,r i k)) := by
    simpa only [Function.comp_def] using (poisson_block_sums_hasLaw r).integral_comp b.continuous.measurable.aestronglyMeasurable
  simpa only [id_eq,hb] using hm b

/-- A finite coordinate regrouping preserves the actual product Poisson law. -/
lemma poisson_flat_to_blocks_hasLaw {d K:ℕ} (e : Fin (d*K) ≃ Fin d × Fin K)
    (r : Fin (d*K)→ℝ≥0) :
    HasLaw (fun z:Fin (d*K)→ℕ => fun i k=>z (e.symm (i,k)))
      (Measure.pi (fun i=>productPoissonMeasure (fun k=>r (e.symm (i,k)))))
      (productPoissonMeasure r) := by
  have hgroup : Measurable (fun z:Fin (d*K)→ℕ => fun i k=>z (e.symm (i,k))) :=
    Measurable.of_eval (fun i=>Measurable.of_eval (fun k=>measurable_pi_apply _))
  refine ⟨hgroup.aemeasurable,?_⟩
  apply Measure.ext_of_singleton
  intro z
  rw [Measure.map_apply hgroup (measurableSet_singleton z)]
  have hp : (fun x:Fin (d*K)→ℕ => fun i k=>x (e.symm (i,k))) ⁻¹' {z} =
      {fun a:Fin (d*K)=>z (e a).1 (e a).2} := by
    ext x
    simp only [mem_preimage,mem_singleton_iff]
    constructor
    · intro hx
      funext a
      have he := congrFun (congrFun hx (e a).1) (e a).2
      simpa only [Prod.mk.eta,e.symm_apply_apply] using he
    · intro hx
      subst x
      funext i k
      simp
  rw [hp]
  simp only [productPoissonMeasure,Measure.pi_singleton]
  calc
    _ = ∏p:Fin d×Fin K,poissonMeasure (r (e.symm p)) {z p.1 p.2} :=
      Fintype.prod_equiv e _ _ (fun a=>by simp)
    _ = _ := Fintype.prod_prod_type _

/-- The directly consumable flattened count-vector form. -/
theorem lawConverges_flat_poisson_block_sums {d K:ℕ} {Ω:ℕ→Type*}
    [∀j,MeasurableSpace (Ω j)] (μ:(j:ℕ)→Measure (Ω j))
    (X:(j:ℕ)→Ω j→Fin (d*K)→ℕ) (e:Fin (d*K)≃Fin d×Fin K)
    (r:Fin (d*K)→ℝ≥0) (h : LawConverges μ X (productPoissonMeasure r) id) :
    LawConverges μ (fun j ω i=>∑k,X j ω (e.symm (i,k)))
      (productPoissonMeasure (fun i=>∑k,r (e.symm (i,k)))) id := by
  have hm := lawConverges_continuous_map μ X _ id h
    (fun z:Fin (d*K)→ℕ => fun i k=>z (e.symm (i,k))) continuous_of_discreteTopology
  have hblocks : LawConverges μ (fun j ω i k=>X j ω (e.symm (i,k)))
      (Measure.pi (fun i=>productPoissonMeasure (fun k=>r (e.symm (i,k))))) id := by
    intro b
    have hb : (∫z:Fin (d*K)→ℕ,b (fun i k=>z (e.symm (i,k))) ∂productPoissonMeasure r) =
        (∫z,b z ∂Measure.pi (fun i=>productPoissonMeasure (fun k=>r (e.symm (i,k))))) := by
      simpa only [Function.comp_def] using (poisson_flat_to_blocks_hasLaw e r).integral_comp b.continuous.measurable.aestronglyMeasurable
    simpa only [id_eq,hb] using hm b
  exact lawConverges_poisson_block_sums μ _ _ hblocks

end WP.Probability
