import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.MeasureTheory.Integral.Lebesgue.Map


/-! Genuine mixtures on a disjoint union of varying measurable fibers.
The count marginal is exactly the supplied PMF. All integral identities are
proved with Mathlib's sum/map measure theorems, with explicit integrability.
No geometric or distribution-specific result is supplied as a hypothesis. -/

noncomputable section
universe u
namespace WP.Probability
open MeasureTheory Set
open scoped ENNReal
variable {Ω : ℕ → Type u} [m : ∀n,MeasurableSpace (Ω n)]

lemma measurable_sigmaMk (n : ℕ) : Measurable (Sigma.mk n : Ω n → Sigma Ω) := by
  intro s hs
  exact (iInf_le (fun n => (m n).map (Sigma.mk n)) n) s hs

def sigmaMixture (p : PMF ℕ) (μ : (n : ℕ) → Measure (Ω n)) : Measure (Sigma Ω) :=
  Measure.sum (fun n => p n • (μ n).map (Sigma.mk n))

lemma sigmaMixture_apply (p : PMF ℕ) (μ : (n : ℕ) → Measure (Ω n))
    (s : Set (Sigma Ω)) (hs : MeasurableSet s) :
    sigmaMixture p μ s = ∑' n,p n * μ n ((Sigma.mk n)⁻¹' s) := by
  rw [sigmaMixture,Measure.sum_apply _ hs]
  apply tsum_congr
  intro n
  rw [Measure.smul_apply,smul_eq_mul,Measure.map_apply (measurable_sigmaMk n) hs]

lemma sigmaMixture_isProbabilityMeasure (p : PMF ℕ) (μ : (n : ℕ) → Measure (Ω n))
    [∀n,IsProbabilityMeasure (μ n)] : IsProbabilityMeasure (sigmaMixture p μ) := by
  apply isProbabilityMeasure_iff.mpr
  rw [sigmaMixture_apply _ _ _ MeasurableSet.univ]
  simpa only [Set.preimage_univ,measure_univ,mul_one] using p.tsum_coe

lemma lintegral_sigmaMixture (p : PMF ℕ) (μ : (n : ℕ) → Measure (Ω n))
    (f : Sigma Ω → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ x,f x ∂sigmaMixture p μ = ∑' n,p n * ∫⁻ω,f ⟨n,ω⟩ ∂μ n := by
  rw [sigmaMixture,lintegral_sum_measure]
  apply tsum_congr
  intro n
  rw [lintegral_smul_measure,smul_eq_mul,lintegral_map hf (measurable_sigmaMk n)]

lemma measurableEmbedding_sigmaMk (n : ℕ) : MeasurableEmbedding (Sigma.mk n : Ω n → Sigma Ω) := by
  refine ⟨?_,measurable_sigmaMk n,?_⟩
  · intro x y h
    exact eq_of_heq (Sigma.mk.inj h).2
  intro s hs
  apply MeasurableSpace.measurableSet_iInf.mpr
  intro j
  change MeasurableSet ((Sigma.mk j : Ω j → Sigma Ω)⁻¹' (Sigma.mk n '' s))
  by_cases h : j=n
  · subst j
    simpa only [Set.preimage_image_eq _ (fun _ _ h => eq_of_heq (Sigma.mk.inj h).2)] using hs
  · have he : (Sigma.mk j : Ω j → Sigma Ω)⁻¹' (Sigma.mk n '' s) = ∅ := by
      ext x
      simp only [Set.mem_preimage,Set.mem_image,Set.mem_empty_iff_false,iff_false]
      rintro ⟨y,_,hy⟩
      have hj := congrArg Sigma.fst hy
      exact h hj.symm
    rw [he]
    exact MeasurableSet.empty

lemma measurable_sigmaElim {E : Type*} [MeasurableSpace E]
    (f : Sigma Ω → E) (hf : ∀n,Measurable (fun ω : Ω n => f ⟨n,ω⟩)) : Measurable f := by
  intro s hs
  apply MeasurableSpace.measurableSet_iInf.mpr
  intro n
  exact hf n hs

lemma measurable_sigmaFst : Measurable (Sigma.fst : Sigma Ω → ℕ) :=
  measurable_sigmaElim _ (fun _ => measurable_const)

lemma sigmaMixture_map_fst (p : PMF ℕ) (μ : (n : ℕ) → Measure (Ω n))
    [∀n,IsProbabilityMeasure (μ n)] :
    (sigmaMixture p μ).map Sigma.fst = p.toMeasure := by
  ext s hs
  rw [Measure.map_apply measurable_sigmaFst hs,
    sigmaMixture_apply _ _ _ (measurable_sigmaFst hs),PMF.toMeasure_apply _ hs]
  apply tsum_congr
  intro n
  by_cases hn : n∈s
  · have he : (Sigma.mk n : Ω n → Sigma Ω)⁻¹' Sigma.fst⁻¹' s = Set.univ := by ext x;simpa using hn
    simp [he,hn]
  · have he : (Sigma.mk n : Ω n → Sigma Ω)⁻¹' Sigma.fst⁻¹' s = ∅ := by ext x;simp [hn]
    simp [he,hn]

lemma integral_sigmaMixture (p : PMF ℕ) (μ : (n : ℕ) → Measure (Ω n))
    (f : Sigma Ω → ℝ) (hi : Integrable f (sigmaMixture p μ)) :
    ∫x,f x ∂sigmaMixture p μ = ∑'n,(p n).toReal * ∫ω,f ⟨n,ω⟩ ∂μ n := by
  rw [sigmaMixture,integral_sum_measure hi]
  apply tsum_congr
  intro n
  rw [integral_smul_measure,
    (measurableEmbedding_sigmaMk n).integral_map,smul_eq_mul]

lemma integrable_sigmaMixture_bounded (p : PMF ℕ) (μ : (n : ℕ) → Measure (Ω n))
    [∀n,IsProbabilityMeasure (μ n)] (f : Sigma Ω → ℝ) (hf : Measurable f)
    (C : ℝ) (hC : ∀x,‖f x‖ ≤ C) : Integrable f (sigmaMixture p μ) := by
  let _ := sigmaMixture_isProbabilityMeasure p μ
  exact (integrable_const C).mono' hf.aestronglyMeasurable (ae_of_all _ hC)

end WP.Probability
