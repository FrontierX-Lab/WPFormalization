import WPFormalization.Probability.SigmaMixture
import WPFormalization.Probability.PointMeasureDefinitions
/-! Averaging deterministic conditional convergence over an arbitrary changing
PMF on genuinely varying measurable fibers. Uniformity in the count index is
proved from the all-sequences premise. Only eventual fiberwise probability and
a.e. measurability are required; no global representative or external theorem
is assumed. -/
noncomputable section
universe u v w
namespace WP.Probability
open MeasureTheory Filter Set
open scoped ENNReal Topology

lemma aemeasurable_sigmaMixture {Ω : ℕ → Type u} [∀n,MeasurableSpace (Ω n)]
    {E : Type v} [MeasurableSpace E] (p : PMF ℕ) (μ : (n : ℕ) → Measure (Ω n))
    (X : Sigma Ω → E) (hX : ∀ n,AEMeasurable (fun ω : Ω n => X ⟨n,ω⟩) (μ n)) :
    AEMeasurable X (sigmaMixture p μ) := by
  rw [sigmaMixture,aemeasurable_sum_measure_iff]
  intro n
  exact ((measurableEmbedding_sigmaMk n).aemeasurable_map_iff.mpr (hX n)).smul_measure _

lemma integrable_sigmaMixture_ae_bounded {Ω : ℕ → Type u} [∀n,MeasurableSpace (Ω n)]
    (p : PMF ℕ) (μ : (n : ℕ) → Measure (Ω n)) [∀n,IsProbabilityMeasure (μ n)]
    (f : Sigma Ω → ℝ) (hf : ∀ n,AEMeasurable (fun ω : Ω n => f ⟨n,ω⟩) (μ n))
    (C : ℝ) (hC : ∀x,‖f x‖≤C) : Integrable f (sigmaMixture p μ) := by
  let _ := sigmaMixture_isProbabilityMeasure p μ
  exact (integrable_const C).mono'
    (aemeasurable_sigmaMixture p μ f hf).aestronglyMeasurable (ae_of_all _ hC)

lemma uniform_atTop_of_all_sequences (a : ℕ → ℕ → ℝ) (L : ℝ)
    (h : ∀ (gs : ℕ → ℕ),Tendsto gs atTop atTop → ∀ ns : ℕ → ℕ,
      Tendsto (fun j => a (gs j) (ns j)) atTop (𝓝 L)) (ε : ℝ) (hε : 0<ε) :
    ∃ N : ℕ,∀ g≥N,∀ n,|a g n-L|<ε := by
  by_contra hb
  push Not at hb
  choose gs hgs ns hbad using hb
  have hg : Tendsto gs atTop atTop := tendsto_atTop_mono hgs tendsto_id
  have he := (Metric.tendsto_nhds.mp (h gs hg ns)) ε hε
  have hall : ∀ᶠ j in atTop,False := he.mono fun j hj => by
    have : |a (gs j) (ns j)-L|<ε := by simpa only [Real.dist_eq] using hj
    exact (not_lt_of_ge (hbad j)) this
  exact (Filter.Eventually.exists hall).elim (fun _ hj => hj)

lemma pmf_average_error_le (p : PMF ℕ) (a : ℕ → ℝ) (L ε : ℝ)
    (h : ∀ n,|a n-L|≤ε) : |(∑'n,(p n).toReal*a n)-L|≤ε := by
  have hi : Integrable a p.toMeasure := by
    apply (integrable_const (ε+|L|)).mono' (measurable_of_countable a).aestronglyMeasurable
    apply ae_of_all
    intro n
    rw [Real.norm_eq_abs]
    calc |a n| = |(a n-L)+L| := by ring_nf
         _ ≤ |a n-L|+|L| := abs_add_le _ _
         _ ≤ ε+|L| := by linarith [h n]
  have he : (∫ n,a n ∂p.toMeasure)=∑'n,(p n).toReal*a n := by
    rw [integral_countable hi]
    apply tsum_congr
    intro n
    simp only [measureReal_def,p.toMeasure_apply_singleton n (measurableSet_singleton n),smul_eq_mul]
  rw [←he]
  have hs : |(∫ n,a n ∂p.toMeasure)-L|=|∫ n,a n-L ∂p.toMeasure| := by
    simp [integral_sub hi (integrable_const L)]
  rw [hs]
  have hb := norm_integral_le_of_norm_le_const (μ:=p.toMeasure)
    (f:=fun n => a n-L) (C:=ε) (ae_of_all _ fun n => by simpa only [Real.norm_eq_abs] using h n)
  simpa only [Real.norm_eq_abs,measureReal_def,measure_univ,ENNReal.toReal_one,mul_one] using hb

/-- Uniform convergence of every deterministic conditional law survives an
arbitrary genus-dependent PMF average on the genuine varying sigma space.
Probability and a.e. measurability are needed only eventually, uniformly in n. -/
lemma lawConverges_sigmaMixture {Ω : ℕ → ℕ → Type u}
    [∀g n,MeasurableSpace (Ω g n)]
    {E : Type v} [TopologicalSpace E] [MeasurableSpace E] [OpensMeasurableSpace E]
    {Ωlimit : Type w} [MeasurableSpace Ωlimit]
    (μ : (g n : ℕ) → Measure (Ω g n)) (X : (g n : ℕ) → Ω g n → E)
    (Q : Measure Ωlimit) (Z : Ωlimit → E) (pg : ℕ → PMF ℕ)
    (hprob : ∀ᶠ g in atTop,∀n,IsProbabilityMeasure (μ g n))
    (hX : ∀ᶠ g in atTop,∀n,AEMeasurable (X g n) (μ g n))
    (hseq : ∀ (gs : ℕ → ℕ),Tendsto gs atTop atTop → ∀ ns : ℕ → ℕ,
      LawConverges (fun j => μ (gs j) (ns j))
        (fun j => X (gs j) (ns j)) Q Z) :
    LawConverges (fun g => sigmaMixture (pg g) (μ g))
      (fun g (s : Sigma (Ω g)) => X g s.1 s.2) Q Z := by
  intro f
  let a : ℕ → ℕ → ℝ := fun g n => ∫ω,f (X g n ω) ∂μ g n
  let L : ℝ := ∫ω,f (Z ω) ∂Q
  have hscalar : ∀ (gs : ℕ → ℕ),Tendsto gs atTop atTop → ∀ ns : ℕ → ℕ,
      Tendsto (fun j => a (gs j) (ns j)) atTop (𝓝 L) := by
    intro gs hgs ns
    exact hseq gs hgs ns f
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨N,hN⟩ := uniform_atTop_of_all_sequences a L hscalar (ε/2) (half_pos hε)
  filter_upwards [hprob,hX,eventually_ge_atTop N] with g hpg hxg hg
  let : ∀n,IsProbabilityMeasure (μ g n) := hpg
  have hi : Integrable (fun s : Sigma (Ω g) => f (X g s.1 s.2))
      (sigmaMixture (pg g) (μ g)) :=
    integrable_sigmaMixture_ae_bounded (pg g) (μ g) _
      (fun n => f.continuous.measurable.comp_aemeasurable (hxg n)) ‖f‖
      (fun s => f.norm_coe_le_norm _)
  have he := integral_sigmaMixture (pg g) (μ g) (fun s => f (X g s.1 s.2)) hi
  have hb := pmf_average_error_le (pg g) (a g) L (ε/2)
    (fun n => (hN g hg n).le)
  rw [Real.dist_eq,he]
  exact lt_of_le_of_lt hb (half_lt_self hε)

end WP.Probability
