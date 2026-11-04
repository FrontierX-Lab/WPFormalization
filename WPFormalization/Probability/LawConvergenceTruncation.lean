import WPFormalization.Probability.LawConvergenceBadEvent

noncomputable section
universe u v w z
namespace WP.Probability
open Set Filter MeasureTheory
open scoped Topology

/-- Convergence through finite approximants, with an independently controlled
    uniform tail. All source spaces and the approximating limit spaces may vary. -/
theorem lawConverges_of_truncations {E : Type u} [TopologicalSpace E]
    [MeasurableSpace E] [OpensMeasurableSpace E]
    {Ω : ℕ → Type v} [∀ j,MeasurableSpace (Ω j)]
    {ΩK : ℕ → Type w} [∀ K,MeasurableSpace (ΩK K)]
    {Ωlimit : Type z} [MeasurableSpace Ωlimit]
    (μ : (j:ℕ) → Measure (Ω j)) (X : (j:ℕ) → Ω j → E)
    (Y : (K j:ℕ) → Ω j → E) (QK : (K:ℕ) → Measure (ΩK K))
    (ZK : (K:ℕ) → ΩK K → E) (Q : Measure Ωlimit) (Z : Ωlimit → E)
    (hprob : ∀ᶠ j in atTop,IsProbabilityMeasure (μ j))
    (hX : ∀ᶠ j in atTop,AEMeasurable (X j) (μ j))
    (hY : ∀ K,∀ᶠ j in atTop,AEMeasurable (Y K j) (μ j))
    (A : (K j:ℕ) → Set (Ω j))
    (hA : ∀ K,∀ᶠ j in atTop,MeasurableSet (A K j))
    (hXY : ∀ K,∀ᶠ j in atTop,∀ ω,ω ∉ A K j → X j ω=Y K j ω)
    (htail : ∀ ε:ℝ,0<ε → ∃ K0:ℕ,∀ K:ℕ,K0≤K →
      ∀ᶠ j in atTop,(μ j).real (A K j)≤ε)
    (hLaw : ∀ K,LawConverges μ (Y K) (QK K) (ZK K))
    (hLimit : LawConverges QK ZK Q Z) : LawConverges μ X Q Z := by
  intro f
  rw [Metric.tendsto_nhds]
  intro ε hε
  let δ : ℝ := ε/(6*‖f‖+1)
  have hden : 0<6*‖f‖+1 := by positivity
  have hδ : 0<δ := div_pos hε hden
  obtain ⟨K0,hK0⟩ := htail δ hδ
  have hlim := (Metric.tendsto_nhds.mp (hLimit f)) (ε/3) (by positivity)
  obtain ⟨K,hK,hclose⟩ := ((eventually_ge_atTop K0).and hlim).exists
  have hsmall : 2*‖f‖*δ < ε/3 := by
    dsimp only [δ]
    rw [←mul_div_assoc,div_lt_iff₀ hden]
    nlinarith [norm_nonneg f]
  have hlocal := (Metric.tendsto_nhds.mp (hLaw K f)) (ε/3) (by positivity)
  filter_upwards [hprob,hX,hY K,hA K,hXY K,hK0 K hK,hlocal] with j hp hx hy ha hxy htailj hj
  haveI := hp
  have hb := boundedContinuousFunction_integral_sub_le_bad_event (μ j) (X j) (Y K j)
    hx hy (A K j) ha hxy f
  rw [dist_eq_norm] at hj hclose ⊢
  have hbad : ‖(∫ω,f (X j ω) ∂μ j)-(∫ω,f (Y K j ω) ∂μ j)‖ < ε/3 :=
    hb.trans_lt ((mul_le_mul_of_nonneg_left htailj (by positivity)).trans_lt hsmall)
  calc
    _ = ‖((∫ω,f (X j ω) ∂μ j)-(∫ω,f (Y K j ω) ∂μ j)) +
        ((∫ω,f (Y K j ω) ∂μ j)-(∫ω,f (ZK K ω) ∂QK K)) +
        ((∫ω,f (ZK K ω) ∂QK K)-(∫ω,f (Z ω) ∂Q))‖ := by congr 1;ring
    _ ≤ ‖(∫ω,f (X j ω) ∂μ j)-(∫ω,f (Y K j ω) ∂μ j)‖ +
        ‖(∫ω,f (Y K j ω) ∂μ j)-(∫ω,f (ZK K ω) ∂QK K)‖ +
        ‖(∫ω,f (ZK K ω) ∂QK K)-(∫ω,f (Z ω) ∂Q)‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ < ε := by linarith

end WP.Probability
