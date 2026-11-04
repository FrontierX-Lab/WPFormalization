import WPFormalization.Probability.TwoColorPointMeasuresConvergence
import WPFormalization.Probability.TwoColorPointMeasuresHomeomorph

/-! Genuine weak convergence of the pair is exactly weak convergence of its
sum-space encoding, using the proved homeomorphism of vague topologies. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace WP.Probability
open MeasureTheory Filter Set Topology
open scoped Topology CompactlySupported ENNReal NNReal Classical

lemma lawConverges_twoColor_iff {Ω : ℕ → Type u} [∀ n,MeasurableSpace (Ω n)]
    {Ωlimit : Type v} [MeasurableSpace Ωlimit]
    (μ : (n:ℕ) → Measure (Ω n)) (Ξ : (n:ℕ) → Ω n → TwoColorPointMeasure)
    (μlimit : Measure Ωlimit) (Z : Ωlimit → PointMeasure TwoColorSpace) :
    LawConverges μ (fun n ω => twoColorEncode (Ξ n ω)) μlimit Z ↔
      LawConverges μ Ξ μlimit (fun ω => twoColorDecode (Z ω)) := by
  constructor
  · intro h f
    have ht := h (f.compContinuous ⟨twoColorDecode,twoColorDecode_continuous⟩)
    simpa only [BoundedContinuousFunction.compContinuous_apply,ContinuousMap.coe_mk,twoColorDecode_encode] using ht
  · intro h f
    have ht := h (f.compContinuous ⟨twoColorEncode,twoColorEncode_continuous⟩)
    simpa only [BoundedContinuousFunction.compContinuous_apply,ContinuousMap.coe_mk,twoColorEncode_decode] using ht

/-- The same generic factorial criterion, with the actual pair-valued vague
limit. The PPP on the disjoint union specifies all independent color counts. -/
theorem twoColor_poisson_pair_limit_of_color_window_factorials
    {Ω : ℕ → Type*} [∀ n,MeasurableSpace (Ω n)]
    (μ : (n:ℕ) → Measure (Ω n))
    (ΞN ΞP : (n:ℕ) → Ω n → PointMeasure ℝ≥0)
    (hprob : ∀ᶠ n in atTop,IsProbabilityMeasure (μ n))
    (νN νP : Measure ℝ≥0) [IsLocallyFiniteMeasure νN] [IsLocallyFiniteMeasure νP]
    [NullSingletonClass νN] [NullSingletonClass νP]
    (hcounts : ∀ᶠ n in atTop,
      (∀ B ∈ nnrealRationalWindows,AEMeasurable (fun ω => (ΞN n ω).count ℝ≥0 B) (μ n)) ∧
      (∀ B ∈ nnrealRationalWindows,AEMeasurable (fun ω => (ΞP n ω).count ℝ≥0 B) (μ n)))
    (hmom : ∀ d : ℕ,∀ color : Fin d → Bool,∀ B : Fin d → RelCompactBorelWindow ℝ≥0,
      (∀ i,B i ∈ nnrealRationalWindows) →
      Pairwise (fun i j => color i=color j → Disjoint (B i).carrier (B j).carrier) →
      MixedFactorialMomentLimit μ
        (fun n ω i => if color i then (ΞP n ω).count ℝ≥0 (B i) else (ΞN n ω).count ℝ≥0 (B i))
        (fun i => (if color i then νP (B i).carrier else νN (B i).carrier).toNNReal)) :
    ∃ Q : ProbabilityMeasure (PointMeasure TwoColorSpace),
      IsPoissonPointProcessLaw TwoColorSpace (twoColorMeasure νN νP) Q ∧
      LawConverges μ (fun n ω => (ΞN n ω,ΞP n ω)) Q twoColorDecode := by
  obtain ⟨Q,hQ,hconv⟩ := twoColor_poisson_limit_of_color_window_factorials μ ΞN ΞP hprob νN νP hcounts hmom
  refine ⟨Q,hQ,?_⟩
  exact (lawConverges_twoColor_iff μ (fun n ω => (ΞN n ω,ΞP n ω)) Q (fun ξ => ξ)).mp hconv

end WP.Probability
