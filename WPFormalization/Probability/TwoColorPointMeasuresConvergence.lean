import WPFormalization.Probability.TwoColorPointMeasuresBasis
import WPFormalization.External.PointProcessProbability

/-! A local two-color specialization of the existing classical convergence
criterion. All mixed factorial moments remain explicit mathematical premises
of this generic theorem; a geometric application must actually prove them. -/
noncomputable section
namespace WP.Probability
open MeasureTheory Filter Set Topology
open scoped Topology CompactlySupported ENNReal NNReal Classical

lemma twoColorEncode_count_color (ξ : TwoColorPointMeasure) (b : Bool)
    (B : RelCompactBorelWindow ℝ≥0) :
    (twoColorEncode ξ).count TwoColorSpace (twoColorWindow b B)=
      if b then ξ.2.count ℝ≥0 B else ξ.1.count ℝ≥0 B := by
  cases b <;> simp only [twoColorWindow,Bool.false_eq_true,if_false,if_true,
    twoColorEncode_count_left,twoColorEncode_count_right]

lemma twoColorMeasure_colorWindow (νN νP : Measure ℝ≥0) (b : Bool)
    (B : RelCompactBorelWindow ℝ≥0) :
    twoColorMeasure νN νP (twoColorWindow b B).carrier = if b then νP B.carrier else νN B.carrier := by
  cases b <;> simp only [twoColorWindow,Bool.false_eq_true,if_false,if_true,
    twoColorLeftWindow,twoColorRightWindow]
  · exact twoColorMeasure_inl _ _ _ B.measurableSet
  · exact twoColorMeasure_inr _ _ _ B.measurableSet

lemma twoColorEncode_aemeasurable_of_window_counts {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (ΞN ΞP : Ω → PointMeasure ℝ≥0)
    (νN νP : Measure ℝ≥0) [IsLocallyFiniteMeasure νN] [IsLocallyFiniteMeasure νP]
    [NullSingletonClass νN] [NullSingletonClass νP]
    (hN : ∀ B ∈ nnrealRationalWindows,AEMeasurable (fun ω => (ΞN ω).count ℝ≥0 B) μ)
    (hP : ∀ B ∈ nnrealRationalWindows,AEMeasurable (fun ω => (ΞP ω).count ℝ≥0 B) μ) :
    AEMeasurable (fun ω => twoColorEncode (ΞN ω,ΞP ω)) μ := by
  apply WP.External.pointMeasure_aemeasurable_of_basis_counts TwoColorSpace μ _
    (twoColorMeasure νN νP) twoColorRationalWindows (twoColorRationalWindows_basis νN νP)
  intro B hB
  obtain ⟨b,A,hA,rfl⟩ := twoColorRationalWindows_cases hB
  simp_rw [twoColorEncode_count_color]
  cases b
  · exact hN A hA
  · exact hP A hA

/-- Two actual point measures converge jointly to the ordinary PPP on the
disjoint union, provided their genuine colored-window mixed factorial moments
are proved. In particular the target law specifies independent color counts. -/
theorem twoColor_poisson_limit_of_mixed_factorials
    {Ω : ℕ → Type*} [∀ n,MeasurableSpace (Ω n)]
    (μ : (n:ℕ) → Measure (Ω n))
    (ΞN ΞP : (n:ℕ) → Ω n → PointMeasure ℝ≥0)
    (hprob : ∀ᶠ n in atTop,IsProbabilityMeasure (μ n))
    (νN νP : Measure ℝ≥0) [IsLocallyFiniteMeasure νN] [IsLocallyFiniteMeasure νP]
    [NullSingletonClass νN] [NullSingletonClass νP]
    (hcounts : ∀ᶠ n in atTop,
      (∀ B ∈ nnrealRationalWindows,AEMeasurable (fun ω => (ΞN n ω).count ℝ≥0 B) (μ n)) ∧
      (∀ B ∈ nnrealRationalWindows,AEMeasurable (fun ω => (ΞP n ω).count ℝ≥0 B) (μ n)))
    (hmom : ∀ d : ℕ,∀ B : Fin d → RelCompactBorelWindow TwoColorSpace,
      (∀ i,B i ∈ twoColorRationalWindows) → DisjointWindows TwoColorSpace B →
      MixedFactorialMomentLimit μ
        (fun n ω => windowCountVector TwoColorSpace B (twoColorEncode (ΞN n ω,ΞP n ω)))
        (windowRates TwoColorSpace (twoColorMeasure νN νP) B)) :
    ∃ Q : ProbabilityMeasure (PointMeasure TwoColorSpace),
      IsPoissonPointProcessLaw TwoColorSpace (twoColorMeasure νN νP) Q ∧
      LawConverges μ (fun n ω => twoColorEncode (ΞN n ω,ΞP n ω)) Q (fun ξ => ξ) := by
  obtain ⟨Q,hQ⟩ := WP.External.poisson_point_process_exists TwoColorSpace (twoColorMeasure νN νP)
  refine ⟨Q,hQ,?_⟩
  apply WP.External.pointMeasure_vague_of_semiring_mixed_factorials TwoColorSpace μ _
    hprob ?_ (twoColorMeasure νN νP) twoColorRationalWindows (twoColorRationalWindows_basis νN νP) Q hQ hmom
  filter_upwards [hcounts] with n hn
  exact twoColorEncode_aemeasurable_of_window_counts (μ n) (ΞN n) (ΞP n) νN νP hn.1 hn.2

/-- Consumer-facing form: disjointness is required only within each color.
Every order of each mixed factorial moment is still a proved input. -/
theorem twoColor_poisson_limit_of_color_window_factorials
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
      LawConverges μ (fun n ω => twoColorEncode (ΞN n ω,ΞP n ω)) Q (fun ξ => ξ) := by
  apply twoColor_poisson_limit_of_mixed_factorials μ ΞN ΞP hprob νN νP hcounts
  intro d B hB hdis
  choose color A hA hEq using fun i => twoColorRationalWindows_cases (hB i)
  have he : B=fun i => twoColorWindow (color i) (A i) := funext (fun i => (hEq i).symm)
  subst B
  have hd : Pairwise (fun i j => color i=color j → Disjoint (A i).carrier (A j).carrier) := by
    intro i j hij
    exact (twoColorWindow_disjoint_iff (color i) (color j) (A i) (A j)).mp (hdis hij)
  change MixedFactorialMomentLimit μ
    (fun n ω i => (twoColorEncode (ΞN n ω,ΞP n ω)).count TwoColorSpace (twoColorWindow (color i) (A i)))
    (fun i => (twoColorMeasure νN νP (twoColorWindow (color i) (A i)).carrier).toNNReal)
  simp_rw [twoColorEncode_count_color,twoColorMeasure_colorWindow]
  exact hmom d color A hA hd

end WP.Probability
