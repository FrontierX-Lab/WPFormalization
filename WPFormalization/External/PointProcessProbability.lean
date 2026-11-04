import WPFormalization.Probability.PointMeasureDefinitions

/-! Stage-one deferred classical probability results.

The declarations below are independently source/type reviewed. The original
eight are registered under PROB-POINT-BOREL, PROB-FACTORIAL-POS,
PROB-FACTORIAL-ZERO, PROB-PPP-EXISTS, and PROB-VAGUE-COUNTS; the separately
approved count-law corollary belongs to the last group. The exact deferred
roots are tracked in `audit/phase1-external-inputs.json`. Their `sorry`s remain
explicit classical external dependencies; they are not machine-checked proofs.

Sources: Hide--Thomas arXiv:2209.15568v3, Proposition 3.1;
Kallenberg, Foundations of Modern Probability, second edition (2002),
Theorems A2.3(iv) and 16.16(iii) => (i); Last--Penrose, Lectures on the
Poisson Process, author manuscript (21 August 2017), Theorem 3.6.
The prefix/basis, zero-rate, and semiring forms are explicitly identified
as generic classical corollaries. No declaration concerns a WP geometric
object, a paper-specific moment estimate, or a planar type tail.
-/
noncomputable section
universe u v
namespace WP.External
open WP.Probability MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal

/-- Kallenberg (2002), Theorem A2.3(iv), restricted to integer-valued measures.
The measurable space is Borel for the genuine compact-support-integral vague topology. -/
theorem pointMeasure_count_measurable (E : Type u) [TopologicalSpace E]
    [MeasurableSpace E] [BorelSpace E] [T2Space E] [LocallyCompactSpace E]
    [SecondCountableTopology E] (B : RelCompactBorelWindow E) :
    Measurable (fun ξ : PointMeasure E => ξ.count E B) := by
  sorry

/-- Countable prefix-generator specialization of Kallenberg A2.3(iv) on the
nonnegative real line, including the origin. Actual geometric CDF counts
therefore suffice to prove genuine vague-Borel process measurability. -/
theorem pointMeasure_nnreal_aemeasurable_of_prefix_counts {Ω : Type v}
    [MeasurableSpace Ω] (μ : Measure Ω) (Ξ : Ω → PointMeasure ℝ≥0)
    (hcounts : ∀ b : ℝ≥0,
      AEMeasurable (fun ω => (Ξ ω).count ℝ≥0 (nnrealPrefixWindow b)) μ) :
    AEMeasurable Ξ μ := by
  sorry

/-- Hide--Thomas, arXiv:2209.15568v3, Proposition 3.1, p.7.
The source has strictly positive rates. Eventual probability/measurability is
the cofinal-shift version of its varying-probability-space formulation.
Extended nonnegative expectation records genuine factorial moments, including
all zero and mixed orders. -/
theorem factorial_moments_poisson_positive {d : ℕ} {Ω : ℕ → Type v}
    [∀ n, MeasurableSpace (Ω n)] (μ : (n : ℕ) → Measure (Ω n))
    (X : (n : ℕ) → Ω n → Fin d → ℕ)
    (hprob : ∀ᶠ n in atTop, IsProbabilityMeasure (μ n))
    (hX : ∀ᶠ n in atTop, AEMeasurable (X n) (μ n))
    (rates : Fin d → ℝ≥0) (hrates : ∀ i, 0 < rates i)
    (hmom : MixedFactorialMomentLimit μ X rates) :
    LawConverges μ X (productPoissonMeasure rates) (fun z => z) := by
  sorry

/-- Classical corollary of the preceding positive-rate theorem: discard every
zero-rate coordinate by Markov's inequality and its first factorial moment,
use a finite union bound, and reinsert deterministic zero coordinates.
This is explicitly a sourced corollary, not the literal positive-rate source. -/
theorem factorial_moments_poisson_nonneg {d : ℕ} {Ω : ℕ → Type v}
    [∀ n, MeasurableSpace (Ω n)] (μ : (n : ℕ) → Measure (Ω n))
    (X : (n : ℕ) → Ω n → Fin d → ℕ)
    (hprob : ∀ᶠ n in atTop, IsProbabilityMeasure (μ n))
    (hX : ∀ᶠ n in atTop, AEMeasurable (X n) (μ n))
    (rates : Fin d → ℝ≥0) (hmom : MixedFactorialMomentLimit μ X rates) :
    LawConverges μ X (productPoissonMeasure rates) (fun z => z) := by
  sorry

variable (E : Type u) [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E]
    [T2Space E] [LocallyCompactSpace E] [SecondCountableTopology E]

/-- Countable generating-window form of Kallenberg A2.3(iv).
It lets a genuine geometric process prove vague-Borel measurability from
actual bounded-window counts, without assuming arbitrary-test measurability. -/
theorem pointMeasure_aemeasurable_of_basis_counts {Ω : Type v}
    [MeasurableSpace Ω] (μ : Measure Ω) (Ξ : Ω → PointMeasure E)
    (ν : Measure E) [IsLocallyFiniteMeasure ν] [Measure.Regular ν]
    (R : Set (RelCompactBorelWindow E)) (hR : ContinuityWindowBasis E ν R)
    (hcounts : ∀ B ∈ R, AEMeasurable (fun ω => (Ξ ω).count E B) μ) :
    AEMeasurable Ξ μ := by
  sorry

/-- Last--Penrose (2017 author manuscript), Theorem 3.6, p.21.
The lcscH/Radon specialization is sigma-finite; countable compact exhaustion
and modification on one null set give a law of genuinely locally finite
point measures. No diffuse-intensity or simplicity hypothesis is imposed. -/
theorem poisson_point_process_exists (ν : Measure E)
    [IsLocallyFiniteMeasure ν] [Measure.Regular ν] :
    ∃ Q : ProbabilityMeasure (PointMeasure E), IsPoissonPointProcessLaw E ν Q := by
  sorry

/-- Kallenberg (2002), Theorem 16.16(iii) => (i), pp.316--317.
All relatively compact Borel continuity windows are quantified. Their target
boundary mass is required almost surely, not guessed from their endpoints. -/
theorem pointMeasure_vague_of_count_vectors {Ω : ℕ → Type v}
    [∀ n, MeasurableSpace (Ω n)] (μ : (n : ℕ) → Measure (Ω n))
    (Ξ : (n : ℕ) → Ω n → PointMeasure E)
    (hprob : ∀ᶠ n in atTop, IsProbabilityMeasure (μ n))
    (hΞ : ∀ᶠ n in atTop, AEMeasurable (Ξ n) (μ n))
    (Q : ProbabilityMeasure (PointMeasure E))
    (hcounts : ∀ d : ℕ, ∀ B : Fin d → RelCompactBorelWindow E,
      (∀ i, ∀ᵐ ξ ∂(Q : Measure (PointMeasure E)),
        ξ.toMeasure (frontier (B i).carrier) = 0) →
      LawConverges μ (fun n ω => windowCountVector E B (Ξ n ω))
        Q (windowCountVector E B)) :
    LawConverges μ Ξ Q (fun ξ => ξ) := by
  sorry

/-- Generic continuity-semiring specialization of the preceding two classical
criteria. First moments yield tightness on compact sets, the semiring gives
finite disjoint simple-function approximations to compact-support tests,
and the full mixed factorial criterion identifies the target PPP counts.
This contains no geometric object, type weight, or planar-tail premise. -/
theorem pointMeasure_vague_of_semiring_mixed_factorials {Ω : ℕ → Type v}
    [∀ n, MeasurableSpace (Ω n)] (μ : (n : ℕ) → Measure (Ω n))
    (Ξ : (n : ℕ) → Ω n → PointMeasure E)
    (hprob : ∀ᶠ n in atTop, IsProbabilityMeasure (μ n))
    (hΞ : ∀ᶠ n in atTop, AEMeasurable (Ξ n) (μ n))
    (ν : Measure E) [IsLocallyFiniteMeasure ν] [Measure.Regular ν]
    (R : Set (RelCompactBorelWindow E)) (hR : ContinuityWindowBasis E ν R)
    (Q : ProbabilityMeasure (PointMeasure E)) (hQ : IsPoissonPointProcessLaw E ν Q)
    (hmom : ∀ d : ℕ, ∀ B : Fin d → RelCompactBorelWindow E,
      (∀ i, B i ∈ R) → DisjointWindows E B →
      MixedFactorialMomentLimit μ
        (fun n ω => windowCountVector E B (Ξ n ω)) (windowRates E ν B)) :
    LawConverges μ Ξ Q (fun ξ => ξ) := by
  sorry

/-- Generic derived continuity-semiring count-law criterion, from Kallenberg
(2002), Lemma 16.15 and Theorem 16.16, pp.316--317, with the separating-class
extension in Chapter 16 Exercise 11, p.327. Finite semiring refinement gives
joint laws on finite unions; local approximation makes these unions separating.
Count-law tightness suffices here; no first-moment convergence is assumed.
This is an independently deferred classical corollary, not a Lean proof or a
verbatim source theorem. Zero rates, empty families, and varying probability
spaces with eventual probability/measurability remain allowed. -/
theorem pointMeasure_vague_of_semiring_count_laws {Ω : ℕ → Type v}
    [∀ j, MeasurableSpace (Ω j)] (μ : (j : ℕ) → Measure (Ω j))
    (Ξ : (j : ℕ) → Ω j → PointMeasure E)
    (hprob : ∀ᶠ j in atTop, IsProbabilityMeasure (μ j))
    (hΞ : ∀ᶠ j in atTop, AEMeasurable (Ξ j) (μ j))
    (ν : Measure E) [IsLocallyFiniteMeasure ν] [Measure.Regular ν]
    (R : Set (RelCompactBorelWindow E)) (hR : ContinuityWindowBasis E ν R)
    (Q : ProbabilityMeasure (PointMeasure E)) (hQ : IsPoissonPointProcessLaw E ν Q)
    (hcounts : ∀ d : ℕ, ∀ B : Fin d → RelCompactBorelWindow E,
      (∀ i, B i ∈ R) → DisjointWindows E B →
      LawConverges μ (fun j ω => windowCountVector E B (Ξ j ω))
        (productPoissonMeasure (windowRates E ν B)) (fun z => z)) :
    LawConverges μ Ξ Q (fun ξ => ξ) := by
  sorry

end WP.External
