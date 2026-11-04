import Mathlib.Probability.Distributions.Poisson.Basic
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.Topology.ContinuousMap.CompactlySupported
import Mathlib.Data.Nat.Factorial.Basic

/-! Genuine locally finite Radon counting measures and their vague topology.
Weak convergence is tested against bounded continuous functions of the actual
measure-valued random variable. No count convergence criterion is a definition.
-/
noncomputable section
universe u v w z
namespace WP.Probability
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology CompactlySupported ENNReal NNReal

/-- The usual bounded-continuous-test form of weak convergence. It is useful
when the input measures are probabilities only eventually. Probability and
measurability hypotheses are supplied explicitly at each theorem that uses it. -/
def LawConverges {E : Type u} [TopologicalSpace E] {Ω : ℕ → Type v}
    [∀ n, MeasurableSpace (Ω n)] {Ωlimit : Type w} [MeasurableSpace Ωlimit]
    (μ : (n : ℕ) → Measure (Ω n)) (X : (n : ℕ) → Ω n → E)
    (μlimit : Measure Ωlimit) (Z : Ωlimit → E) : Prop :=
  ∀ f : BoundedContinuousFunction E ℝ,
    Tendsto (fun n => ∫ ω, f (X n ω) ∂μ n) atTop
      (𝓝 (∫ ω, f (Z ω) ∂μlimit))

theorem lawConverges_iff_tendstoInDistribution {E : Type u} [TopologicalSpace E]
    [MeasurableSpace E] [OpensMeasurableSpace E] {Ω : ℕ → Type v}
    [∀ n, MeasurableSpace (Ω n)] {Ωlimit : Type w} [MeasurableSpace Ωlimit]
    (μ : (n : ℕ) → Measure (Ω n)) [∀ n, IsProbabilityMeasure (μ n)]
    (X : (n : ℕ) → Ω n → E) (μlimit : Measure Ωlimit) [IsProbabilityMeasure μlimit]
    (Z : Ωlimit → E) (hX : ∀ n, AEMeasurable (X n) (μ n))
    (hZ : AEMeasurable Z μlimit) :
    LawConverges μ X μlimit Z ↔ TendstoInDistribution X atTop Z μ μlimit := by
  exact (tendstoInDistribution_iff_forall_integral_rclike_tendsto ℝ hX hZ).symm

def productPoissonMeasure {d : ℕ} (rates : Fin d → ℝ≥0) : Measure (Fin d → ℕ) :=
  Measure.pi (fun i => poissonMeasure (rates i))

instance {d : ℕ} (rates : Fin d → ℝ≥0) :
    IsProbabilityMeasure (productPoissonMeasure rates) :=
  inferInstanceAs (IsProbabilityMeasure (Measure.pi (fun i => poissonMeasure (rates i))))

def productPoissonLaw {d : ℕ} (rates : Fin d → ℝ≥0) : ProbabilityMeasure (Fin d → ℕ) :=
  ⟨productPoissonMeasure rates, inferInstance⟩

/-- All mixed factorial moments, using genuine nonnegative expectations.
No nonintegrable Bochner integral can silently become zero in this hypothesis. -/
def MixedFactorialMomentLimit {d : ℕ} {Ω : ℕ → Type v}
    [∀ n, MeasurableSpace (Ω n)] (μ : (n : ℕ) → Measure (Ω n))
    (X : (n : ℕ) → Ω n → Fin d → ℕ) (rates : Fin d → ℝ≥0) : Prop :=
  ∀ α : Fin d → ℕ,
    Tendsto (fun n => ∫⁻ ω, ∏ i : Fin d,
      (((X n ω i).descFactorial (α i) : ℕ) : ℝ≥0∞) ∂μ n)
      atTop (𝓝 (∏ i : Fin d, (rates i : ℝ≥0∞) ^ (α i)))

variable (E : Type u) [TopologicalSpace E] [MeasurableSpace E]

structure RelCompactBorelWindow where
  carrier : Set E
  measurableSet : MeasurableSet carrier
  compactClosure : IsCompact (closure carrier)

/-- A genuine Radon counting measure. Multiplicities are allowed. -/
structure PointMeasure where
  toMeasure : Measure E
  locallyFinite : IsLocallyFiniteMeasure toMeasure
  regular : Measure.Regular toMeasure
  integerOnRelCompact : ∀ B : Set E, MeasurableSet B → IsCompact (closure B) →
    ∃ n : ℕ, toMeasure B = (n : ℝ≥0∞)

namespace PointMeasure

instance (ξ : PointMeasure E) : IsLocallyFiniteMeasure ξ.toMeasure := ξ.locallyFinite
instance (ξ : PointMeasure E) : Measure.Regular ξ.toMeasure := ξ.regular

def count (ξ : PointMeasure E) (B : RelCompactBorelWindow E) : ℕ :=
  Classical.choose (ξ.integerOnRelCompact B.carrier B.measurableSet B.compactClosure)

theorem count_spec (ξ : PointMeasure E) (B : RelCompactBorelWindow E) :
    ξ.toMeasure B.carrier = (ξ.count E B : ℝ≥0∞) :=
  Classical.choose_spec (ξ.integerOnRelCompact B.carrier B.measurableSet B.compactClosure)

/-- The actual vague topology: initial topology for integrals of all
compactly supported continuous real functions against the underlying measure. -/
instance : TopologicalSpace (PointMeasure E) :=
  TopologicalSpace.induced
    (fun ξ : PointMeasure E => fun f : C_c(E, ℝ) => ∫ x, f x ∂ξ.toMeasure)
    inferInstance

instance : MeasurableSpace (PointMeasure E) := borel (PointMeasure E)
instance : BorelSpace (PointMeasure E) := ⟨rfl⟩

end PointMeasure

def DisjointWindows {d : ℕ} (B : Fin d → RelCompactBorelWindow E) : Prop :=
  Pairwise (fun i j => Disjoint (B i).carrier (B j).carrier)

def windowCountVector {d : ℕ} (B : Fin d → RelCompactBorelWindow E)
    (ξ : PointMeasure E) : Fin d → ℕ :=
  fun i => ξ.count E (B i)

def windowRates {d : ℕ} (ν : Measure E) (B : Fin d → RelCompactBorelWindow E) :
    Fin d → ℝ≥0 := fun i => (ν (B i).carrier).toNNReal

theorem window_measure_lt_top (ν : Measure E) [IsFiniteMeasureOnCompacts ν]
    (B : RelCompactBorelWindow E) : ν B.carrier < ∞ :=
  (measure_mono subset_closure).trans_lt B.compactClosure.measure_lt_top

theorem windowRates_coe {d : ℕ} (ν : Measure E) [IsFiniteMeasureOnCompacts ν]
    (B : Fin d → RelCompactBorelWindow E) (i : Fin d) :
    ((windowRates E ν B i : ℝ≥0) : ℝ≥0∞) = ν (B i).carrier := by
  exact ENNReal.coe_toNNReal (window_measure_lt_top E ν (B i)).ne

/-- The ordinary PPP law is specified by actual disjoint-set counts.
The finite-on-compacts hypothesis prevents any infinite intensity from being
silently converted to a zero `NNReal` rate. No convergence is a field here. -/
def IsPoissonPointProcessLaw (ν : Measure E) [IsFiniteMeasureOnCompacts ν]
    (Q : ProbabilityMeasure (PointMeasure E)) : Prop :=
  ∀ d : ℕ, ∀ B : Fin d → RelCompactBorelWindow E, DisjointWindows E B →
    HasLaw (windowCountVector E B) (productPoissonMeasure (windowRates E ν B)) Q

/-- A relatively compact Borel semiring of intensity-continuity windows with
enough finite unions to approximate the topology locally. -/
structure ContinuityWindowBasis (ν : Measure E)
    (R : Set (RelCompactBorelWindow E)) : Prop where
  countable : R.Countable
  empty_mem : ∃ B ∈ R, B.carrier = ∅
  intersection : ∀ A ∈ R, ∀ B ∈ R,
    ∃ C ∈ R, C.carrier = A.carrier ∩ B.carrier
  difference : ∀ A ∈ R, ∀ B ∈ R,
    ∃ F : Finset (RelCompactBorelWindow E),
      (∀ C ∈ F, C ∈ R) ∧
      (∀ C ∈ F, ∀ D ∈ F, C ≠ D → Disjoint C.carrier D.carrier) ∧
      (⋃ C ∈ F, C.carrier) = A.carrier \ B.carrier
  continuity : ∀ B ∈ R, ν (frontier B.carrier) = 0
  localApproximation : ∀ K U : Set E, IsCompact K → IsOpen U → K ⊆ U →
    ∃ F : Finset (RelCompactBorelWindow E),
      (∀ B ∈ F, B ∈ R) ∧
      K ⊆ interior (⋃ B ∈ F, B.carrier) ∧ (⋃ B ∈ F, B.carrier) ⊆ U


def nnrealPrefixWindow (b : ℝ≥0) : RelCompactBorelWindow ℝ≥0 where
  carrier := Iic b
  measurableSet := measurableSet_Iic
  compactClosure := by
    rw [closure_Iic]
    have he : Iic b = Icc (0:ℝ≥0) b := by ext x; simp
    rw [he]
    exact isCompact_Icc

end WP.Probability
