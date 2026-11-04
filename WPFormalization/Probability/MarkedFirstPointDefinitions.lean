import WPFormalization.Probability.PointMeasureDefinitions
import Mathlib.MeasureTheory.Measure.Prod
noncomputable section
namespace WP.Probability
open Set MeasureTheory Filter
open scoped ENNReal NNReal Topology

abbrev MarkedLengthSpace := ℝ≥0 × ℕ
abbrev MarkedFirstState := ℝ≥0∞ × ℕ

/-- Finite first length and its original discrete mark. -/
def markedFirstEmbed (p:MarkedLengthSpace) : MarkedFirstState := ((p.1:ℝ≥0∞),p.2)

/-- The genuine whole-type prefix is finite. This is stronger than marked
local finiteness, since the mark coordinate is not compact. -/
def MarkedTimePrefixFinite (ξ:PointMeasure MarkedLengthSpace) : Prop :=
  ∀T:ℝ≥0,ξ.toMeasure (Iic T ×ˢ (univ:Set ℕ))<∞

/-- Any minimum-atom tie choice is allowed. Infinite first length represents
an empty process; its irrelevant default mark is unrestricted. -/
def IsFirstMarkedPoint (ξ:PointMeasure MarkedLengthSpace) (p:MarkedFirstState) : Prop :=
  if p.1=∞ then ξ.toMeasure=0 else
    ξ.toMeasure {(p.1.toNNReal,p.2)}≠0 ∧
      ξ.toMeasure (Iio p.1.toNNReal ×ˢ (univ:Set ℕ))=0

/-- The first time is finite and supports exactly one point, counted with
multiplicity over every mark. This excludes limiting ties without imposing
an unjustified no-ties condition on approximating processes. -/
def IsUniqueFirstMarkedPoint (ξ:PointMeasure MarkedLengthSpace) (p:MarkedFirstState) : Prop :=
  p.1≠∞ ∧ IsFirstMarkedPoint ξ p ∧
    ξ.toMeasure ({p.1.toNNReal} ×ˢ (univ:Set ℕ))=1

/-- No escape of actual marks on any bounded length prefix. -/
def MarkedNoEscape {Ω:ℕ→Type*} [∀n,MeasurableSpace (Ω n)]
    (μ:(n:ℕ)→Measure (Ω n)) (Ξ:(n:ℕ)→Ω n→PointMeasure MarkedLengthSpace) : Prop :=
  ∀T:ℝ≥0,∀ε:ℝ,0<ε→∃K:ℕ,∀ᶠn in atTop,
    (μ n) {ω|(Ξ n ω).toMeasure (Iic T ×ˢ {k:ℕ|K≤k})≠0}≤ENNReal.ofReal ε

/-- The ordinary first-arrival measure for a diffuse time intensity and a
finite mark measure. Its probability normalization is a separate theorem. -/
def markedFirstArrivalMeasure (ν:Measure ℝ≥0) (η:Measure ℕ) : Measure MarkedLengthSpace :=
  (ν.withDensity (fun t=>ENNReal.ofReal
    (Real.exp (-((η univ).toReal*(ν (Iic t)).toReal))))).prod η

def markedFirstArrivalStateMeasure (ν:Measure ℝ≥0) (η:Measure ℕ) : Measure MarkedFirstState :=
  (markedFirstArrivalMeasure ν η).map markedFirstEmbed

lemma markedFirstEmbed_continuous : Continuous markedFirstEmbed := by
  exact (ENNReal.continuous_coe.comp continuous_fst).prodMk continuous_snd

lemma markedFirstEmbed_measurable : Measurable markedFirstEmbed :=
  markedFirstEmbed_continuous.measurable

lemma isFirstMarkedPoint_top (ξ:PointMeasure MarkedLengthSpace) (k:ℕ) :
    IsFirstMarkedPoint ξ (∞,k) ↔ ξ.toMeasure=0 := by
  simp only [IsFirstMarkedPoint,ite_true]

lemma isFirstMarkedPoint_embed (ξ:PointMeasure MarkedLengthSpace) (p:MarkedLengthSpace) :
    IsFirstMarkedPoint ξ (markedFirstEmbed p) ↔
      ξ.toMeasure {p}≠0 ∧ ξ.toMeasure (Iio p.1 ×ˢ (univ:Set ℕ))=0 := by
  simp only [IsFirstMarkedPoint,markedFirstEmbed,ENNReal.coe_ne_top,ite_false,
    ENNReal.toNNReal_coe,Prod.mk.eta]
end WP.Probability
