import WPFormalization.External.PantsFamily
import WPFormalization.RandomGeometry.CurveLengthPointMeasures

/-! The entire primitive unoriented spectrum of the actual two-cusp pants.
The atoms are the periods of primitive axes in the actual quotient, counted
once per primitive conjugacy/inverse class, including its one boundary.
Local finiteness and integer/Radon properties are proved, not fields. -/
noncomputable section
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
universe u v
namespace WP.Critical.PantsCluster
open WP.External.PantsCluster WP.External.HyperbolicPacking
open MeasureTheory Set Filter
open scoped Topology ENNReal NNReal CompactlySupported

variable (F : Family.{u,v})

def measure (s : Waist) : Measure ℝ≥0 :=
  Measure.sum (fun γ : F.Primitive => Measure.dirac (Real.toNNReal (F.length s γ)))

lemma measure_eq_intrinsic (s : Waist) :
    measure F s = Measure.sum (fun γ : (F.model s).curves.Primitive =>
      Measure.dirac (Real.toNNReal ((F.model s).curves.length γ))) := by
  let μ : (F.model s).curves.Primitive → Measure ℝ≥0 :=
    fun γ => Measure.dirac (Real.toNNReal ((F.model s).curves.length γ))
  change Measure.sum (μ ∘ F.marking s) = Measure.sum μ
  exact Measure.sum_comp_equiv (F.marking s) μ

lemma finite_below (s : Waist) (B : ℝ≥0) :
    Finite {γ : F.Primitive // Real.toNNReal (F.length s γ) ≤ B} := by
  let e : {γ : F.Primitive // Real.toNNReal (F.length s γ) ≤ B} →
      {γ : F.Primitive // γ ∈ F.short s (B : ℝ)} := fun γ =>
    ⟨γ.val, (F.mem_short s _ _).mpr (Real.toNNReal_le_iff_le_coe.mp γ.property)⟩
  exact Finite.of_injective e (by
    intro a b h
    apply Subtype.ext
    have he := congrArg Subtype.val h
    exact he)

lemma measure_Iic (s : Waist) (B : ℝ≥0) :
    measure F s (Iic B) =
      (Nat.card {γ : F.Primitive // F.length s γ ≤ (B : ℝ)} : ℝ≥0∞) := by
  letI : Finite {γ : F.Primitive // Real.toNNReal (F.length s γ) ∈ Iic B} :=
    finite_below F s B
  rw [measure, WP.RandomGeometry.sum_dirac_apply_eq_natCard _ _ measurableSet_Iic]
  congr 1
  exact Nat.card_congr (Equiv.subtypeEquivRight (fun _ => Real.toNNReal_le_iff_le_coe))

instance measure_isLocallyFinite (s : Waist) : IsLocallyFiniteMeasure (measure F s) := by
  constructor
  intro x
  refine ⟨Iic (x+1), Iic_mem_nhds (by simp), ?_⟩
  rw [measure_Iic]
  exact ENNReal.natCast_lt_top _

lemma finite_window (s : Waist) (B : Set ℝ≥0) (hB : BddAbove B) :
    Finite {γ : F.Primitive // Real.toNNReal (F.length s γ) ∈ B} := by
  rcases hB with ⟨U,hU⟩
  letI := finite_below F s U
  let e : {γ : F.Primitive // Real.toNNReal (F.length s γ) ∈ B} →
      {γ : F.Primitive // Real.toNNReal (F.length s γ) ≤ U} :=
    fun γ => ⟨γ.val,hU γ.property⟩
  exact Finite.of_injective e (by
    intro a b h
    apply Subtype.ext
    have he := congrArg Subtype.val h
    exact he)

def pointMeasure (s : Waist) : WP.Probability.PointMeasure ℝ≥0 where
  toMeasure := measure F s
  locallyFinite := measure_isLocallyFinite F s
  regular := by infer_instance
  integerOnRelCompact := by
    intro B hB hcompact
    letI := finite_window F s B (hcompact.bddAbove.mono subset_closure)
    exact ⟨_,WP.RandomGeometry.sum_dirac_apply_eq_natCard _ B hB⟩

lemma integral_eq_tsum (s : Waist) (f : C_c(ℝ≥0,ℝ)) :
    (∫ x, f x ∂measure F s) = ∑' γ : F.Primitive, f (Real.toNNReal (F.length s γ)) := by
  have hi : Integrable f (measure F s) := f.integrable
  rw [measure, integral_sum_measure hi]
  simp only [integral_dirac]

lemma measure_waist_le (s : Waist) :
    Measure.dirac (Real.toNNReal s.val) ≤ measure F s := by
  simpa only [F.length_waist, measure] using
    Measure.le_sum (fun γ : F.Primitive => Measure.dirac (Real.toNNReal (F.length s γ))) F.waistClass

end WP.Critical.PantsCluster
