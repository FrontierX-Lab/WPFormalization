import WPFormalization.External.HyperbolicSurfacePacking
import Mathlib
/-! Actual finite measure packing and maximal separated nets.
No net-cardinality or based-loop count assumption is used. -/
noncomputable section
set_option maxHeartbeats 0
namespace WP.Critical.PrimitivePacking
open Set MeasureTheory Finset
open scoped Classical ENNReal

/-- Finite area packing, with the actual sets and measure retained. -/
lemma finite_packing_card_mul_le {X ι : Type*} [MeasurableSpace X]
    (μ : Measure X) (s : Finset ι) (pieces : ι → Set X) (region : Set X)
    (hfinite : μ region ≠ ⊤) (hm : ∀ i ∈ s, MeasurableSet (pieces i))
    (hd : Set.PairwiseDisjoint (s : Set ι) pieces)
    (hsub : ∀ i ∈ s, pieces i ⊆ region)
    (a : ℝ) (ha : 0 ≤ a) (harea : ∀ i ∈ s, ENNReal.ofReal a ≤ μ (pieces i)) :
    (s.card:ℝ)*a ≤ (μ region).toReal := by
  have hc : (s.card:ℝ≥0∞)*ENNReal.ofReal a ≤ μ region := by
    calc
      _ = ∑ i ∈ s, ENNReal.ofReal a := by simp
      _ ≤ ∑ i ∈ s, μ (pieces i) := sum_le_sum harea
      _ = μ (⋃ i ∈ s, pieces i) := (measure_biUnion_finset hd hm).symm
      _ ≤ μ region := measure_mono (by intro x hx;obtain ⟨i,hi,hx⟩:=mem_iUnion₂.mp hx;exact hsub i hi hx)
  have hr := ENNReal.toReal_mono hfinite hc
  simpa only [ENNReal.toReal_mul,ENNReal.toReal_natCast,ENNReal.toReal_ofReal ha] using hr

lemma separated_balls_disjoint {X : Type*} [PseudoMetricSpace X]
    (s : Finset X) (r : ℝ)
    (hsep : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → 2*r ≤ dist x y) :
    Set.PairwiseDisjoint (s : Set X) (fun x => Metric.ball x r) := by
  intro x hx y hy hxy
  apply Set.disjoint_left.mpr
  intro z hz hz'
  have hh := dist_triangle x z y
  have h1 := Metric.mem_ball.mp hz
  have h2 := Metric.mem_ball.mp hz'
  rw [dist_comm z x] at h1
  linarith [hsep x hx y hy hxy]

/-- A cardinal bound on all finite separated subsets yields an actual finite
cover, by choosing a maximal-cardinality separated subset. -/
lemma finite_net_of_separated_card_bound {X : Type*} [PseudoMetricSpace X]
    (thick : Set X) (r : ℝ) (hr : 0 < r) (M : ℕ)
    (hbound : ∀ s : Finset X, (∀ x ∈ s, x ∈ thick) →
      (∀ x ∈ s, ∀ y ∈ s, x ≠ y → r ≤ dist x y) → s.card ≤ M) :
    ∃ s : Finset X, (∀ x ∈ s, x ∈ thick) ∧
      (∀ x ∈ s, ∀ y ∈ s, x ≠ y → r ≤ dist x y) ∧ s.card ≤ M ∧
      ∀ x ∈ thick, ∃ y ∈ s, dist x y < r := by
  let admissible : Finset X → Prop := fun s => (∀ x ∈ s, x ∈ thick) ∧
    (∀ x ∈ s, ∀ y ∈ s, x ≠ y → r ≤ dist x y)
  have hzero : ∃ s : Finset X, admissible s ∧ s.card=0 := ⟨∅,by simp [admissible]⟩
  have hex : ∃ m ∈ Finset.range (M+1), ∃ s : Finset X, admissible s ∧ s.card=m :=
    ⟨0,by simp,hzero⟩
  let counts := (Finset.range (M+1)).filter (fun m => ∃ s : Finset X, admissible s ∧ s.card=m)
  have hc : counts.Nonempty := by
    obtain ⟨m,hm,hs⟩:=hex
    exact ⟨m,mem_filter.mpr ⟨hm,hs⟩⟩
  obtain ⟨m,hm,hmax⟩ := Finset.exists_max_image counts id hc
  obtain ⟨s,hs,hsm⟩ := (mem_filter.mp hm).2
  refine ⟨s,hs.1,hs.2,hbound s hs.1 hs.2,?_⟩
  intro x hx
  by_contra hn
  have hfar : ∀ y ∈ s, r ≤ dist x y := by simpa only [not_exists,not_and,not_lt] using hn
  have hxs : x ∉ s := by
    intro hi
    have hh := hfar x hi
    simp only [dist_self] at hh
    linarith
  have hi : admissible (insert x s) := by
    refine ⟨?_,?_⟩
    · intro y hy
      rcases mem_insert.mp hy with rfl|hy
      · exact hx
      · exact hs.1 y hy
    · intro y hy z hz hyz
      by_cases hyx : y=x
      · have hzs : z ∈ s := (mem_insert.mp hz).resolve_left (fun hzx => hyz (hyx.trans hzx.symm))
        simpa only [hyx] using hfar z hzs
      · have hys : y ∈ s := (mem_insert.mp hy).resolve_left hyx
        by_cases hzx : z=x
        · simpa only [hzx,dist_comm] using hfar y hys
        · exact hs.2 y hys z ((mem_insert.mp hz).resolve_left hzx) hyz
  have hibound := hbound (insert x s) hi.1 hi.2
  have himem : (insert x s).card ∈ counts :=
    mem_filter.mpr ⟨mem_range.mpr (by omega),⟨insert x s,hi,rfl⟩⟩
  have hle := hmax _ himem
  simp only [id_eq,card_insert_of_notMem hxs] at hle
  omega
end WP.Critical.PrimitivePacking
