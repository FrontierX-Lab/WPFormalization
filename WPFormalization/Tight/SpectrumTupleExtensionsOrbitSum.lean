import WPFormalization.Tight.SpectrumTupleExtensionsIdentification
import WPFormalization.Critical.CutBoxIntegral
/- Appendix F.4 exact finite tuple count/orbit-sum identifications. The bounded
actual primitive catalog proves finiteness; the stable ordered orbit partition
and uniqueness split the true tuple count into actual orbit sums. The general
filter/window form covers connected, separating and scaled Borel windows.
No moment estimate, integration identity or limit is assumed in these proofs. -/
noncomputable section
universe u v w z
namespace WP.Tight
open External Set MeasureTheory
open scoped ENNReal Classical

lemma ennreal_card_eq_tsum_indicator {α : Type w} (p : α → Prop) [Finite {a // p a}] :
    (Nat.card {a // p a} : ℝ≥0∞) = ∑' a : α, if p a then 1 else 0 := by
  letI := Fintype.ofFinite {a // p a}
  calc
    _ = ∑' _ : {a // p a}, (1 : ℝ≥0∞) := by simp
    _ = _ := by
      convert (tsum_subtype {a | p a} (fun _ : α => (1 : ℝ≥0∞))) using 1
      · rfl
      · apply tsum_congr
        intro a
        by_cases hp : p a <;> simp [hp]

namespace SpectrumTupleExtensions
variable {P : PsiTheory} {G : WeilPeterssonGeometry.{u,v} P}
  {T : TightRegions G} {H : HyperbolicCurveGeometry.{u,v,w} G}
  (Q : TightGeodesicGeometry G T H) (A : TightMulticurveTopology G T H Q)
  {g n : ℕ} (X : TightSurface G g 0 n (fun _ => 0) (fun _ => 0))

lemma cutLengthTest_eq_ite (r : ℕ) (b : ℝ) (Γ : Fin r → Curve Q X) :
    Critical.cutLengthTest r b (fun i => Q.length (Γ i)) =
      if ∀ i, Q.length (Γ i) ≤ b then 1 else 0 := by
  by_cases hb : ∀ i, Q.length (Γ i) ≤ b
  · rw [if_pos hb, Critical.cutLengthTest, Set.indicator_of_mem]
    exact ⟨fun i => (Q.length_pos (Γ i)).le, hb⟩
  · rw [if_neg hb, Critical.cutLengthTest, Set.indicator_of_notMem]
    exact fun h => hb h.2

lemma separating_tuple_indicator_eq_orbit_sum (r : ℕ) (b : ℝ) (hs : Stable g 0)
    (Γ : Fin r → Curve Q X) :
    (if SeparatingTuple Q A X r b Γ then (1 : ℝ≥0∞) else 0) =
      ∑ o ∈ Finset.univ.filter (fun o : A.Orbit g 0 r => 2 ≤ (A.cut o).components),
        if A.orbitMem o X Γ then Critical.cutLengthTest r b (fun i => Q.length (Γ i)) else 0 := by
  classical
  by_cases hgood : Q.GoodTuple Γ
  · obtain ⟨o, ho, huniq⟩ := A.orbit_partition X Γ hs hgood
    have horbit (q : A.Orbit g 0 r) : A.orbitMem q X Γ ↔ q = o :=
      ⟨fun hq => huniq q hq, fun hq => hq ▸ ho⟩
    have hsep : A.Separating Γ ↔ 2 ≤ (A.cut o).components := by
      constructor
      · rintro ⟨q, hq, hc⟩
        rwa [(horbit q).mp hq] at hc
      · exact fun hc => ⟨o, ho, hc⟩
    simp_rw [horbit]
    rw [Finset.sum_ite_eq']
    rw [cutLengthTest_eq_ite Q X r b Γ]
    by_cases hc : 2 ≤ (A.cut o).components <;>
      by_cases hb : ∀ i, Q.length (Γ i) ≤ b <;>
      simp only [SeparatingTuple, hgood, hsep, hc, hb, true_and, false_and,
        and_true, and_false, if_true, if_false, Finset.mem_filter, Finset.mem_univ]
  · have hnone (o : A.Orbit g 0 r) : ¬A.orbitMem o X Γ := fun ho => hgood (A.orbit_good o ho)
    simp only [SeparatingTuple, hgood, false_and, if_false]
    simp only [hnone, if_false, Finset.sum_const_zero]

/- Exact pointwise actual separating count, with the same physical-length box
and actual orbit sum used by the classical tight integration formula. -/
theorem separating_count_eq_orbit_sum (r : ℕ) (b : ℝ) (hs : Stable g 0) :
    (Nat.card {Γ : Fin r → Curve Q X // SeparatingTuple Q A X r b Γ} : ℝ≥0∞) =
      ∑ o ∈ Finset.univ.filter (fun o : A.Orbit g 0 r => 2 ≤ (A.cut o).components),
        A.orbitSum o (Critical.cutLengthTest r b) X := by
  classical
  letI := finite_separating_tuples Q A X r b
  rw [ennreal_card_eq_tsum_indicator]
  unfold TightMulticurveTopology.orbitSum
  rw [←Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  apply tsum_congr
  intro Γ
  exact separating_tuple_indicator_eq_orbit_sum Q A X r b hs Γ



def FilteredOrbitWindowTuple {r : ℕ} (C : A.Orbit g 0 r → Prop)
    (W : Set (Fin r → ℝ)) (Γ : Fin r → Curve Q X) : Prop :=
  Q.GoodTuple Γ ∧ (∃ o : A.Orbit g 0 r, A.orbitMem o X Γ ∧ C o) ∧
    (fun i => Q.length (Γ i)) ∈ W

lemma finite_filtered_orbit_window_tuples {r : ℕ} (C : A.Orbit g 0 r → Prop)
    (W : Set (Fin r → ℝ)) (b : ℝ) (hW : ∀ x ∈ W, ∀ i, x i ≤ b) :
    Finite {Γ : Fin r → Curve Q X // FilteredOrbitWindowTuple Q A X C W Γ} := by
  letI := finite_primitive_bounded_tuples Q X r b
  apply Finite.of_injective (fun Γ : {Γ : Fin r → Curve Q X //
      FilteredOrbitWindowTuple Q A X C W Γ} =>
    (⟨Γ.val, fun i => ⟨(Γ.property.1.2.1 i).1,
      hW _ Γ.property.2.2 i⟩⟩ : {Γ : Fin r → Curve Q X //
      ∀ i, Q.primitive (Γ i) ∧ Q.length (Γ i) ≤ b}))
  intro Γ Ξ heq
  exact Subtype.ext (Subtype.mk.inj heq)

lemma filtered_window_indicator_eq_orbit_sum {r : ℕ} (C : A.Orbit g 0 r → Prop)
    (W : Set (Fin r → ℝ)) (hs : Stable g 0) (Γ : Fin r → Curve Q X) :
    (if FilteredOrbitWindowTuple Q A X C W Γ then (1:ℝ≥0∞) else 0) =
      ∑ o ∈ Finset.univ.filter C,
        if A.orbitMem o X Γ then W.indicator (fun _ => (1:ℝ≥0∞)) (fun i => Q.length (Γ i)) else 0 := by
  classical
  by_cases hgood : Q.GoodTuple Γ
  · obtain ⟨o, ho, huniq⟩ := A.orbit_partition X Γ hs hgood
    have horbit (q : A.Orbit g 0 r) : A.orbitMem q X Γ ↔ q = o :=
      ⟨fun hq => huniq q hq, fun hq => hq ▸ ho⟩
    have hC : (∃ q : A.Orbit g 0 r, A.orbitMem q X Γ ∧ C q) ↔ C o := by
      simp only [horbit, exists_eq_left]
    simp_rw [horbit]
    rw [Finset.sum_ite_eq']
    by_cases hc : C o <;> by_cases hW : (fun i => Q.length (Γ i)) ∈ W <;>
      simp only [FilteredOrbitWindowTuple, hgood, hC, hc, hW, true_and, false_and,
        if_true, if_false, Finset.mem_filter, Finset.mem_univ, Set.indicator_apply]
  · have hnone (o : A.Orbit g 0 r) : ¬A.orbitMem o X Γ := fun ho => hgood (A.orbit_good o ho)
    simp only [FilteredOrbitWindowTuple, hgood, false_and, if_false]
    simp only [hnone, if_false, Finset.sum_const_zero]

theorem filtered_window_count_eq_orbit_sum {r : ℕ} (C : A.Orbit g 0 r → Prop)
    (W : Set (Fin r → ℝ)) (b : ℝ) (hW : ∀ x ∈ W, ∀ i, x i ≤ b) (hs : Stable g 0) :
    (Nat.card {Γ : Fin r → Curve Q X // FilteredOrbitWindowTuple Q A X C W Γ} : ℝ≥0∞) =
      ∑ o ∈ Finset.univ.filter C, A.orbitSum o (W.indicator (fun _ => 1)) X := by
  classical
  letI := finite_filtered_orbit_window_tuples Q A X C W b hW
  rw [ennreal_card_eq_tsum_indicator]
  unfold TightMulticurveTopology.orbitSum
  rw [←Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  apply tsum_congr
  intro Γ
  exact filtered_window_indicator_eq_orbit_sum Q A X C W hs Γ

def ConnectedWindowTuple {r : ℕ} (lo hi : Fin r → ℝ) (Γ : Fin r → Curve Q X) : Prop :=
  WindowTuple Q X lo hi Γ ∧
    ∃ o : A.Orbit g 0 r, A.orbitMem o X Γ ∧ (A.cut o).components = 1

theorem connected_window_count_eq_orbit_sum {r : ℕ} (lo hi : Fin r → ℝ)
    (b : ℝ) (hhi : ∀ i, hi i ≤ b) (hs : Stable g 0) :
    (Nat.card {Γ : Fin r → Curve Q X // ConnectedWindowTuple Q A X lo hi Γ} : ℝ≥0∞) =
      ∑ o ∈ Finset.univ.filter (fun o : A.Orbit g 0 r => (A.cut o).components = 1),
        A.orbitSum o ((Icc lo hi).indicator (fun _ => 1)) X := by
  classical
  have hpred : ConnectedWindowTuple Q A X lo hi =
      FilteredOrbitWindowTuple Q A X (fun o : A.Orbit g 0 r => (A.cut o).components = 1) (Icc lo hi) := by
    funext Γ
    apply propext
    simp only [ConnectedWindowTuple, WindowTuple, FilteredOrbitWindowTuple,
      Set.mem_Icc, Pi.le_def, forall_and]
    tauto
  rw [hpred]
  convert filtered_window_count_eq_orbit_sum Q A X
    (fun o : A.Orbit g 0 r => (A.cut o).components = 1) (Icc lo hi) b
    (fun x hx i => (hx.2 i).trans (hhi i)) hs using 1 <;> try rfl
  apply Finset.sum_congr
  · ext o
    simp
  · intro o ho
    unfold TightMulticurveTopology.orbitSum
    apply tsum_congr
    intro Γ
    by_cases hmem : A.orbitMem o X Γ
    · simp only [hmem, if_true]
    · simp only [hmem, if_false]

end SpectrumTupleExtensions
end WP.Tight
