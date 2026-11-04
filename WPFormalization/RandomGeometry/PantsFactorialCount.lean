import WPFormalization.RandomGeometry.PantsCounts
import Mathlib.Data.Fintype.CardEmbedding

noncomputable section
universe u v w
namespace WP.External.HyperbolicCurveGeometry
open MeasureTheory
open scoped ENNReal Classical
variable {P : PsiTheory} {G : WP.External.WeilPeterssonGeometry.{u,v} P}
    (H : WP.External.HyperbolicCurveGeometry.{u,v,w} G) {g n : ℕ}

/-- Ordered distinct short curves with a prescribed number of planar cusp
labels. Edge order is retained, so no factorial divisor occurs. -/
def OrderedPlanarTuple (X : G.Moduli g n (fun _ => 0)) (k : ℕ) (L : ℝ) (r : ℕ) :=
  {γ : Fin r → H.Primitive g n X //
    Function.Injective γ ∧ ∀ i, γ i ∈ H.shortPlanar X k L}

/-- The original finite geometric catalog parametrizes these ordered tuples. -/
def orderedPlanarTupleEquivEmbedding (X : G.Moduli g n (fun _ => 0))
    (k : ℕ) (L : ℝ) (r : ℕ) :
    H.OrderedPlanarTuple X k L r ≃ (Fin r ↪ {γ // γ ∈ H.shortPlanar X k L}) where
  toFun t :=
    { toFun := fun i => ⟨t.val i,t.property.2 i⟩
      inj' := fun _ _ h => t.property.1 (congrArg Subtype.val h) }
  invFun t := ⟨fun i => (t i).val,
    (fun _ _ h => t.injective (Subtype.ext h)), fun i => (t i).property⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance orderedPlanarTupleFintype (X : G.Moduli g n (fun _ => 0))
    (k : ℕ) (L : ℝ) (r : ℕ) : Fintype (H.OrderedPlanarTuple X k L r) :=
  Fintype.ofEquiv (Fin r ↪ {γ // γ ∈ H.shortPlanar X k L})
    (H.orderedPlanarTupleEquivEmbedding X k L r).symm

theorem orderedPlanarTuple_card (X : G.Moduli g n (fun _ => 0))
    (k : ℕ) (L : ℝ) (r : ℕ) :
    Nat.card (H.OrderedPlanarTuple X k L r) = (H.planarCount X k L).descFactorial r := by
  classical
  rw [Nat.card_congr (H.orderedPlanarTupleEquivEmbedding X k L r),
    Nat.card_eq_fintype_card, Fintype.card_embedding_eq, Fintype.card_fin,
    Fintype.card_coe, ← H.planarCount_eq_card]

/-- Exact finite falling-factorial count for the actual pants catalog. -/
theorem orderedPantsTuple_card (X : G.Moduli g n (fun _ => 0)) (L : ℝ) (r : ℕ) :
    Nat.card (H.OrderedPlanarTuple X 2 L r) = (H.pantsCount X L).descFactorial r :=
  H.orderedPlanarTuple_card X 2 L r

/-- The finite tuple count as an ENNReal sum, for orbit partitions. -/
theorem orderedPantsTuple_tsum_one (X : G.Moduli g n (fun _ => 0))
    (L : ℝ) (r : ℕ) :
    (∑' _ : H.OrderedPlanarTuple X 2 L r, (1 : ℝ≥0∞)) =
      ((H.pantsCount X L).descFactorial r : ℝ≥0∞) := by
  rw [tsum_fintype]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  rw [← Nat.card_eq_fintype_card, H.orderedPantsTuple_card]

/-- An arbitrary ambient curve universe contributes only the finitely many
catalog tuples; the ENNReal sum therefore equals the actual finite count. -/
theorem orderedPantsTuple_tsum_indicator (X : G.Moduli g n (fun _ => 0))
    (L : ℝ) (r : ℕ) :
    (∑' γ : Fin r → H.Primitive g n X,
      if Function.Injective γ ∧ (∀ i, γ i ∈ H.shortPlanar X 2 L)
      then (1 : ℝ≥0∞) else 0) = ((H.pantsCount X L).descFactorial r : ℝ≥0∞) := by
  classical
  have hsub := tsum_subtype
    {γ : Fin r → H.Primitive g n X |
      Function.Injective γ ∧ ∀ i, γ i ∈ H.shortPlanar X 2 L}
    (fun _ => (1 : ℝ≥0∞))
  have hc : (∑' _ : H.OrderedPlanarTuple X 2 L r, (1 : ℝ≥0∞)) =
      (Nat.card (H.OrderedPlanarTuple X 2 L r) : ℝ≥0∞) := by
    rw [tsum_fintype]
    simp [Nat.card_eq_fintype_card]
  have he : {γ : Fin r → H.Primitive g n X |
      Function.Injective γ ∧ ∀ i, γ i ∈ H.shortPlanar X 2 L} ≃
      H.OrderedPlanarTuple X 2 L r := Equiv.refl _
  have ht := he.tsum_eq (fun _ => (1 : ℝ≥0∞))
  rw [← H.orderedPantsTuple_card X L r, ← hc]
  calc
    _ = ∑' _ : {γ : Fin r → H.Primitive g n X |
        Function.Injective γ ∧ ∀ i, γ i ∈ H.shortPlanar X 2 L}, (1 : ℝ≥0∞) := by
      simpa only [Set.indicator, Set.mem_ofPred_eq] using hsub.symm
    _ = _ := ht

theorem orderedPantsTuple_first_real (X : G.Moduli g n (fun _ => 0)) (L : ℝ) :
    (Nat.card (H.OrderedPlanarTuple X 2 L 1) : ℝ) = (H.pantsCount X L : ℝ) := by
  rw [H.orderedPantsTuple_card, Nat.descFactorial_one]

theorem orderedPantsTuple_second_real (X : G.Moduli g n (fun _ => 0)) (L : ℝ) :
    (Nat.card (H.OrderedPlanarTuple X 2 L 2) : ℝ) =
      (H.pantsCount X L : ℝ) * ((H.pantsCount X L : ℝ)-1) := by
  rw [H.orderedPantsTuple_card]
  generalize H.pantsCount X L = N
  cases N with
  | zero => norm_num
  | succ N => simp [Nat.descFactorial_succ]; ring

end WP.External.HyperbolicCurveGeometry
