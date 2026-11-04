import WPFormalization.Critical.MixedIntersectingDomination

/-! The complete finite catalog of actual short intersecting simple tuples.
Finiteness uses the original complete primitive length catalog. No measurability
statement or geometric domination estimate is assumed or asserted here.
-/
noncomputable section
set_option maxHeartbeats 400000
universe aa bb cc dd
namespace WP.Critical
open WP.External Finset
open scoped Classical ENNReal
variable {P : PsiTheory} {G : WeilPeterssonGeometry.{aa,bb} P}
    {H : HyperbolicCurveGeometry.{aa,bb,cc} G}
    (T : MulticurveTopology.{aa,bb,cc,dd} G H) {g n : ℕ}

/-- Every coordinate lies in the complete original primitive length catalog. -/
def shortIntersectingSimpleTupleToShortCatalog
    (X : G.Moduli g n (fun _ => 0)) (r : ℕ) (L : ℝ) :
    ShortIntersectingSimpleTuple T X r L →
      (Fin r → {γ // γ ∈ H.shortPrimitive X L}) := fun γ i =>
  ⟨γ.val i, (H.mem_shortPrimitive X L _).2 (γ.property.2.2.1 i)⟩

lemma shortIntersectingSimpleTupleToShortCatalog_injective
    (X : G.Moduli g n (fun _ => 0)) (r : ℕ) (L : ℝ) :
    Function.Injective (shortIntersectingSimpleTupleToShortCatalog T X r L) := by
  intro γ δ h
  apply Subtype.ext
  funext i
  exact congrArg Subtype.val (congrFun h i)

instance shortIntersectingSimpleTupleFinite
    (X : G.Moduli g n (fun _ => 0)) (r : ℕ) (L : ℝ) :
    Finite (ShortIntersectingSimpleTuple T X r L) :=
  Finite.of_injective (shortIntersectingSimpleTupleToShortCatalog T X r L)
    (shortIntersectingSimpleTupleToShortCatalog_injective T X r L)

instance shortIntersectingSimpleTupleFintype
    (X : G.Moduli g n (fun _ => 0)) (r : ℕ) (L : ℝ) :
    Fintype (ShortIntersectingSimpleTuple T X r L) := Fintype.ofFinite _

/-- The full actual finite tuple directory, with the original curve values. -/
def shortIntersectingSimpleTupleCatalog
    (X : G.Moduli g n (fun _ => 0)) (r : ℕ) (L : ℝ) :
    Finset (Fin r → H.Primitive g n X) :=
  (univ : Finset (ShortIntersectingSimpleTuple T X r L)).image Subtype.val

@[simp] lemma mem_shortIntersectingSimpleTupleCatalog
    (X : G.Moduli g n (fun _ => 0)) (r : ℕ) (L : ℝ)
    (γ : Fin r → H.Primitive g n X) :
    γ ∈ shortIntersectingSimpleTupleCatalog T X r L ↔
      Function.Injective γ ∧ (∀ i, H.simple (γ i)) ∧
        (∀ i, H.length (γ i) ≤ L) ∧ ¬∀ i j, i ≠ j → T.disjoint (γ i) (γ j) := by
  letI : Fintype {γ : Fin r → H.Primitive g n X //
      Function.Injective γ ∧ (∀ i, H.simple (γ i)) ∧
      (∀ i, H.length (γ i) ≤ L) ∧ ¬∀ i j, i ≠ j → T.disjoint (γ i) (γ j)} :=
    shortIntersectingSimpleTupleFintype T X r L
  constructor
  · intro hγ
    obtain ⟨δ, _, hδ⟩ := Finset.mem_image.1 hγ
    exact hδ ▸ δ.property
  · intro hγ
    have hh : (⟨γ, hγ⟩ : ShortIntersectingSimpleTuple T X r L) ∈
        (univ : Finset (ShortIntersectingSimpleTuple T X r L)) := mem_univ _
    exact Finset.mem_image_of_mem
      (fun δ : ShortIntersectingSimpleTuple T X r L => δ.val) hh

lemma shortIntersectingSimpleTupleCatalog_card
    (X : G.Moduli g n (fun _ => 0)) (r : ℕ) (L : ℝ) :
    (shortIntersectingSimpleTupleCatalog T X r L).card =
      Nat.card (ShortIntersectingSimpleTuple T X r L) := by
  calc
    _ = (univ : Finset (ShortIntersectingSimpleTuple T X r L)).card :=
      Finset.card_image_of_injective _ Subtype.val_injective
    _ = _ := by rw [card_univ, Nat.card_eq_fintype_card]

/-- The existing actual ENNReal count equals the ordinary finite catalog card. -/
lemma allShortIntersectingSimpleTupleCount_eq_card
    (X : G.Moduli g n (fun _ => 0)) (r : ℕ) (L : ℝ) :
    allShortIntersectingSimpleTupleCount T X r L =
      ((shortIntersectingSimpleTupleCatalog T X r L).card : ℝ≥0∞) := by
  rw [allShortIntersectingSimpleTupleCount, tsum_fintype]
  simp only [sum_const, card_univ, nsmul_eq_mul, mul_one]
  rw [shortIntersectingSimpleTupleCatalog_card, Nat.card_eq_fintype_card]

lemma allShortIntersectingSimpleTupleCount_ne_top
    (X : G.Moduli g n (fun _ => 0)) (r : ℕ) (L : ℝ) :
    allShortIntersectingSimpleTupleCount T X r L ≠ ⊤ := by
  rw [allShortIntersectingSimpleTupleCount_eq_card]
  exact ENNReal.natCast_ne_top _

/-- Nonpositive physical length cutoffs admit no intersecting simple tuple. -/
lemma allShortIntersectingSimpleTupleCount_zero_of_nonpos
    (X : G.Moduli g n (fun _ => 0)) (r : ℕ) (L : ℝ) (hL : L ≤ 0) :
    allShortIntersectingSimpleTupleCount T X r L = 0 := by
  by_cases hr : r ≤ 1
  · exact allShortIntersectingSimpleTupleCount_zero_of_le_one T X r hr L
  · apply ENNReal.tsum_eq_zero.mpr
    intro γ
    have hi : 0 < r := by omega
    have hpos := H.length_pos (γ.val ⟨0, hi⟩)
    have hle := γ.property.2.2.1 ⟨0, hi⟩
    exact False.elim ((not_lt_of_ge (hle.trans hL)) hpos)

lemma shortIntersectingSimpleTupleCatalog_eq_empty_of_nonpos
    (X : G.Moduli g n (fun _ => 0)) (r : ℕ) (L : ℝ) (hL : L ≤ 0) :
    shortIntersectingSimpleTupleCatalog T X r L = ∅ := by
  have hc := allShortIntersectingSimpleTupleCount_zero_of_nonpos T X r L hL
  rw [allShortIntersectingSimpleTupleCount_eq_card] at hc
  apply Finset.card_eq_zero.1
  exact_mod_cast hc

end WP.Critical
