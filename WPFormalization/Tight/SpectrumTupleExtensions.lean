import WPFormalization.External.BuddLionsTightGeometry
import Mathlib.SetTheory.Cardinal.Finite

/- Local Appendix F.4 proof: actual finite tuple families, exact retained-prefix
injections and the marked bad-event count inequality. Geometry is supplied only
by the separately approved classical BuddLionsTightGeometry interface; the
count inequalities and actual-H event identifications are proved here.
No asymptotic, moment estimate or probability conclusion is assumed. -/

noncomputable section
universe u v w z
namespace WP.Tight
open Set
open scoped Classical

/- A finite family of extensions retaining every marked coordinate gives a
cardinality bound. The indexing set records each possible extra length. -/
theorem card_le_sum_of_prefix_extensions {α : Type w} {ι : Type z}
    [Fintype ι] (r : ℕ) (m : ι → ℕ) (P : (Fin r → α) → Prop)
    (R : ∀ i : ι, (Fin (r + m i) → α) → Prop)
    [∀ i : ι, Finite {Δ // R i Δ}]
    (hext : ∀ Γ, P Γ → ∃ i, ∃ Δ : Fin (r + m i) → α, R i Δ ∧
      ∀ j : Fin r, Δ (Fin.castAdd (m i) j) = Γ j) :
    Nat.card {Γ // P Γ} ≤ ∑ i : ι, Nat.card {Δ // R i Δ} := by
  classical
  have hex : ∀ Γ : {Γ // P Γ}, ∃ out : Σ i : ι, {Δ // R i Δ},
      ∀ j : Fin r, out.2.val (Fin.castAdd (m out.1) j) = Γ.val j := by
    intro Γ
    obtain ⟨i, Δ, hΔ, hp⟩ := hext Γ.val Γ.property
    exact ⟨⟨i, ⟨Δ, hΔ⟩⟩, hp⟩
  choose f hf using hex
  have hinj : Function.Injective f := by
    intro Γ Ξ heq
    apply Subtype.ext
    funext j
    have hv := congrArg (fun out : Σ i : ι, {Δ // R i Δ} =>
      out.2.val (Fin.castAdd (m out.1) j)) heq
    exact (hf Γ j).symm.trans (hv.trans (hf Ξ j))
  exact (Nat.card_le_card_of_injective f hinj).trans_eq Nat.card_sigma

namespace SpectrumTupleExtensions
open External
variable {P : PsiTheory} {G : WeilPeterssonGeometry.{u,v} P}
  {T : TightRegions G} {H : HyperbolicCurveGeometry.{u,v,w} G}
  (Q : TightGeodesicGeometry G T H) (A : TightMulticurveTopology G T H Q)
  {g n : ℕ} (X : TightSurface G g 0 n (fun _ => 0) (fun _ => 0))

abbrev Curve := Q.Geodesic g 0 n (fun _ => 0) (fun _ => 0) X

def WindowTuple {r : ℕ} (lo hi : Fin r → ℝ) (Γ : Fin r → Curve Q X) : Prop :=
  Q.GoodTuple Γ ∧ ∀ i, lo i ≤ Q.length (Γ i) ∧ Q.length (Γ i) ≤ hi i

def SeparatingTuple (r : ℕ) (b : ℝ) (Γ : Fin r → Curve Q X) : Prop :=
  Q.GoodTuple Γ ∧ A.Separating Γ ∧ ∀ i, Q.length (Γ i) ≤ b

def ShortAugmentedTuple {r : ℕ} (lo hi : Fin r → ℝ) (b : ℝ)
    (Δ : Fin (r+1) → Curve Q X) : Prop :=
  Q.GoodTuple Δ ∧
  (∀ i : Fin r, lo i ≤ Q.length (Δ (Fin.castAdd 1 i)) ∧
    Q.length (Δ (Fin.castAdd 1 i)) ≤ hi i) ∧
  Q.length (Δ (Fin.last r)) ≤ b

lemma finite_primitive_bounded_tuples (r : ℕ) (b : ℝ) :
    Finite {Γ : Fin r → Curve Q X //
      ∀ i, Q.primitive (Γ i) ∧ Q.length (Γ i) ≤ b} := by
  classical
  let f : {Γ : Fin r → Curve Q X //
      ∀ i, Q.primitive (Γ i) ∧ Q.length (Γ i) ≤ b} →
      (Fin r → ↥(Q.shortPrimitive X b)) := fun Γ i =>
    ⟨⟨Γ.val i, (Γ.property i).1⟩,
      (Q.mem_shortPrimitive X b _).mpr (Γ.property i).2⟩
  apply Finite.of_injective f
  intro Γ Ξ heq
  apply Subtype.ext
  funext i
  exact congrArg (fun e => e.val.val) (congrFun heq i)

lemma finite_separating_tuples (r : ℕ) (b : ℝ) :
    Finite {Γ : Fin r → Curve Q X // SeparatingTuple Q A X r b Γ} := by
  let := finite_primitive_bounded_tuples Q X r b
  apply Finite.of_injective (fun Γ : {Γ : Fin r → Curve Q X // SeparatingTuple Q A X r b Γ} =>
    (⟨Γ.val, fun i => ⟨(Γ.property.1.2.1 i).1, Γ.property.2.2 i⟩⟩ :
      {Γ : Fin r → Curve Q X // ∀ i, Q.primitive (Γ i) ∧ Q.length (Γ i) ≤ b}))
  intro Γ Ξ heq
  exact Subtype.ext (Subtype.mk.inj heq)

lemma finite_window_tuples {r : ℕ} (lo hi : Fin r → ℝ) (b : ℝ)
    (hb : ∀ i, hi i ≤ b) :
    Finite {Γ : Fin r → Curve Q X // WindowTuple Q X lo hi Γ} := by
  let := finite_primitive_bounded_tuples Q X r b
  apply Finite.of_injective (fun Γ : {Γ : Fin r → Curve Q X // WindowTuple Q X lo hi Γ} =>
    (⟨Γ.val, fun i => ⟨(Γ.property.1.2.1 i).1, (Γ.property.2 i).2.trans (hb i)⟩⟩ :
      {Γ : Fin r → Curve Q X // ∀ i, Q.primitive (Γ i) ∧ Q.length (Γ i) ≤ b}))
  intro Γ Ξ heq
  exact Subtype.ext (Subtype.mk.inj heq)


def HasShortSimple (b : ℝ) : Prop :=
  ∃ γ : Curve Q X, Q.primitive γ ∧ Q.IsTight γ ∧ Q.simple γ ∧ Q.length γ ≤ b

def HasShortTight (b : ℝ) : Prop :=
  ∃ γ : Curve Q X, Q.primitive γ ∧ Q.IsTight γ ∧ Q.length γ ≤ b

def BadConfiguration (b : ℝ) : Prop :=
  (∃ γ : Curve Q X, Q.primitive γ ∧ Q.IsTight γ ∧ Q.length γ ≤ b ∧ ¬Q.simple γ) ∨
  ∃ γ δ : Curve Q X, γ ≠ δ ∧ Q.primitive γ ∧ Q.primitive δ ∧
    Q.IsTight γ ∧ Q.IsTight δ ∧ Q.length γ ≤ b ∧ Q.length δ ≤ b ∧ ¬Q.disjoint γ δ

lemma short_tight_iff_simple (D : BuddLionsTightGeometry G T H Q A)
    (hg : 2 ≤ g) (hgeneric : Q.NoSimpleLengthTies (X:=X)) (b : ℝ) :
    HasShortTight Q X b ↔ HasShortSimple Q X b := by
  constructor
  · exact D.short_tight_has_simple g n hg X b hgeneric
  · rintro ⟨γ, hp, ht, hs, hl⟩
    exact ⟨γ, hp, ht, hl⟩

lemma finite_short_augmented_tuples {r : ℕ} (lo hi : Fin r → ℝ) (b c : ℝ)
    (hc : ∀ i, hi i ≤ c) :
    Finite {Δ : Fin (r+1) → Curve Q X // ShortAugmentedTuple Q X lo hi b Δ} := by
  classical
  let := finite_primitive_bounded_tuples Q X (r+1) (max b c)
  have hbound : ∀ Δ, ShortAugmentedTuple Q X lo hi b Δ →
      ∀ i, Q.primitive (Δ i) ∧ Q.length (Δ i) ≤ max b c := by
    intro Δ hΔ i
    refine ⟨(hΔ.1.2.1 i).1, ?_⟩
    refine Fin.lastCases ?_ (fun j => ?_) i
    · exact hΔ.2.2.trans (le_max_left _ _)
    · change Q.length (Δ (Fin.castAdd 1 j)) ≤ max b c
      exact ((hΔ.2.1 j).2.trans (hc j)).trans (le_max_right _ _)
  apply Finite.of_injective (fun Δ : {Δ : Fin (r+1) → Curve Q X //
      ShortAugmentedTuple Q X lo hi b Δ} =>
    (⟨Δ.val, hbound Δ.val Δ.property⟩ : {Δ : Fin (r+1) → Curve Q X //
      ∀ i, Q.primitive (Δ i) ∧ Q.length (Δ i) ≤ max b c}))
  intro Δ Ξ heq
  exact Subtype.ext (Subtype.mk.inj heq)

/- The deterministic no-short part of BL (61), with the actual finite primitive
catalog establishing finiteness of every output tuple family. -/
theorem window_count_le_separating_of_no_short
    (D : BuddLionsTightGeometry G T H Q A)
    {r : ℕ} (lo hi : Fin r → ℝ) (s ε B : ℝ)
    (hs : 0 < s) (he : 0 < ε) (hB : 0 < B)
    (hgenus : 2*B*((r:ℝ)+2)/ε+2 < g)
    (hgeneric : Q.NoSimpleLengthTies (X:=X))
    (hhi : ∀ i, hi i ≤ s*B)
    (hnoshort : ¬HasShortSimple Q X (s*ε))
    (hbad : BadConfiguration Q X (s*B)) :
    Nat.card {Γ : Fin r → Curve Q X // WindowTuple Q X lo hi Γ} ≤
      ∑ m : Fin (⌈2*B*((r:ℝ)+2)/ε⌉₊+1),
        Nat.card {Δ : Fin (r+m.val) → Curve Q X //
          SeparatingTuple Q A X (r+m.val) (s*B*((r:ℝ)+2)) Δ} := by
  classical
  let M := ⌈2*B*((r:ℝ)+2)/ε⌉₊
  let (m : Fin (M+1)) := finite_separating_tuples Q A X
    (r+m.val) (s*B*((r:ℝ)+2))
  apply card_le_sum_of_prefix_extensions r (fun m : Fin (M+1) => m.val)
    (WindowTuple Q X lo hi)
    (fun m => SeparatingTuple Q A X (r+m.val) (s*B*((r:ℝ)+2)))
  intro Γ hΓ
  have hnone : ∀ γ : Curve Q X,
      Q.primitive γ → Q.IsTight γ → Q.simple γ → s*ε < Q.length γ := by
    intro γ hp ht hsimple
    by_contra hn
    exact hnoshort ⟨γ, hp, ht, hsimple, le_of_not_gt hn⟩
  obtain ⟨m, hm, Δ, hΔgood, hΔsep, hprefix, hΔbound⟩ :=
    D.extend_no_short g n r X s ε B hs he hB hgenus hgeneric Γ hΓ.1
      (fun i => (hΓ.2 i).2.trans (hhi i)) hnone hbad
  have hm' : m ≤ M := by
    have hreal : (m:ℝ) ≤ (M:ℝ) := hm.trans (Nat.le_ceil _)
    exact_mod_cast hreal
  exact ⟨⟨m, Nat.lt_succ_iff.mpr hm'⟩, Δ, ⟨hΔgood, hΔsep, hΔbound⟩, hprefix⟩

/- The short-systole part of BL (60): epsilon lies strictly below the
original window endpoints, so an appended short curve is a new coordinate. -/
theorem window_count_le_short_augmented_add_separating
    (D : BuddLionsTightGeometry G T H Q A)
    {r : ℕ} (lo hi : Fin r → ℝ) (s ε a B : ℝ)
    (hg : 2 ≤ g) (hs : 0 < s) (he : 0 < ε) (hea : ε < a) (haB : a ≤ B)
    (hgeneric : Q.NoSimpleLengthTies (X:=X))
    (hlo : ∀ i, s*a ≤ lo i) (hhi : ∀ i, hi i ≤ s*B)
    (hshort : HasShortSimple Q X (s*ε)) :
    Nat.card {Γ : Fin r → Curve Q X // WindowTuple Q X lo hi Γ} ≤
      Nat.card {Δ : Fin (r+1) → Curve Q X // ShortAugmentedTuple Q X lo hi (s*ε) Δ} +
      ∑ m : Fin 4, Nat.card {Δ : Fin (r+m.val) → Curve Q X //
        SeparatingTuple Q A X (r+m.val) (s*(2*B+ε)) Δ} := by
  classical
  let m : Option (Fin 4) → ℕ := fun i => match i with
    | none => 1
    | some j => j.val
  let R : (i : Option (Fin 4)) → (Fin (r+m i) → Curve Q X) → Prop := fun i =>
    match i with
    | none => ShortAugmentedTuple Q X lo hi (s*ε)
    | some j => SeparatingTuple Q A X (r+j.val) (s*(2*B+ε))
  let : ∀ i : Option (Fin 4), Finite {Δ // R i Δ} := by
    intro i
    cases i with
    | none => exact finite_short_augmented_tuples Q X lo hi (s*ε) (s*B) hhi
    | some j => exact finite_separating_tuples Q A X (r+j.val) (s*(2*B+ε))
  have hcard := card_le_sum_of_prefix_extensions r m (WindowTuple Q X lo hi) R
  have hbound : Nat.card {Γ : Fin r → Curve Q X // WindowTuple Q X lo hi Γ} ≤
      ∑ i : Option (Fin 4), Nat.card {Δ // R i Δ} := by
    apply hcard
    intro Γ hΓ
    obtain hshort' | hsep := D.augment_with_short g n r X s ε a B hg hs he hea haB
      hgeneric Γ hΓ.1 (fun i => ⟨(hlo i).trans (hΓ.2 i).1,
        (hΓ.2 i).2.trans (hhi i)⟩) hshort
    · obtain ⟨Δ, hgood, hpref, hlast⟩ := hshort'
      refine ⟨none, Δ, ⟨hgood, ?_, hlast⟩, hpref⟩
      intro i
      rw [hpref i]
      exact hΓ.2 i
    · obtain ⟨m', hm, Δ, hgood, hsep, hpref, hlength⟩ := hsep
      exact ⟨some ⟨m', by omega⟩, Δ, ⟨hgood, hsep, hlength⟩, hpref⟩
  simpa only [Fintype.sum_option, R, m] using hbound


/- The actual full primitive spectrum event is exactly the event used by the
geometric extension, through the fixed H identification; no simple restriction
is inserted into this event. -/
lemma hasShortTight_iff_actual (b : ℝ) : HasShortTight Q X b ↔
    ∃ γ : H.Primitive g n (tightCuspSurface G X), Q.cuspTight X γ ∧ H.length γ ≤ b := by
  constructor
  · rintro ⟨γ, hp, ht, hl⟩
    let γ' := Q.cuspPrimitiveEquiv g n X ⟨γ, hp⟩
    refine ⟨γ', ?_, ?_⟩
    · simpa only [TightGeodesicGeometry.cuspTight, γ', Equiv.symm_apply_apply] using ht
    · simpa only [γ', Q.cuspPrimitive_length] using hl
  · rintro ⟨γ, ht, hl⟩
    let γ' := (Q.cuspPrimitiveEquiv g n X).symm γ
    refine ⟨γ'.val, γ'.property, ht, ?_⟩
    have heq := Q.cuspPrimitive_length g n X γ'
    rw [Equiv.apply_symm_apply] at heq
    exact heq.symm.le.trans hl

lemma finite_actual_tight_bounded (b : ℝ) :
    Finite {γ : H.Primitive g n (tightCuspSurface G X) //
      Q.cuspTight X γ ∧ H.length γ ≤ b} := by
  classical
  apply Finite.of_injective (fun γ : {γ : H.Primitive g n (tightCuspSurface G X) //
      Q.cuspTight X γ ∧ H.length γ ≤ b} =>
    (⟨γ.val, (H.mem_shortPrimitive _ b γ.val).mpr γ.property.2⟩ :
      ↥(H.shortPrimitive (tightCuspSurface G X) b)))
  intro γ δ heq
  exact Subtype.ext (Subtype.mk.inj heq)

lemma hasShortTight_iff_actual_count_pos (b : ℝ) :
    HasShortTight Q X b ↔ 0 < Q.cuspTightCount X (Iic b) := by
  rw [hasShortTight_iff_actual Q X b]
  change (∃ γ, Q.cuspTight X γ ∧ H.length γ ≤ b) ↔
    0 < Nat.card {γ : H.Primitive g n (tightCuspSurface G X) //
      Q.cuspTight X γ ∧ H.length γ ≤ b}
  rw [Nat.card_pos_iff]
  constructor
  · rintro ⟨γ, ht, hl⟩
    exact ⟨⟨⟨γ, ht, hl⟩⟩, finite_actual_tight_bounded Q X b⟩
  · rintro ⟨⟨γ⟩, _⟩
    exact ⟨γ.val, γ.property⟩

/- Pointwise marked bad-event inequality used in Appendix F.4. The only
hypotheses beyond numerical/window guards are the approved classical geometric
objects. All count and extension steps below are local proved results. -/
theorem window_bad_indicator_le_short_add_separating
    (D : BuddLionsTightGeometry G T H Q A)
    {r : ℕ} (lo hi : Fin r → ℝ) (s ε a B : ℝ)
    (hg : 2 ≤ g) (hs : 0 < s) (he : 0 < ε) (hea : ε < a) (haB : a ≤ B)
    (hgenus : 2*B*((r:ℝ)+2)/ε+2 < g)
    (hgeneric : Q.NoSimpleLengthTies (X:=X))
    (hlo : ∀ i, s*a ≤ lo i) (hhi : ∀ i, hi i ≤ s*B) :
    (if BadConfiguration Q X (s*B) then
      Nat.card {Γ : Fin r → Curve Q X // WindowTuple Q X lo hi Γ} else 0) ≤
      Nat.card {Δ : Fin (r+1) → Curve Q X // ShortAugmentedTuple Q X lo hi (s*ε) Δ} +
      (∑ m : Fin 4, Nat.card {Δ : Fin (r+m.val) → Curve Q X //
        SeparatingTuple Q A X (r+m.val) (s*(2*B+ε)) Δ}) +
      ∑ m : Fin (⌈2*B*((r:ℝ)+2)/ε⌉₊+1),
        Nat.card {Δ : Fin (r+m.val) → Curve Q X //
          SeparatingTuple Q A X (r+m.val) (s*B*((r:ℝ)+2)) Δ} := by
  classical
  by_cases hbad : BadConfiguration Q X (s*B)
  · rw [if_pos hbad]
    by_cases hshort : HasShortSimple Q X (s*ε)
    · exact (window_count_le_short_augmented_add_separating Q A X D lo hi s ε a B
        hg hs he hea haB hgeneric hlo hhi hshort).trans (Nat.le_add_right _ _)
    · have hB : 0 < B := he.trans (hea.trans_le haB)
      exact (window_count_le_separating_of_no_short Q A X D lo hi s ε B
        hs he hB hgenus hgeneric hhi hshort hbad).trans (Nat.le_add_left _ _)
  · rw [if_neg hbad]
    exact Nat.zero_le _

end SpectrumTupleExtensions
end WP.Tight
