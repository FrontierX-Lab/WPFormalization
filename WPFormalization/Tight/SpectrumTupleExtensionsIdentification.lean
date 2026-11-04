import WPFormalization.Tight.SpectrumTupleExtensions

/- Appendix F.4 pointwise identification of the full primitive tight tuple
count, using exactly H.Primitive, with the simple/disjoint count outside the
actual bad configuration. All count transports and the unmarked extension
bound are proved locally; no distribution or moment conclusion is assumed. -/
noncomputable section
universe u v w z

namespace WP.Tight.SpectrumTupleExtensions
open External Set
variable {P : PsiTheory} {G : WeilPeterssonGeometry.{u,v} P}
  {T : TightRegions G} {H : HyperbolicCurveGeometry.{u,v,w} G}
  (Q : TightGeodesicGeometry G T H) {g n : ℕ}
  (X : TightSurface G g 0 n (fun _ => 0) (fun _ => 0))

def TightWindowTuple {r : ℕ} (lo hi : Fin r → ℝ)
    (Γ : Fin r → Curve Q X) : Prop :=
  Function.Injective Γ ∧ ∀ i, Q.primitive (Γ i) ∧ Q.IsTight (Γ i) ∧
    lo i ≤ Q.length (Γ i) ∧ Q.length (Γ i) ≤ hi i

def ActualTightWindowTuple {r : ℕ} (lo hi : Fin r → ℝ)
    (Γ : Fin r → H.Primitive g n (tightCuspSurface G X)) : Prop :=
  Function.Injective Γ ∧ ∀ i, Q.cuspTight X (Γ i) ∧
    lo i ≤ H.length (Γ i) ∧ H.length (Γ i) ≤ hi i

lemma windowTuple_iff_tightWindowTuple_of_not_bad {r : ℕ}
    (lo hi : Fin r → ℝ) (b : ℝ) (hhi : ∀ i, hi i ≤ b)
    (hnobad : ¬BadConfiguration Q X b) (Γ : Fin r → Curve Q X) :
    WindowTuple Q X lo hi Γ ↔ TightWindowTuple Q X lo hi Γ := by
  constructor
  · rintro ⟨hgood, hwindow⟩
    exact ⟨hgood.1, fun i => ⟨(hgood.2.1 i).1, (hgood.2.1 i).2.1, hwindow i⟩⟩
  · rintro ⟨hinj, htight⟩
    refine ⟨⟨hinj, ?_, ?_⟩, fun i => (htight i).2.2⟩
    · intro i
      refine ⟨(htight i).1, (htight i).2.1, ?_, ?_⟩
      · by_contra hnot
        exact hnobad (Or.inl ⟨Γ i, (htight i).1, (htight i).2.1,
          (htight i).2.2.2.trans (hhi i), hnot⟩)
      · exact ⟨(htight i).2.1.1, fun j => Fin.elim0 j⟩
    · intro i j hij
      by_contra hnot
      exact hnobad (Or.inr ⟨Γ i, Γ j, fun heq => hij (hinj heq),
        (htight i).1, (htight j).1, (htight i).2.1, (htight j).2.1,
        (htight i).2.2.2.trans (hhi i), (htight j).2.2.2.trans (hhi j), hnot⟩)

/- Every coordinate is transported through the approved equivalence with the
same actual H.Primitive; the construction adds no simplicity condition. -/
def tightWindowTupleEquivActual {r : ℕ} (lo hi : Fin r → ℝ) :
    {Γ : Fin r → Curve Q X // TightWindowTuple Q X lo hi Γ} ≃
      {Γ : Fin r → H.Primitive g n (tightCuspSurface G X) //
        ActualTightWindowTuple Q X lo hi Γ} where
  toFun Γ := ⟨fun i => Q.cuspPrimitiveEquiv g n X ⟨Γ.val i, (Γ.property.2 i).1⟩, by
    refine ⟨?_, ?_⟩
    · intro i j heq
      exact Γ.property.1 (congrArg Subtype.val ((Q.cuspPrimitiveEquiv g n X).injective heq))
    · intro i
      refine ⟨?_, ?_, ?_⟩
      · simpa only [TightGeodesicGeometry.cuspTight, Equiv.symm_apply_apply]
          using (Γ.property.2 i).2.1
      · simpa only [Q.cuspPrimitive_length] using (Γ.property.2 i).2.2.1
      · simpa only [Q.cuspPrimitive_length] using (Γ.property.2 i).2.2.2⟩
  invFun Γ := ⟨fun i => ((Q.cuspPrimitiveEquiv g n X).symm (Γ.val i)).val, by
    refine ⟨?_, ?_⟩
    · intro i j heq
      apply Γ.property.1
      apply (Q.cuspPrimitiveEquiv g n X).symm.injective
      exact Subtype.ext heq
    · intro i
      refine ⟨((Q.cuspPrimitiveEquiv g n X).symm (Γ.val i)).property,
        (Γ.property.2 i).1, ?_, ?_⟩
      · have hl := Q.cuspPrimitive_length g n X ((Q.cuspPrimitiveEquiv g n X).symm (Γ.val i))
        rw [Equiv.apply_symm_apply] at hl
        exact (Γ.property.2 i).2.1.trans_eq hl
      · have hl := Q.cuspPrimitive_length g n X ((Q.cuspPrimitiveEquiv g n X).symm (Γ.val i))
        rw [Equiv.apply_symm_apply] at hl
        exact hl.symm.le.trans (Γ.property.2 i).2.2⟩
  left_inv Γ := by
    apply Subtype.ext
    funext i
    exact congrArg Subtype.val ((Q.cuspPrimitiveEquiv g n X).symm_apply_apply _)
  right_inv Γ := by
    apply Subtype.ext
    funext i
    exact (Q.cuspPrimitiveEquiv g n X).apply_symm_apply (Γ.val i)

lemma tight_window_count_eq_actual {r : ℕ} (lo hi : Fin r → ℝ) :
    Nat.card {Γ : Fin r → Curve Q X // TightWindowTuple Q X lo hi Γ} =
      Nat.card {Γ : Fin r → H.Primitive g n (tightCuspSurface G X) //
        ActualTightWindowTuple Q X lo hi Γ} :=
  Nat.card_congr (tightWindowTupleEquivActual Q X lo hi)

/- On the complement of the actual full primitive bad configuration, distinct
primitive tight ordered tuples are exactly simple/disjoint good tuples. This
is the pointwise count identity needed before invoking the moment method. -/
theorem actual_count_eq_window_count_of_not_bad {r : ℕ}
    (lo hi : Fin r → ℝ) (b : ℝ) (hhi : ∀ i, hi i ≤ b)
    (hnobad : ¬BadConfiguration Q X b) :
    Nat.card {Γ : Fin r → H.Primitive g n (tightCuspSurface G X) //
      ActualTightWindowTuple Q X lo hi Γ} =
      Nat.card {Γ : Fin r → Curve Q X // WindowTuple Q X lo hi Γ} := by
  rw [←tight_window_count_eq_actual Q X lo hi]
  have heq : TightWindowTuple Q X lo hi = WindowTuple Q X lo hi := by
    funext Γ
    exact propext (windowTuple_iff_tightWindowTuple_of_not_bad Q X lo hi b hhi hnobad Γ).symm
  rw [heq]


lemma empty_window_count (lo hi : Fin 0 → ℝ) :
    Nat.card {Γ : Fin 0 → Curve Q X // WindowTuple Q X lo hi Γ} = 1 := by
  have hwindow : WindowTuple Q X lo hi (fun i => Fin.elim0 i) := by
    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
    · intro i
      exact Fin.elim0 i
    · intro i
      exact Fin.elim0 i
    · intro i
      exact Fin.elim0 i
    · intro i
      exact Fin.elim0 i
  let : Nonempty {Γ : Fin 0 → Curve Q X // WindowTuple Q X lo hi Γ} :=
    ⟨⟨_, hwindow⟩⟩
  exact Nat.card_unique

/- The same extension with no marked coordinates controls the probability of
a bad event once the separating tuple expectations are bounded locally. -/
theorem one_le_separating_count_of_bad_no_short
    (A : TightMulticurveTopology G T H Q) (D : BuddLionsTightGeometry G T H Q A)
    (s ε B : ℝ) (hs : 0 < s) (he : 0 < ε) (hB : 0 < B)
    (hgenus : 2*B*((0:ℝ)+2)/ε+2 < g)
    (hgeneric : Q.NoSimpleLengthTies (X:=X))
    (hnoshort : ¬HasShortSimple Q X (s*ε))
    (hbad : BadConfiguration Q X (s*B)) :
    1 ≤ ∑ m : Fin (⌈2*B*(((0:ℕ):ℝ)+2)/ε⌉₊+1),
      Nat.card {Δ : Fin (0+m.val) → Curve Q X //
        SeparatingTuple Q A X (0+m.val) (s*B*(((0:ℕ):ℝ)+2)) Δ} := by
  have hcard := window_count_le_separating_of_no_short Q A X D
    (fun _ : Fin 0 => 0) (fun _ : Fin 0 => 0) s ε B hs he hB (by simpa only [Nat.cast_zero] using hgenus) hgeneric
    (fun i => Fin.elim0 i) hnoshort hbad
  simpa only [empty_window_count] using hcard

end WP.Tight.SpectrumTupleExtensions
