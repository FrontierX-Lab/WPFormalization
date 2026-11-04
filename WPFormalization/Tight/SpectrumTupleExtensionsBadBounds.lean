import WPFormalization.Tight.SpectrumTupleExtensionsSetWindows
/- Appendix F.4 actual bad-event indicator bounds by a single short
good-curve count and finitely many separating tuple counts, and monotonicity
from arbitrary bounded window sets to their enclosing marked box. -/
noncomputable section
universe u v w z
namespace WP.Tight.SpectrumTupleExtensions
open External Set
open scoped ENNReal NNReal Classical
variable {P : PsiTheory} {G : WeilPeterssonGeometry.{u,v} P}
  {T : TightRegions G} {H : HyperbolicCurveGeometry.{u,v,w} G}
  (Q : TightGeodesicGeometry G T H) {g n : ℕ}
  (X : TightSurface G g 0 n (fun _=>0) (fun _=>0))

lemma short_simple_indicator_le_single_window_count (b : ℝ) :
    (if HasShortSimple Q X b then (1:ℝ≥0∞) else 0) ≤
      (Nat.card {Γ : Fin 1→Curve Q X // WindowTuple Q X (fun _=>0) (fun _=>b) Γ} : ℝ≥0∞) := by
  classical
  by_cases hs : HasShortSimple Q X b
  · rw [if_pos hs]
    obtain ⟨γ,hp,ht,hsimple,hl⟩ := hs
    have hw : WindowTuple Q X (fun _ : Fin 1=>0) (fun _=>b) (fun _=>γ) := by
      refine ⟨⟨?_,fun _=>⟨hp,ht,hsimple,ht.1,fun j=>Fin.elim0 j⟩,?_⟩,fun _=>⟨(Q.length_pos γ).le,hl⟩⟩
      · intro i j _
        exact Subsingleton.elim i j
      · intro i j hij
        exact (hij (Subsingleton.elim i j)).elim
    letI := finite_window_tuples Q X (fun _ : Fin 1=>0) (fun _=>b) b (fun _=>le_rfl)
    letI : Nonempty {Γ : Fin 1→Curve Q X // WindowTuple Q X (fun _=>0) (fun _=>b) Γ} := ⟨⟨_,hw⟩⟩
    exact_mod_cast (Nat.succ_le_iff.mpr Nat.card_pos)
  · rw [if_neg hs]
    exact zero_le

lemma bad_indicator_le_short_window_add_separating
    (A : TightMulticurveTopology.{u,v,w,z} G T H Q)
    (D : BuddLionsTightGeometry G T H Q A)
    (s ε B : ℝ) (hs : 0<s) (he : 0<ε) (hB : 0<B)
    (hgenus : 2*B*((0:ℝ)+2)/ε+2<g)
    (hgeneric : Q.NoSimpleLengthTies (X:=X)) :
    (if BadConfiguration Q X (s*B) then (1:ℝ≥0∞) else 0) ≤
      (Nat.card {Γ : Fin 1→Curve Q X // WindowTuple Q X (fun _=>0) (fun _=>s*ε) Γ} : ℝ≥0∞) +
      ∑m : Fin (⌈2*B*(((0:ℕ):ℝ)+2)/ε⌉₊+1),
        (Nat.card {Δ : Fin (0+m.val)→Curve Q X //
          SeparatingTuple Q A X (0+m.val) (s*B*(((0:ℕ):ℝ)+2)) Δ} : ℝ≥0∞) := by
  classical
  by_cases hb : BadConfiguration Q X (s*B)
  · rw [if_pos hb]
    by_cases hshort : HasShortSimple Q X (s*ε)
    · have hh:=short_simple_indicator_le_single_window_count Q X (s*ε)
      rw [if_pos hshort] at hh
      exact hh.trans le_self_add
    · have hh:=one_le_separating_count_of_bad_no_short Q X A D s ε B hs he hB hgenus hgeneric hshort hb
      have hh' : (1:ℝ≥0∞)≤∑m : Fin (⌈2*B*(((0:ℕ):ℝ)+2)/ε⌉₊+1),
          (Nat.card {Δ : Fin (0+m.val)→Curve Q X //
            SeparatingTuple Q A X (0+m.val) (s*B*(((0:ℕ):ℝ)+2)) Δ} : ℝ≥0∞) := by
        exact_mod_cast hh
      exact hh'.trans le_add_self
  · rw [if_neg hb]
    exact zero_le

lemma good_set_count_le_closed_box {r : ℕ} (W : Fin r→Set ℝ) (a b : ℝ)
    (hW : ∀i,W i⊆Icc a b) :
    Nat.card {Γ : Fin r→Curve Q X // GoodSetTuple Q X W Γ} ≤
      Nat.card {Γ : Fin r→Curve Q X // WindowTuple Q X (fun _=>a) (fun _=>b) Γ} := by
  letI := finite_window_tuples Q X (fun _ : Fin r=>a) (fun _=>b) b (fun _=>le_rfl)
  apply Nat.card_le_card_of_injective (fun Γ : {Γ : Fin r→Curve Q X // GoodSetTuple Q X W Γ}=>
    (⟨Γ.val,Γ.property.1,fun i=>hW i (Γ.property.2 i)⟩ :
      {Γ : Fin r→Curve Q X // WindowTuple Q X (fun _=>a) (fun _=>b) Γ}))
  intro a b h
  exact Subtype.ext (Subtype.mk.inj h)

end WP.Tight.SpectrumTupleExtensions
