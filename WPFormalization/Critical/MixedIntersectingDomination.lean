import WPFormalization.Critical.MixedGeometricTuples
noncomputable section
set_option maxHeartbeats 0
universe aa bb cc dd
namespace WP.Critical
open WP.External WP.RandomGeometry MeasureTheory Filter
open scoped Classical ENNReal Topology
variable {P : PsiTheory} {G : WeilPeterssonGeometry.{aa,bb} P}
    {H : HyperbolicCurveGeometry.{aa,bb,cc} G} (T : MulticurveTopology.{aa,bb,cc,dd} G H)
    {g n r k : ℕ}

def ShortIntersectingSimpleTuple (X : G.Moduli g n (fun _ => 0)) (t : ℕ) (L : ℝ) :=
  {γ : Fin t→H.Primitive g n X // Function.Injective γ ∧ (∀i,H.simple (γ i)) ∧
    (∀i,H.length (γ i)≤L) ∧ ¬∀i j,i≠j → T.disjoint (γ i) (γ j)}

def allShortIntersectingSimpleTupleCount (X : G.Moduli g n (fun _ => 0))
    (t : ℕ) (L : ℝ) : ℝ≥0∞ := ∑' _ : ShortIntersectingSimpleTuple T X t L,(1 : ℝ≥0∞)

def mixedIntersectingForget (X : G.Moduli g n (fun _ => 0))
    (I : Fin (r+k)→Set ℝ) (L : ℝ) (hIL : ∀i,I i⊆Set.Icc 0 L) :
    {γ : MixedWindowTuple T X I // ¬TupleDisjoint T γ.val} →
      ShortIntersectingSimpleTuple T X (r+k) L := fun γ =>
  ⟨γ.val.val,γ.val.property.1,γ.val.property.2.1.simple T,
    fun i => (hIL i (γ.val.property.2.2 i)).2,γ.property⟩

lemma mixedIntersectingForget_injective (X : G.Moduli g n (fun _ => 0))
    (I : Fin (r+k)→Set ℝ) (L : ℝ) (hIL : ∀i,I i⊆Set.Icc 0 L) :
    Function.Injective (mixedIntersectingForget T X I L hIL) := by
  intro a b hab
  have hγ := congrArg (fun z : ShortIntersectingSimpleTuple T X (r+k) L => z.val) hab
  change a.val.val=b.val.val at hγ
  exact Subtype.ext (Subtype.ext hγ)

lemma mixedIntersectingWindowTupleCount_le_allShort (X : G.Moduli g n (fun _ => 0))
    (I : Fin (r+k)→Set ℝ) (L : ℝ) (hIL : ∀i,I i⊆Set.Icc 0 L) :
    mixedIntersectingWindowTupleCount T X I≤allShortIntersectingSimpleTupleCount T X (r+k) L :=
  ENNReal.tsum_comp_le_tsum_of_injective
    (mixedIntersectingForget_injective T X I L hIL) (fun _ => (1 : ℝ≥0∞))

lemma allShortIntersectingSimpleTupleCount_zero_of_le_one
    (X : G.Moduli g n (fun _ => 0)) (t : ℕ) (ht : t≤1) (L : ℝ) :
    allShortIntersectingSimpleTupleCount T X t L=0 := by
  apply ENNReal.tsum_eq_zero.mpr
  intro γ
  apply False.elim
  apply γ.property.2.2.2
  intro i j hij
  have he : i=j := Fin.ext (by omega)
  exact False.elim (hij he)

lemma mixedIntersectingWindowTupleCount_tendsto_of_allShort
    (n : ℕ→ℕ) (r k : ℕ) (I : Fin (r+k)→Set ℝ) (L : ℝ)
    (hIL : ∀i,I i⊆Set.Icc 0 L)
    (hshort : Tendsto (fun g => ∫⁻ X,allShortIntersectingSimpleTupleCount T X (r+k) L
      ∂wpProbability G g (n g)) atTop (𝓝 0)) :
    Tendsto (fun g => ∫⁻ X,mixedIntersectingWindowTupleCount T X I
      ∂wpProbability G g (n g)) atTop (𝓝 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hshort
  · exact Filter.Eventually.of_forall (fun _ => bot_le)
  · exact Filter.Eventually.of_forall (fun g => lintegral_mono
      (fun X => mixedIntersectingWindowTupleCount_le_allShort T X I L hIL))
end WP.Critical
