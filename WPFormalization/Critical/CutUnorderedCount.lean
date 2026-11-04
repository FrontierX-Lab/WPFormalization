import WPFormalization.Critical.CutActualEstimate
noncomputable section
set_option maxHeartbeats 0
universe aa bb cc dd
namespace WP.Critical.CutGraphOrbits
open WP.External Finset MeasureTheory
open scoped ENNReal Classical
variable {P : PsiTheory} {G : WeilPeterssonGeometry.{aa,bb} P}
  {H : HyperbolicCurveGeometry.{aa,bb,cc} G} (T : MulticurveTopology.{aa,bb,cc,dd} G H)
  {g n k Q : ℕ} {S : CutSkeleton k Q}

abbrev CutTupleIndex (s : Finset (Orbits T S (g:=g) (n:=n)))
    (X : G.Moduli g n (fun _ => 0)) :=
  Σ o : s, {γ : Fin k → H.Primitive g n X // T.orbitMem o.val.val X γ}

def tupleRange {s : Finset (Orbits T S (g:=g) (n:=n))}
    {X : G.Moduli g n (fun _ => 0)} (j : CutTupleIndex T s X) : Finset (H.Primitive g n X) :=
  univ.image j.2.val

def IsUnorderedCut (s : Finset (Orbits T S (g:=g) (n:=n))) (L : ℝ)
    (X : G.Moduli g n (fun _ => 0)) (U : Finset (H.Primitive g n X)) : Prop :=
  ∃ j : CutTupleIndex T s X, tupleRange T j=U ∧ ∀ i, H.length (j.2.val i) ≤ L

/-- The number of unordered sets of physical primitive curves occurring in
one of the actual selected orbits. Existential ordering counts each set once. -/
def unorderedCutCount (s : Finset (Orbits T S (g:=g) (n:=n))) (L : ℝ)
    (X : G.Moduli g n (fun _ => 0)) : ℝ≥0∞ :=
  ∑' U : {U : Finset (H.Primitive g n X) // IsUnorderedCut T s L X U}, (1 : ℝ≥0∞)

lemma tupleRange_card {s : Finset (Orbits T S (g:=g) (n:=n))}
    {X : G.Moduli g n (fun _ => 0)} (j : CutTupleIndex T s X) :
    (tupleRange T j).card=k := by
  rw [tupleRange,card_image_of_injective _ (T.orbit_injective j.1.val.val X j.2.val j.2.property),card_univ,Fintype.card_fin]

lemma unorderedCutCount_le_ordered (s : Finset (Orbits T S (g:=g) (n:=n))) (L : ℝ)
    (X : G.Moduli g n (fun _ => 0)) :
    unorderedCutCount T s L X ≤ ∑ o ∈ s, T.orbitSum o.val (cutLengthTest k L) X := by
  classical
  let W := {U : Finset (H.Primitive g n X) // IsUnorderedCut T s L X U}
  let pick : W → CutTupleIndex T s X := fun U => Classical.choose U.property
  have hp (U : W) : tupleRange T (pick U)=U.val ∧ ∀ i, H.length ((pick U).2.val i) ≤ L :=
    Classical.choose_spec U.property
  have hinj : Function.Injective pick := by
    intro U V h
    apply Subtype.ext
    exact (hp U).1.symm.trans ((congrArg (tupleRange T) h).trans (hp V).1)
  let weight : CutTupleIndex T s X → ℝ≥0∞ := fun j => cutLengthTest k L (fun i => H.length (j.2.val i))
  have hw (U : W) : weight (pick U)=1 := by
    apply Set.indicator_of_mem
    exact ⟨fun i => (H.length_pos _).le,(hp U).2⟩
  calc
    _ = ∑' U : W, weight (pick U) := tsum_congr (fun U => (hw U).symm)
    _ ≤ ∑' j : CutTupleIndex T s X, weight j := ENNReal.tsum_comp_le_tsum_of_injective hinj weight
    _ = _ := by
      rw [ENNReal.tsum_sigma']
      change (∑' o : s, T.orbitSum o.val.val (cutLengthTest k L) X)=_
      rw [tsum_fintype]
      exact sum_coe_sort s (fun o : Orbits T S (g:=g) (n:=n) => T.orbitSum o.val (cutLengthTest k L) X)
end WP.Critical.CutGraphOrbits
