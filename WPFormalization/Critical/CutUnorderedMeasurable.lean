import WPFormalization.Critical.CutUnorderedCount
import WPFormalization.External.MulticurveCountingMeasurability

noncomputable section
namespace WP.Critical.CutGraphOrbits
open WP.External MeasureTheory Finset
open scoped ENNReal Classical
universe ee ff gg hh
variable {P : PsiTheory} {G : WeilPeterssonGeometry.{ee,ff} P}
  {H : HyperbolicCurveGeometry.{ee,ff,gg} G} (T : MulticurveTopology.{ee,ff,gg,hh} G H)
  {g n k Q : ℕ} {S : CutSkeleton k Q}

lemma unorderedCutCount_eq_classical (s : Finset (Orbits T S (g:=g) (n:=n)))
    (L : ℝ) (X : G.Moduli g n (fun _ => 0)) :
    unorderedCutCount T s L X =
      T.unorderedLengthCount (s.image Subtype.val) (cutLengthBox k L) X := by
  classical
  have hpred (U : Finset (H.Primitive g n X)) : IsUnorderedCut T s L X U ↔
      ∃ o ∈ s.image Subtype.val, ∃ γ : Fin k → H.Primitive g n X,
        T.orbitMem o X γ ∧ univ.image γ=U ∧ (fun i => H.length (γ i)) ∈ cutLengthBox k L := by
    constructor
    · rintro ⟨j,hU,hL⟩
      exact ⟨j.1.val.val,mem_image.mpr ⟨j.1.val,j.1.property,rfl⟩,
        j.2.val,j.2.property,hU,⟨fun i => (H.length_pos _).le,hL⟩⟩
    · rintro ⟨o,ho,γ,hγ,hU,hB⟩
      obtain ⟨q,hq,rfl⟩ := mem_image.mp ho
      exact ⟨⟨⟨q,hq⟩,⟨γ,hγ⟩⟩,hU,hB.2⟩
  exact (Equiv.subtypeEquivRight hpred).tsum_eq (fun _ => (1 : ℝ≥0∞))

lemma unorderedCutCount_measurable (MC : MulticurveCountingMeasurability G H T)
    (s : Finset (Orbits T S (g:=g) (n:=n))) (L : ℝ) :
    Measurable (unorderedCutCount T s L) := by
  have he : unorderedCutCount T s L =
      T.unorderedLengthCount (s.image Subtype.val) (cutLengthBox k L) :=
    funext (unorderedCutCount_eq_classical T s L)
  rw [he]
  exact MC.unorderedLengthCount_measurable _ _ measurableSet_Icc
    (by simpa only [cutLengthBox,IsClosed.closure_eq isClosed_Icc] using
      (isCompact_Icc : IsCompact (Set.Icc (fun _ : Fin k => (0 : ℝ)) (fun _ => L))))

lemma unorderedCutCount_aemeasurable (MC : MulticurveCountingMeasurability G H T)
    (s : Finset (Orbits T S (g:=g) (n:=n))) (L : ℝ)
    (μ : Measure (G.Moduli g n (fun _ => 0))) :
    AEMeasurable (unorderedCutCount T s L) μ :=
  (unorderedCutCount_measurable T MC s L).aemeasurable
end WP.Critical.CutGraphOrbits
