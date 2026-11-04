import WPFormalization.Critical.NonsimpleNonPantsCounts
import WPFormalization.External.ShortFullFillingGeometry

/-! Original G.3(G.4) counts literal complement filling, rather than merely
the topology of a chosen bounded supporting piece. The latter count is a
stronger majorant. Hide's full classical filling clause supplies the local
one-way bridge below; no equivalence with a weaker loop criterion is assumed. -/
noncomputable section
universe u v w z
namespace WP.Critical
open WP.External WP.External.HyperbolicPacking WP.External.ShortFillingGeometry
open WP.External.PantsCluster WP.External.ShortFullFillingGeometry
open scoped ENNReal
variable {P : PsiTheory} {G : WeilPeterssonGeometry.{u,v} P}
  {H : HyperbolicCurveGeometry.{u,v,w} G}
  (A : AmbientRealization H) {g n : ℕ}

def FillsTwoCuspPants {X : G.Moduli g n (fun _ => 0)}
    (γ : H.Primitive g n X) : Prop :=
  ∃ Q : IntrinsicPiece (A.model g n X), HasPantsTopology Q.model ∧
    ∃ β : Q.model.curves.Primitive,
      Q.primitiveProjection β = A.primitiveEquiv g n X γ ∧
      Q.model.curves.trace β ⊆ intrinsicInterior Q.model ∧
      FullFilling Q.model Q.boundary β

def IsNonsimpleNotFillingPants {X : G.Moduli g n (fun _ => 0)}
    (γ : H.Primitive g n X) : Prop :=
  ¬ H.simple γ ∧ ¬ FillsTwoCuspPants A γ

def nonFillingPantsFinset (X : G.Moduli g n (fun _ => 0)) (L : ℝ) :
    Finset (H.Primitive g n X) := by
  classical
  exact (H.shortPrimitive X L).filter (IsNonsimpleNotFillingPants A)

lemma mem_nonFillingPantsFinset (X : G.Moduli g n (fun _ => 0)) (L : ℝ)
    (γ : H.Primitive g n X) :
    γ ∈ nonFillingPantsFinset A X L ↔
      IsNonsimpleNotFillingPants A γ ∧ H.length γ ≤ L := by
  classical
  simp only [nonFillingPantsFinset, Finset.mem_filter, H.mem_shortPrimitive]
  exact and_comm

def nonFillingPantsCount (X : G.Moduli g n (fun _ => 0)) (L : ℝ) : ℝ≥0∞ :=
  (nonFillingPantsFinset A X L).card

lemma isNonsimpleNonPants_of_not_filling
    (T : MulticurveTopology.{u,v,w,z} G H) (AC : AmbientCurveCompatibility A T)
    (S : SingleCurvePieceClassics A)
    (HF : FullSingleCurveFillingClassics A AC.complete_domain S)
    (hg : Stable g n) {X : G.Moduli g n (fun _ => 0)}
    (γ : H.Primitive g n X) (hγ : IsNonsimpleNotFillingPants A γ) :
    IsNonsimpleNonPants A S γ := by
  refine (isNonsimpleNonPants_iff A S hg γ).mpr ⟨hγ.1, ?_⟩
  intro hp
  obtain ⟨β, hβ, hi, hf⟩ := HF.fills g n hg X γ hγ.1
  exact hγ.2 ⟨(S.piece g n hg X γ hγ.1).piece, hp, β, hβ, hi, hf⟩

lemma nonFillingPantsCount_le_nonsimpleNonPantsCount
    (T : MulticurveTopology.{u,v,w,z} G H) (AC : AmbientCurveCompatibility A T)
    (S : SingleCurvePieceClassics A)
    (HF : FullSingleCurveFillingClassics A AC.complete_domain S)
    (hg : Stable g n) (X : G.Moduli g n (fun _ => 0)) (L : ℝ) :
    nonFillingPantsCount A X L ≤ nonsimpleNonPantsCount A S X L := by
  classical
  rw [nonsimpleNonPantsCount_eq_card]
  change ((nonFillingPantsFinset A X L).card : ℝ≥0∞) ≤
    ((nonsimpleNonPantsFinset A S X L).card : ℝ≥0∞)
  have hsub : nonFillingPantsFinset A X L ⊆ nonsimpleNonPantsFinset A S X L := by
    intro γ hγ
    obtain ⟨hb, hl⟩ := (mem_nonFillingPantsFinset A X L γ).mp hγ
    exact (mem_nonsimpleNonPantsFinset A S X L γ).mpr
      ⟨isNonsimpleNonPants_of_not_filling A T AC S HF hg γ hb, hl⟩
  exact_mod_cast (Finset.card_le_card hsub)

end WP.Critical
