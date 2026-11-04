import WPFormalization.External.ShortFillingGeometry
import WPFormalization.External.PantsFamilyUniqueness
import WPFormalization.RandomGeometry.ShortCurveTopologicalBound

/-! The second count in G.3 uses the topology of the SAME genuine canonical
Hide piece. It is not the count of all nonsimple curves. The stable witness
only restricts the definition to its geometric domain; along the paper's
large-genus regime stability holds automatically. No Borel claim is made
about this predicate: the quantitative proof must produce a measurable
pointwise majorant, which also controls outer expectations and bad events. -/
noncomputable section
universe u v w
namespace WP.Critical
open WP.External WP.External.ShortFillingGeometry WP.External.PantsCluster
open WP.External.HyperbolicPacking
open scoped ENNReal
variable {P : PsiTheory} {G : WeilPeterssonGeometry.{u, v} P}
  {H : HyperbolicCurveGeometry.{u, v, w} G}
  (A : AmbientRealization H) (S : SingleCurvePieceClassics A)
  {g n : ℕ}

def IsNonsimpleNonPants {X : G.Moduli g n (fun _ => 0)}
    (γ : H.Primitive g n X) : Prop :=
  ∃ hg : Stable g n, ∃ hns : ¬H.simple γ,
    ¬HasPantsTopology (S.piece g n hg X γ hns).piece.model

lemma isNonsimpleNonPants_iff (hg : Stable g n)
    {X : G.Moduli g n (fun _ => 0)} (γ : H.Primitive g n X) :
    IsNonsimpleNonPants A S γ ↔ ∃ hns : ¬H.simple γ,
      ¬HasPantsTopology (S.piece g n hg X γ hns).piece.model := by
  constructor
  · rintro ⟨_, hns, hp⟩
    exact ⟨hns, hp⟩
  · rintro ⟨hns, hp⟩
    exact ⟨hg, hns, hp⟩

lemma IsNonsimpleNonPants.not_simple {X : G.Moduli g n (fun _ => 0)}
    {γ : H.Primitive g n X} (hγ : IsNonsimpleNonPants A S γ) : ¬H.simple γ := by
  obtain ⟨_, hns, _⟩ := hγ
  exact hns

abbrev NonsimpleNonPantsCurve (X : G.Moduli g n (fun _ => 0)) (L : ℝ) :=
  {γ : H.Primitive g n X // IsNonsimpleNonPants A S γ ∧ H.length γ ≤ L}

def nonsimpleNonPantsFinset (X : G.Moduli g n (fun _ => 0)) (L : ℝ) :
    Finset (H.Primitive g n X) := by
  classical
  exact (H.shortPrimitive X L).filter (IsNonsimpleNonPants A S)

lemma mem_nonsimpleNonPantsFinset (X : G.Moduli g n (fun _ => 0)) (L : ℝ)
    (γ : H.Primitive g n X) :
    γ ∈ nonsimpleNonPantsFinset A S X L ↔
      IsNonsimpleNonPants A S γ ∧ H.length γ ≤ L := by
  classical
  simp only [nonsimpleNonPantsFinset, Finset.mem_filter, H.mem_shortPrimitive]
  exact and_comm

def nonsimpleNonPantsCurveEquivFinset (X : G.Moduli g n (fun _ => 0)) (L : ℝ) :
    NonsimpleNonPantsCurve A S X L ≃ ↥(nonsimpleNonPantsFinset A S X L) where
  toFun γ := ⟨γ.val, (mem_nonsimpleNonPantsFinset A S X L γ.val).mpr γ.property⟩
  invFun γ := ⟨γ.val, (mem_nonsimpleNonPantsFinset A S X L γ.val).mp γ.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

def nonsimpleNonPantsCount (X : G.Moduli g n (fun _ => 0)) (L : ℝ) : ℝ≥0∞ :=
  ∑' _ : NonsimpleNonPantsCurve A S X L, (1 : ℝ≥0∞)

lemma nonsimpleNonPantsCount_eq_card (X : G.Moduli g n (fun _ => 0)) (L : ℝ) :
    nonsimpleNonPantsCount A S X L = (nonsimpleNonPantsFinset A S X L).card := by
  classical
  calc
    _ = ∑' _ : ↥(nonsimpleNonPantsFinset A S X L), (1 : ℝ≥0∞) :=
      (nonsimpleNonPantsCurveEquivFinset A S X L).tsum_eq (fun _ => (1 : ℝ≥0∞))
    _ = _ := by rw [tsum_fintype]; simp

lemma nonsimpleNonPantsCount_le_primitiveCount (X : G.Moduli g n (fun _ => 0))
    (L : ℝ) : nonsimpleNonPantsCount A S X L ≤ (H.primitiveCount X L : ℝ≥0∞) := by
  classical
  rw [nonsimpleNonPantsCount_eq_card, H.primitiveCount_eq_card]
  exact_mod_cast (Finset.card_le_card (Finset.filter_subset _ _) :
    (nonsimpleNonPantsFinset A S X L).card ≤ (H.shortPrimitive X L).card)

lemma one_le_nonsimpleNonPantsCount_of_bad (X : G.Moduli g n (fun _ => 0)) (L : ℝ)
    (hX : ∃ γ : H.Primitive g n X, IsNonsimpleNonPants A S γ ∧ H.length γ ≤ L) :
    1 ≤ nonsimpleNonPantsCount A S X L := by
  obtain ⟨γ, hγ⟩ := hX
  exact ENNReal.le_tsum (f := fun _ : NonsimpleNonPantsCurve A S X L => (1 : ℝ≥0∞))
    ⟨γ, hγ⟩

lemma nonsimpleNonPantsCount_eq_zero_of_no_bad
    (X : G.Moduli g n (fun _ => 0)) (L : ℝ)
    (hX : ¬∃ γ : H.Primitive g n X, IsNonsimpleNonPants A S γ ∧ H.length γ ≤ L) :
    nonsimpleNonPantsCount A S X L = 0 := by
  apply ENNReal.tsum_eq_zero.mpr
  intro γ
  exact False.elim (hX ⟨γ.val, γ.property⟩)

end WP.Critical
