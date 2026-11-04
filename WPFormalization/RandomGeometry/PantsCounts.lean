import WPFormalization.External.HyperbolicCurveGeometry
import WPFormalization.RandomGeometry.PantsFiniteCount

/-! Finite-catalog realization of the geometric counts. These are the original
geodesic counts in H, rather than an unrelated collection of random variables.
No geometric moment or asymptotic is assumed. -/
noncomputable section
universe u v w
namespace WP.External.HyperbolicCurveGeometry
open MeasureTheory
variable {P : PsiTheory} {G : WP.External.WeilPeterssonGeometry.{u,v} P}
    (H : WP.External.HyperbolicCurveGeometry.{u,v,w} G) {g n : ℕ}

def shortPlanar (X : G.Moduli g n (fun _ => 0)) (k : ℕ) (L : ℝ) :
    Finset (H.Primitive g n X) := by
  classical
  exact (H.shortPrimitive X L).filter
    (fun γ => ∃ S : Finset (Fin n), H.planarSide γ = some S ∧ S.card = k)

lemma mem_shortPlanar (X : G.Moduli g n (fun _ => 0)) (k : ℕ) (L : ℝ)
    (γ : H.Primitive g n X) :
    γ ∈ H.shortPlanar X k L ↔ H.length γ ≤ L ∧
      ∃ S : Finset (Fin n), H.planarSide γ = some S ∧ S.card = k := by
  classical
  simp only [shortPlanar, Finset.mem_filter, H.mem_shortPrimitive]

lemma planarCount_eq_card (X : G.Moduli g n (fun _ => 0)) (k : ℕ) (L : ℝ) :
    H.planarCount X k L = (H.shortPlanar X k L).card := by
  classical
  unfold planarCount
  let e : {γ : H.Primitive g n X // H.length γ ≤ L ∧
      ∃ S : Finset (Fin n), H.planarSide γ = some S ∧ S.card = k} ≃
      {γ : H.Primitive g n X // γ ∈ H.shortPlanar X k L} :=
    Equiv.subtypeEquivRight (fun γ => (H.mem_shortPlanar X k L γ).symm)
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_coe]

def planarLabels {X : G.Moduli g n (fun _ => 0)} (γ : H.Primitive g n X) :
    Finset (Fin n) := (H.planarSide γ).getD ∅

lemma planarLabels_card {X : G.Moduli g n (fun _ => 0)} (γ : H.Primitive g n X)
    (k : ℕ) (L : ℝ) (hγ : γ ∈ H.shortPlanar X k L) :
    (H.planarLabels γ).card = k := by
  obtain ⟨S, hS, hc⟩ := (H.mem_shortPlanar X k L γ).mp hγ |>.2
  simpa only [planarLabels, hS, Option.getD_some] using hc

lemma pantsCount_le_half_labels (X : G.Moduli g n (fun _ => 0)) (L : ℝ)
    (hdisjoint : (H.shortPlanar X 2 L : Set (H.Primitive g n X)).PairwiseDisjoint
      (fun γ => H.planarLabels γ)) :
    2 * H.pantsCount X L ≤ n := by
  change 2 * H.planarCount X 2 L ≤ n
  rw [H.planarCount_eq_card]
  exact WP.RandomGeometry.disjoint_pair_card_bound _ _
    (fun γ hγ => H.planarLabels_card γ 2 L hγ) hdisjoint

end WP.External.HyperbolicCurveGeometry
