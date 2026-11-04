import WPFormalization.RandomGeometry.PantsWindowMoments

/-! The literal integer count of ordered distinct curves in arbitrary windows. -/
noncomputable section
universe u v w z
namespace WP.RandomGeometry
open WP.External MeasureTheory
open scoped ENNReal
variable {P : PsiTheory} {G : WeilPeterssonGeometry.{u,v} P}
    (H : HyperbolicCurveGeometry.{u,v,w} G) {g n r : ℕ}

def pantsWindowTest (I : Fin r → Set ℝ) (x : Fin r → ℝ) : ℝ≥0∞ := by
  classical
  exact if ∀i, x i ∈ I i then 1 else 0

def pantsWindowCount (X : G.Moduli g n (fun _ => 0)) (L : ℝ)
    (I : Fin r → Set ℝ) : ℕ :=
  Nat.card {γ : H.OrderedPlanarTuple X 2 L r // ∀i, H.length (γ.val i) ∈ I i}

lemma pantsWindowSum_test_eq_count (X : G.Moduli g n (fun _ => 0)) (L : ℝ)
    (I : Fin r → Set ℝ) :
    pantsWindowSum (H:=H) X L (pantsWindowTest I) = (pantsWindowCount H X L I : ℝ≥0∞) := by
  classical
  let p := fun γ : H.OrderedPlanarTuple X 2 L r => ∀i, H.length (γ.val i) ∈ I i
  have hs := tsum_subtype {γ : H.OrderedPlanarTuple X 2 L r | p γ} (fun _ => (1 : ℝ≥0∞))
  let e : {γ : H.OrderedPlanarTuple X 2 L r | p γ} ≃
      {γ : H.OrderedPlanarTuple X 2 L r // p γ} := Equiv.refl _
  calc
    _ = ∑' γ : H.OrderedPlanarTuple X 2 L r,
        ({γ : H.OrderedPlanarTuple X 2 L r | p γ}).indicator (fun _ => (1 : ℝ≥0∞)) γ := by
      apply tsum_congr
      intro γ
      by_cases hp : p γ <;> simp [pantsWindowTest,Set.indicator,p,hp]
    _ = ∑' _ : {γ : H.OrderedPlanarTuple X 2 L r | p γ}, (1 : ℝ≥0∞) := hs.symm
    _ = ∑' _ : {γ : H.OrderedPlanarTuple X 2 L r // p γ}, (1 : ℝ≥0∞) :=
      e.tsum_eq (fun _ => (1 : ℝ≥0∞))
    _ = _ := by rw [tsum_fintype]; simp [pantsWindowCount,Nat.card_eq_fintype_card,p]

lemma pants_window_set_measurable (I : Fin r → Set ℝ) (hI : ∀i, MeasurableSet (I i)) :
    MeasurableSet {x : Fin r → ℝ | ∀i, x i ∈ I i} := by
  have h := MeasurableSet.iInter (fun i : Fin r =>
    (hI i).preimage (measurable_pi_apply i : Measurable (fun x : Fin r → ℝ => x i)))
  convert h using 1
  ext x
  simp

lemma pantsWindowTest_measurable (I : Fin r → Set ℝ) (hI : ∀i, MeasurableSet (I i)) :
    Measurable (pantsWindowTest I) := by
  classical
  exact Measurable.ite (pants_window_set_measurable I hI) measurable_const measurable_const

lemma pantsWindowTest_support (I : Fin r → Set ℝ) (L : ℝ)
    (hI : ∀i, I i ⊆ Set.Icc 0 L) :
    ∀x, ¬ (∀i, x i ≤ L) → pantsWindowTest I x=0 := by
  classical
  intro x hx
  have hn : ¬ ∀i, x i ∈ I i := by
    intro hi
    exact hx (fun i => (hI i (hi i)).2)
  simp [pantsWindowTest,hn]

lemma pantsWindowCount_measurable (T : MulticurveTopology.{u,v,w,z} G H)
    (C : CollarGeometry G H T) (MI : MirzakhaniIntegration G H T)
    (hg : 1 ≤ g) (hr : 0 < r) (L : ℝ) (hL : L < 2*Real.arsinh 1)
    (I : Fin r → Set ℝ) (hI : ∀i, MeasurableSet (I i)) (hsub : ∀i, I i ⊆ Set.Icc 0 L) :
    Measurable (fun X : G.Moduli g n (fun _ => 0) => (pantsWindowCount H X L I : ℝ)) := by
  have hm : Measurable (fun X : G.Moduli g n (fun _ => 0) =>
      ∑' o : PantsStarOrbit T g n r, T.orbitSum o.val (pantsWindowTest I) X) :=
    Measurable.ennreal_tsum (fun o => MI.orbitSum_measurable o.val _ (pantsWindowTest_measurable I hI))
  have he : (fun X : G.Moduli g n (fun _ => 0) =>
      ∑' o : PantsStarOrbit T g n r, T.orbitSum o.val (pantsWindowTest I) X) =
      fun X => (pantsWindowCount H X L I : ℝ≥0∞) := by
    funext X
    exact (pants_weighted_orbit_sum T C hg hr X L hL _ (pantsWindowTest_support I L hsub)).trans
      (pantsWindowSum_test_eq_count H X L I)
  rw [he] at hm
  simpa using hm.ennreal_toReal

end WP.RandomGeometry
