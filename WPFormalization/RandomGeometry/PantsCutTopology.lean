import WPFormalization.External.CollarGeometry
import WPFormalization.RandomGeometry.PantsCutClassification
import WPFormalization.RandomGeometry.PantsCounts

/-! Short actual pants tuples have disjoint actual cusp-label pairs. -/
noncomputable section
universe u v w z
namespace WP.RandomGeometry
open WP.External
variable {P : PsiTheory} {G : WeilPeterssonGeometry.{u,v} P}
    {H : HyperbolicCurveGeometry.{u,v,w} G} (T : MulticurveTopology.{u,v,w,z} G H)
    (C : CollarGeometry G H T) {g n r : ℕ}

include C in
lemma short_pants_tuple_cut (hg : 1 ≤ g) (L : ℝ) (hL : L < 2*Real.arsinh 1)
    (X : G.Moduli g n (fun _ => 0)) (γ : Fin r → H.Primitive g n X)
    (hinj : Function.Injective γ) (hlength : ∀i, H.length (γ i) ≤ L)
    (S : Fin r → Finset (Fin n)) (hS : ∀i, H.planarSide (γ i) = some (S i))
    (hcard : ∀i, (S i).card = 2) :
    ∃o : T.Orbit g n r, T.orbitMem o X γ ∧
      ∃leaf : Fin r → Fin (T.cut o).components,
        (∀e, PantsLeafData (T.cut o) e (leaf e)) ∧
        (∀e, (T.cut o).cuspSet {leaf e} = S e) := by
  have hsimple : ∀i, H.simple (γ i) := fun i => H.planar_simple _ _ (hS i)
  have hdisjoint : ∀i j, i ≠ j → T.disjoint (γ i) (γ j) := by
    intro i j hij
    exact C.shortSimple_disjoint _ _ (hinj.ne hij) (hsimple i) (hsimple j)
      ((hlength i).trans_lt hL) ((hlength j).trans_lt hL)
  obtain ⟨o,ho,_⟩ := T.orbit_partition X γ hinj hsimple hdisjoint
  have he (i : Fin r) := planar_two_cusp_leaf_labels (T.cut o) (T.cut_stable o)
    i (S i) ((T.planarSide_iff o X γ ho hg i (S i)).1 (hS i)) (hcard i)
  choose leaf hp hlabels using he
  exact ⟨o,ho,leaf,hp,hlabels⟩

lemma pants_leaf_cusp_disjoint {n r : ℕ} (D : MulticurveCutData n r)
    (leaf : Fin r → Fin D.components) (hleaf : ∀e, PantsLeafData D e (leaf e))
    (i j : Fin r) (hij : i ≠ j) :
    Disjoint (D.cuspSet {leaf i}) (D.cuspSet {leaf j}) := by
  classical
  apply Finset.disjoint_left.mpr
  intro a hai haj
  have hi : D.cuspVertex a = leaf i := by
    simpa only [MulticurveCutData.cuspSet,Finset.mem_filter,Finset.mem_univ,
      true_and,Finset.mem_singleton] using hai
  have hj : D.cuspVertex a = leaf j := by
    simpa only [MulticurveCutData.cuspSet,Finset.mem_filter,Finset.mem_univ,
      true_and,Finset.mem_singleton] using haj
  exact hij (pantsLeaf_injective D leaf hleaf (hi.symm.trans hj))

include T C in
lemma short_pants_labels_disjoint (hg : 1 ≤ g) (L : ℝ) (hL : L < 2*Real.arsinh 1)
    (X : G.Moduli g n (fun _ => 0)) (γ δ : H.Primitive g n X)
    (hne : γ ≠ δ) (hγ : γ ∈ H.shortPlanar X 2 L) (hδ : δ ∈ H.shortPlanar X 2 L) :
    Disjoint (H.planarLabels γ) (H.planarLabels δ) := by
  classical
  obtain ⟨hlγ,S,hS,hcardS⟩ := (H.mem_shortPlanar X 2 L γ).1 hγ
  obtain ⟨hlδ,U,hU,hcardU⟩ := (H.mem_shortPlanar X 2 L δ).1 hδ
  let curves : Fin 2 → H.Primitive g n X := ![γ,δ]
  let labels : Fin 2 → Finset (Fin n) := ![S,U]
  have hinj : Function.Injective curves := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all [curves]
  have hlength : ∀i, H.length (curves i) ≤ L := by intro i; fin_cases i <;> assumption
  have hlabels : ∀i, H.planarSide (curves i) = some (labels i) := by
    intro i; fin_cases i <;> assumption
  have hcard : ∀i, (labels i).card = 2 := by intro i; fin_cases i <;> assumption
  obtain ⟨o,_,leaf,hleaf,hsides⟩ := short_pants_tuple_cut T C hg L hL X curves hinj
    hlength labels hlabels hcard
  have hd := pants_leaf_cusp_disjoint (T.cut o) leaf hleaf (0 : Fin 2) 1 (by decide)
  rw [hsides 0,hsides 1] at hd
  simpa [labels,HyperbolicCurveGeometry.planarLabels,hS,hU] using hd

include T C in
lemma short_pants_count_bound (hg : 1 ≤ g) (L : ℝ) (hL : L < 2*Real.arsinh 1)
    (X : G.Moduli g n (fun _ => 0)) :
    2*H.pantsCount X L ≤ n := by
  apply H.pantsCount_le_half_labels X L
  intro γ hγ δ hδ hne
  exact short_pants_labels_disjoint T C hg L hL X γ δ hne hγ hδ

end WP.RandomGeometry
