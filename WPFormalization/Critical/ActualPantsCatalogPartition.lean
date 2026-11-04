import WPFormalization.Critical.InternalActualClusterPartition
import WPFormalization.Critical.PantsClusterCutCatalog
import WPFormalization.RandomGeometry.PantsCutClassification
import WPFormalization.Critical.CriticalSpectrumBadEvents

/- Actual uniqueness of the nonseparating/pants alternative follows locally
from the cut embeddings, actual intrinsic pants topology, and simplicity.
Only existence of the short-support coverage is left to G3; it is an explicit
internal premise here, not an external classical field or a final paper theorem. -/
noncomputable section
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false
universe u v w z zz
namespace WP.Critical.PantsCluster
open WP.External WP.RandomGeometry WP.External.PantsCluster
open WP.External.HyperbolicPacking WP.External.ShortFillingGeometry
open WP.External.ShortBorderedLoopGeometry WP.External.PlanarJordanGeometry
open WP.External.PlanarRegionGeometry WP.External.ShortBorderedPeripheralGeometry
open MeasureTheory Set
open scoped ENNReal NNReal
variable {P : PsiTheory} {G : WeilPeterssonGeometry.{u,v} P}
  {H : HyperbolicCurveGeometry.{u,v,w} G} (A : AmbientRealization H)
  (T : MulticurveTopology.{u,v,w,z} G H) (AC : AmbientCurveCompatibility A T)
  {g n k : ℕ} {o : T.Orbit g n k} (X : G.Moduli g n (fun _ => 0))
  {κ : Fin k → H.Primitive g n X} {hκ : T.orbitMem o X κ}
  (C : CutComponentRealization A T o X κ hκ)

include AC in
lemma actual_pants_piece_nonseparating_disjoint
    (hg : 1≤g) (hκplanar : ∀e,∃S : Finset (Fin n),H.planarSide (κ e)=some S)
    (c : Fin (T.cut o).components) (hp : HasPantsTopology (C.piece c).model)
    (hb : (C.piece c).model.boundaries=1)
    (BC : PrimitiveBoundaryClassics (C.piece c).model (C.piece c).boundary)
    (LS : BorderedLoopStraighteningClassics (C.piece c).model (C.piece c).boundary)
    (J : PlanarJordanClassics) (PC : PlanarRegionClassics)
    (PP : BorderedPeripheralClassics (C.piece c).model (C.piece c).boundary)
    (j : Fin (C.piece c).model.boundaries) (γ : H.Primitive g n X)
    (hN : IsNonseparating T γ) :
    ¬actualPiecePrimitivePredicate A X (C.piece c) γ := by
  intro hγ
  have hs := (AC.simple_iff g n X γ).mp (hN.simple T)
  have he := (intrinsic_pants_simple_mem_projected_range_iff (C.piece c)
    hp hb BC LS J PC PP j (A.primitiveEquiv g n X γ) hs).mp hγ
  rw [C.boundary_eq c j] at he
  have hγκ := (A.primitiveEquiv g n X).injective he
  obtain ⟨S,hS⟩ := hκplanar (C.halfSideEquiv c j).val.1
  have hn := hN.no_planarSide T hg
  rw [hγκ,hS] at hn
  cases hn

lemma actual_pants_leaf_boundary_edge
    (leaf : Fin k → Fin (T.cut o).components)
    (hleaf : ∀e,PantsLeafData (T.cut o) e (leaf e))
    (e : Fin k) (j : Fin (C.piece (leaf e)).model.boundaries) :
    (C.halfSideEquiv (leaf e) j).val.1=e := by
  let h := C.halfSideEquiv (leaf e) j
  have hh : (T.cut o).edgeVertex (h.val.1,h.val.2)=leaf e := h.property
  apply (pantsLeaf_edge_iff (T.cut o) e (leaf e) (hleaf e) h.val.1).mp
  by_cases h0 : h.val.2=0
  · exact Or.inl (by simpa only [h0] using hh)
  · have h1 : h.val.2=1 := by
      apply Fin.ext
      have hv := h.val.2.isLt
      have hz : h.val.2.val≠0 := fun hz => h0 (Fin.ext hz)
      omega
    exact Or.inr (by simpa only [h1] using hh)

lemma actual_pants_leaf_waist_length
    (leaf : Fin k → Fin (T.cut o).components)
    (hleaf : ∀e,PantsLeafData (T.cut o) e (leaf e))
    (e : Fin k) (j : Fin (C.piece (leaf e)).model.boundaries) :
    (C.piece (leaf e)).model.curves.length ((C.piece (leaf e)).boundary.curve j)=
      H.length (κ e) := by
  have hlen := (C.piece (leaf e)).length_preserved ((C.piece (leaf e)).boundary.curve j)
  rw [C.boundary_eq,actual_pants_leaf_boundary_edge A T X C leaf hleaf,A.length_eq] at hlen
  exact hlen.symm

lemma actual_pants_leaves_boundary_edges_distinct
    (leaf : Fin k → Fin (T.cut o).components)
    (hleaf : ∀e,PantsLeafData (T.cut o) e (leaf e))
    (e f : Fin k) (hef : e≠f)
    (a : Fin (C.piece (leaf e)).model.boundaries)
    (b : Fin (C.piece (leaf f)).model.boundaries) :
    (C.halfSideEquiv (leaf e) a).val.1 ≠ (C.halfSideEquiv (leaf f) b).val.1 := by
  rw [actual_pants_leaf_boundary_edge A T X C leaf hleaf,
    actual_pants_leaf_boundary_edge A T X C leaf hleaf]
  exact hef

lemma short_simple_covered_by_actual_pants_cut
    (leaf : Fin k → Fin (T.cut o).components)
    (hleaf : ∀e,PantsLeafData (T.cut o) e (leaf e))
    (hb : ∀e,(C.piece (leaf e)).model.boundaries=1)
    (L K : ℝ) (hLK : L≤K)
    (hcomplete : ∀γ : H.Primitive g n X,γ∈H.shortPlanar X 2 K → ∃e,κ e=γ)
    (hgood : ¬HasShortSeparatingNonPants T L X)
    (γ : H.Primitive g n X) (hs : H.simple γ) (hL : H.length γ≤L) :
    IsNonseparating T γ ∨
      ∃e,actualPiecePrimitivePredicate A X (C.piece (leaf e)) γ := by
  rcases short_simple_nonseparating_or_pants_of_no_bad T L X hgood γ hs hL with hN | hp
  · exact Or.inl hN
  · obtain ⟨e,he⟩ := hcomplete γ ((H.mem_shortPlanar X 2 K γ).mpr ⟨hL.trans hLK,hp⟩)
    let j : Fin (C.piece (leaf e)).model.boundaries := ⟨0,by rw [hb e];omega⟩
    refine Or.inr ⟨e,(C.piece (leaf e)).boundary.curve j,?_⟩
    rw [C.boundary_eq,actual_pants_leaf_boundary_edge A T X C leaf hleaf,he]

lemma actual_pants_cut_coverage_of_nonsimple_coverage
    (leaf : Fin k → Fin (T.cut o).components)
    (hleaf : ∀e,PantsLeafData (T.cut o) e (leaf e))
    (hb : ∀e,(C.piece (leaf e)).model.boundaries=1)
    (L K : ℝ) (hLK : L≤K)
    (hcomplete : ∀γ : H.Primitive g n X,γ∈H.shortPlanar X 2 K → ∃e,κ e=γ)
    (hgood : ¬HasShortSeparatingNonPants T L X)
    (hnonsimple : ∀γ : H.Primitive g n X,¬H.simple γ → H.length γ≤L →
      ∃e,actualPiecePrimitivePredicate A X (C.piece (leaf e)) γ) :
    ∀γ : H.Primitive g n X,H.length γ≤L →
      IsNonseparating T γ ∨ ∃e,actualPiecePrimitivePredicate A X (C.piece (leaf e)) γ := by
  intro γ hL
  by_cases hs : H.simple γ
  · exact short_simple_covered_by_actual_pants_cut A T X C leaf hleaf hb
      L K hLK hcomplete hgood γ hs hL
  · exact Or.inr (hnonsimple γ hs hL)

variable {ι : Type zz} (pieces : ι → Fin (T.cut o).components)

lemma actual_piece_predicates_disjoint
    (hinj : Function.Injective pieces)
    (BC : ∀i,PrimitiveBoundaryClassics (C.piece (pieces i)).model
      (C.piece (pieces i)).boundary)
    (hedge : ∀i j,i≠j → ∀a : Fin (C.piece (pieces i)).model.boundaries,
      ∀b : Fin (C.piece (pieces j)).model.boundaries,
      (C.halfSideEquiv (pieces i) a).val.1 ≠ (C.halfSideEquiv (pieces j) b).val.1) :
    Pairwise (fun i j => Disjoint
      {γ : H.Primitive g n X | actualPiecePrimitivePredicate A X (C.piece (pieces i)) γ}
      {γ : H.Primitive g n X | actualPiecePrimitivePredicate A X (C.piece (pieces j)) γ}) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro γ hi hj
  exact Set.disjoint_left.mp (cutComponent_projected_ranges_disjoint A C _ _
    (hinj.ne hij) (BC i).interior_or_boundary (BC j).interior_or_boundary (hedge i j hij)) hi hj

lemma actual_cut_cluster_unique_partition_of_coverage
    (L : ℝ≥0)
    (hbg : ∀i γ,IsNonseparating T γ →
      ¬actualPiecePrimitivePredicate A X (C.piece (pieces i)) γ)
    (hpair : Pairwise (fun i j => Disjoint
      {γ : H.Primitive g n X | actualPiecePrimitivePredicate A X (C.piece (pieces i)) γ}
      {γ : H.Primitive g n X | actualPiecePrimitivePredicate A X (C.piece (pieces j)) γ}))
    (hcover : ∀γ : H.Primitive g n X,H.length γ≤L →
      IsNonseparating T γ ∨ ∃i,actualPiecePrimitivePredicate A X (C.piece (pieces i)) γ) :
    ∀γ : H.Primitive g n X,H.length γ≤L →
      ∃!i : Option ι,actualCutClusterAssignment A T X C pieces i γ := by
  intro γ hγ
  rcases hcover γ hγ with hN | ⟨i,hi⟩
  · refine ⟨none,hN,?_⟩
    intro j hj
    cases j with
    | none => rfl
    | some j => exact False.elim (hbg j γ hN hj)
  · refine ⟨some i,hi,?_⟩
    intro j hj
    cases j with
    | none => exact False.elim (hbg i γ hj hi)
    | some j =>
      congr 1
      by_contra hji
      exact Set.disjoint_left.mp (hpair hji) hj hi

include AC in
lemma actual_cut_cluster_unique_partition
    (hg : 1≤g) (hκplanar : ∀e,∃S : Finset (Fin n),H.planarSide (κ e)=some S)
    (hp : ∀i,HasPantsTopology (C.piece (pieces i)).model)
    (hb : ∀i,(C.piece (pieces i)).model.boundaries=1)
    (BC : ∀i,PrimitiveBoundaryClassics (C.piece (pieces i)).model
      (C.piece (pieces i)).boundary)
    (LS : ∀i,BorderedLoopStraighteningClassics (C.piece (pieces i)).model
      (C.piece (pieces i)).boundary)
    (J : PlanarJordanClassics) (PC : PlanarRegionClassics)
    (PP : ∀i,BorderedPeripheralClassics (C.piece (pieces i)).model
      (C.piece (pieces i)).boundary)
    (j : ∀i,Fin (C.piece (pieces i)).model.boundaries)
    (hinj : Function.Injective pieces)
    (hedge : ∀i j,i≠j → ∀a : Fin (C.piece (pieces i)).model.boundaries,
      ∀b : Fin (C.piece (pieces j)).model.boundaries,
      (C.halfSideEquiv (pieces i) a).val.1 ≠ (C.halfSideEquiv (pieces j) b).val.1)
    (L : ℝ≥0)
    (hcover : ∀γ : H.Primitive g n X,H.length γ≤L →
      IsNonseparating T γ ∨ ∃i,actualPiecePrimitivePredicate A X (C.piece (pieces i)) γ) :
    ∀γ : H.Primitive g n X,H.length γ≤L →
      ∃!i : Option ι,actualCutClusterAssignment A T X C pieces i γ := by
  apply actual_cut_cluster_unique_partition_of_coverage A T X C pieces L _ _ hcover
  · intro i γ hN
    exact actual_pants_piece_nonseparating_disjoint A T AC X C hg hκplanar
      (pieces i) (hp i) (hb i) (BC i) (LS i) J PC (PP i) (j i) γ hN
  · exact actual_piece_predicates_disjoint A T X C pieces hinj BC hedge

include AC in
lemma actual_pants_spectrum_of_nonsimple_coverage
    (F : Family.{u,w}) (U : UniquenessClassics F)
    (hg : 1≤g) (hκplanar : ∀e,∃S : Finset (Fin n),H.planarSide (κ e)=some S)
    (leaf : Fin k → Fin (T.cut o).components)
    (hleaf : ∀e,PantsLeafData (T.cut o) e (leaf e))
    (hp : ∀e,HasPantsTopology (C.piece (leaf e)).model)
    (hb : ∀e,(C.piece (leaf e)).model.boundaries=1)
    (BC : ∀e,PrimitiveBoundaryClassics (C.piece (leaf e)).model (C.piece (leaf e)).boundary)
    (LS : ∀e,BorderedLoopStraighteningClassics (C.piece (leaf e)).model (C.piece (leaf e)).boundary)
    (J : PlanarJordanClassics) (PC : PlanarRegionClassics)
    (PP : ∀e,BorderedPeripheralClassics (C.piece (leaf e)).model (C.piece (leaf e)).boundary)
    (j : ∀e,Fin (C.piece (leaf e)).model.boundaries)
    (L : ℝ≥0) (K : ℝ) (hLK : (L:ℝ)≤K)
    (hcomplete : ∀γ : H.Primitive g n X,γ∈H.shortPlanar X 2 K → ∃e,κ e=γ)
    (hgood : ¬HasShortSeparatingNonPants T L X)
    (hnonsimple : ∀γ : H.Primitive g n X,¬H.simple γ → H.length γ≤L →
      ∃e,actualPiecePrimitivePredicate A X (C.piece (leaf e)) γ) :
    (physicalPrimitiveLengthPointMeasure H X).toMeasure.restrict (Iic L) =
      ((nonseparatingLengthPointMeasure T X).toMeasure +
        Measure.sum (fun e : Fin k => measure F ⟨H.length (κ e),H.length_pos (κ e)⟩)).restrict (Iic L) := by
  have hcover := actual_pants_cut_coverage_of_nonsimple_coverage A T X C leaf hleaf hb
    L K hLK hcomplete hgood hnonsimple
  have hpart := actual_cut_cluster_unique_partition A T AC X C leaf hg hκplanar
    hp hb BC LS J PC PP j (pantsLeaf_injective (T.cut o) leaf hleaf)
    (actual_pants_leaves_boundary_edges_distinct A T X C leaf hleaf) L hcover
  have hdet := actual_finite_cluster_spectrum_of_unique_partition A T X C leaf
    F U hp hb BC j L hpart
  have he : (fun e : Fin k => measure F
        ⟨(C.piece (leaf e)).model.curves.length ((C.piece (leaf e)).boundary.curve (j e)),
          ((C.piece (leaf e)).model.curves.representative
            ((C.piece (leaf e)).boundary.curve (j e))).period_pos⟩) =
      (fun e : Fin k => measure F ⟨H.length (κ e),H.length_pos (κ e)⟩) := by
    funext e
    apply congrArg (measure F)
    apply Subtype.ext
    exact actual_pants_leaf_waist_length A T X C leaf hleaf e (j e)
  rw [he] at hdet
  exact hdet

end WP.Critical.PantsCluster
