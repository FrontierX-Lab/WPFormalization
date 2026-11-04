import WPFormalization.RandomGeometry.GeneralPlanarTuplePartition
import WPFormalization.RandomGeometry.GeneralPlanarWindowCount
import WPFormalization.RandomGeometry.PantsMixedFactorialCount

/-! Mixed falling factorials of actual short planar curves, allowing both the
planar cusp type and the length window to vary between catalog blocks. -/
noncomputable section
universe u v w
namespace WP.RandomGeometry
open WP.External
open scoped Classical ENNReal

/-- Repeat each planar cusp type once for every ordered slot of its block. -/
def expandedTypes {ι : Type*} [Fintype ι] (a : ι → ℕ) (k : ι → ℕ) :
    Fin (∑j,a j) → ℕ := fun i => k ((mixedSlotsEquiv a).symm i).1

variable {P : PsiTheory} {G : WeilPeterssonGeometry.{u,v} P}
    (H : HyperbolicCurveGeometry.{u,v,w} G) {g n : ℕ}

/-- The actual finite catalog of planar curves of one cusp type in a length
window. No geometric moment or asymptotic estimate is assumed. -/
def generalPlanarWindowCatalog (X : G.Moduli g n (fun _ => 0))
    (k : ℕ) (L : ℝ) (I : Set ℝ) : Finset (H.Primitive g n X) :=
  (H.shortPlanar X k L).filter (fun γ => H.length γ ∈ I)

lemma shortPlanar_different_type_disjoint (X : G.Moduli g n (fun _ => 0))
    (k l : ℕ) (hk : k≠l) (L M : ℝ) :
    Disjoint (H.shortPlanar X k L) (H.shortPlanar X l M) := by
  apply Finset.disjoint_left.mpr
  intro γ hkγ hlγ
  exact hk ((H.planarLabels_card γ k L hkγ).symm.trans (H.planarLabels_card γ l M hlγ))

/-- Different types have disjoint catalogs regardless of overlapping length
windows; for an equal type, disjoint length windows suffice. -/
lemma generalPlanarWindowCatalog_disjoint {ι : Type*}
    (X : G.Moduli g n (fun _ => 0)) (k : ι → ℕ) (L : ℝ) (I : ι → Set ℝ)
    (hdis : Pairwise (fun j l => k j≠k l ∨ Disjoint (I j) (I l))) :
    Pairwise (fun j l => Disjoint (generalPlanarWindowCatalog H X (k j) L (I j))
      (generalPlanarWindowCatalog H X (k l) L (I l))) := by
  intro j l hjl
  apply Finset.disjoint_left.mpr
  intro γ hj hl
  rcases Finset.mem_filter.mp hj with ⟨hjt,hjw⟩
  rcases Finset.mem_filter.mp hl with ⟨hlt,hlw⟩
  rcases hdis hjl with htype|hwin
  · exact Finset.disjoint_left.mp (shortPlanar_different_type_disjoint H X _ _ htype L L) hjt hlt
  · exact Set.disjoint_left.mp hwin hjw hlw

/-- Reindex the actual catalog tuple by an arbitrary enumeration of its slots.
The edge order is preserved by that enumeration, without a factorial factor. -/
def generalPlanarWindowCatalogTupleEquiv {ι : Type*}
    (X : G.Moduli g n (fun _ => 0)) (k : ι → ℕ) (L : ℝ) (I : ι → Set ℝ)
    (a : ι → ℕ) (R : ℕ) (e : (Σj,Fin (a j)) ≃ Fin R) :
    CatalogTuple (fun j => generalPlanarWindowCatalog H X (k j) L (I j)) a ≃
      {γ : OrderedGeneralPlanarTuple (H:=H) X (fun i => k (e.symm i).1) L //
        ∀i,H.length (γ.val i) ∈ I (e.symm i).1} where
  toFun t := ⟨⟨fun i => t.val (e.symm i),
    t.property.1.comp e.symm.injective,
    fun i => (Finset.mem_filter.mp (t.property.2 (e.symm i))).1⟩,
    fun i => (Finset.mem_filter.mp (t.property.2 (e.symm i))).2⟩
  invFun t := ⟨fun s => t.val.val (e s),
    t.val.property.1.comp e.injective,fun s => by
      apply Finset.mem_filter.mpr
      constructor
      · simpa using t.val.property.2 (e s)
      · simpa using t.property (e s)⟩
  left_inv t := by
    apply Subtype.ext
    funext s
    exact congrArg t.val (e.symm_apply_apply s)
  right_inv t := by
    apply Subtype.ext
    apply Subtype.ext
    funext i
    exact congrArg t.val.val (e.apply_symm_apply i)

lemma generalPlanarWindowCount_mixed_catalogs {ι : Type*} [Fintype ι]
    (X : G.Moduli g n (fun _ => 0)) (k : ι → ℕ) (L : ℝ) (I : ι → Set ℝ)
    (a : ι → ℕ) (hdis : Pairwise (fun j l => k j≠k l ∨ Disjoint (I j) (I l)))
    (R : ℕ) (e : (Σj,Fin (a j)) ≃ Fin R) :
    generalPlanarWindowCount H X (fun i => k (e.symm i).1) L (fun i => I (e.symm i).1) =
      ∏j,(generalPlanarWindowCatalog H X (k j) L (I j)).card.descFactorial (a j) := by
  unfold generalPlanarWindowCount
  rw [← Nat.card_congr (generalPlanarWindowCatalogTupleEquiv H X k L I a R e)]
  exact catalogTuple_card _ a (generalPlanarWindowCatalog_disjoint H X k L I hdis)

/-- The literal one-slot count is exactly the cardinal of its actual catalog. -/
def generalPlanarWindowCatalogEquivSingleton (X : G.Moduli g n (fun _ => 0))
    (k : ℕ) (L : ℝ) (I : Set ℝ) :
    {γ // γ ∈ generalPlanarWindowCatalog H X k L I} ≃
      {t : OrderedGeneralPlanarTuple (H:=H) X (fun _ : Fin 1 => k) L //
        ∀i,H.length (t.val i) ∈ I} where
  toFun γ := ⟨⟨fun _ => γ.val,Function.injective_of_subsingleton _,
    fun _ => (Finset.mem_filter.mp γ.property).1⟩,
    fun _ => (Finset.mem_filter.mp γ.property).2⟩
  invFun t := ⟨t.val.val 0,Finset.mem_filter.mpr ⟨t.val.property.2 0,t.property 0⟩⟩
  left_inv _ := rfl
  right_inv t := by
    apply Subtype.ext
    apply Subtype.ext
    funext i
    have hi : i=(0 : Fin 1) := Subsingleton.elim _ _
    subst i
    rfl

lemma generalPlanarWindowCatalog_card (X : G.Moduli g n (fun _ => 0))
    (k : ℕ) (L : ℝ) (I : Set ℝ) :
    (generalPlanarWindowCatalog H X k L I).card =
      generalPlanarWindowCount H X (fun _ : Fin 1 => k) L (fun _ => I) := by
  calc
    _ = Nat.card {γ // γ ∈ generalPlanarWindowCatalog H X k L I} := by
      simp only [Nat.card_eq_fintype_card,Fintype.card_coe]
    _ = _ := Nat.card_congr (generalPlanarWindowCatalogEquivSingleton H X k L I)

/-- Actual mixed falling factorials equal the globally distinct actual typed
window count for every enumeration of the ordered blocks. -/
lemma generalPlanar_mixed_factorial_eq_windowCount {ι : Type*} [Fintype ι]
    (X : G.Moduli g n (fun _ => 0)) (k : ι → ℕ) (L : ℝ) (I : ι → Set ℝ)
    (a : ι → ℕ) (hdis : Pairwise (fun j l => k j≠k l ∨ Disjoint (I j) (I l)))
    (R : ℕ) (e : (Σj,Fin (a j)) ≃ Fin R) :
    (∏j,(generalPlanarWindowCount H X (fun _ : Fin 1 => k j) L
      (fun _ => I j)).descFactorial (a j)) =
      generalPlanarWindowCount H X (fun i => k (e.symm i).1) L (fun i => I (e.symm i).1) := by
  rw [generalPlanarWindowCount_mixed_catalogs H X k L I a hdis R e]
  simp_rw [generalPlanarWindowCatalog_card]

/-- Canonical expanded-slot version; empty index sets, zero blocks and total
order zero are included, with no multinomial or ordering factor. -/
lemma generalPlanar_mixed_factorial_eq_expandedWindowCount {ι : Type*} [Fintype ι]
    (X : G.Moduli g n (fun _ => 0)) (k : ι → ℕ) (L : ℝ) (I : ι → Set ℝ)
    (a : ι → ℕ) (hdis : Pairwise (fun j l => k j≠k l ∨ Disjoint (I j) (I l))) :
    (∏j,(generalPlanarWindowCount H X (fun _ : Fin 1 => k j) L
      (fun _ => I j)).descFactorial (a j)) =
      generalPlanarWindowCount H X (expandedTypes a k) L (expandedWindows a I) :=
  generalPlanar_mixed_factorial_eq_windowCount H X k L I a hdis _ (mixedSlotsEquiv a)

lemma generalPlanar_mixed_factorial_eq_expandedWindowCount_real {ι : Type*} [Fintype ι]
    (X : G.Moduli g n (fun _ => 0)) (k : ι → ℕ) (L : ℝ) (I : ι → Set ℝ)
    (a : ι → ℕ) (hdis : Pairwise (fun j l => k j≠k l ∨ Disjoint (I j) (I l))) :
    (∏j,((generalPlanarWindowCount H X (fun _ : Fin 1 => k j) L
      (fun _ => I j)).descFactorial (a j) : ℝ)) =
      (generalPlanarWindowCount H X (expandedTypes a k) L (expandedWindows a I) : ℝ) := by
  rw [← Nat.cast_prod,generalPlanar_mixed_factorial_eq_expandedWindowCount H X k L I a hdis]

lemma generalPlanar_mixed_factorial_eq_expandedWindowCount_ennreal {ι : Type*} [Fintype ι]
    (X : G.Moduli g n (fun _ => 0)) (k : ι → ℕ) (L : ℝ) (I : ι → Set ℝ)
    (a : ι → ℕ) (hdis : Pairwise (fun j l => k j≠k l ∨ Disjoint (I j) (I l))) :
    (∏j,((generalPlanarWindowCount H X (fun _ : Fin 1 => k j) L
      (fun _ => I j)).descFactorial (a j) : ℝ≥0∞)) =
      (generalPlanarWindowCount H X (expandedTypes a k) L (expandedWindows a I) : ℝ≥0∞) := by
  rw [← Nat.cast_prod,generalPlanar_mixed_factorial_eq_expandedWindowCount H X k L I a hdis]

end WP.RandomGeometry
