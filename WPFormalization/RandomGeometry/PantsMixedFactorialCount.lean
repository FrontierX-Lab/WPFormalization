import WPFormalization.RandomGeometry.PantsWindowCount

/-! Finite mixed factorial counts for disjoint actual length windows. -/
noncomputable section
universe u v w
namespace WP.RandomGeometry
open WP.External
open scoped Classical ENNReal

/-- One globally distinct tuple, with its slots grouped into catalog blocks. -/
def CatalogTuple {ι α : Type*} (F : ι → Finset α) (a : ι → ℕ) :=
  {γ : (Σ j, Fin (a j)) → α // Function.Injective γ ∧ ∀ s, γ s ∈ F s.1}

/-- Pairwise disjoint catalogs make global distinctness exactly equivalent to
choosing an injection independently in each block. -/
def catalogTupleEquiv {ι α : Type*} (F : ι → Finset α) (a : ι → ℕ)
    (hF : Pairwise (fun j k => Disjoint (F j) (F k))) :
    (∀ j, Fin (a j) ↪ {x // x ∈ F j}) ≃ CatalogTuple F a where
  toFun e := ⟨fun s => (e s.1 s.2).val, by
    constructor
    · rintro ⟨j,i⟩ ⟨k,l⟩ h
      change (e j i).val = (e k l).val at h
      by_cases hjk : j=k
      · subst k
        have hi := (e j).injective (Subtype.ext h)
        exact congrArg (Sigma.mk j) hi
      · exact False.elim ((Finset.disjoint_left.mp (hF hjk))
          (e j i).property (h.symm ▸ (e k l).property))
    · intro s
      exact (e s.1 s.2).property⟩
  invFun t j :=
    { toFun := fun i => ⟨t.val ⟨j,i⟩, t.property.2 ⟨j,i⟩⟩
      inj' := fun i k h => by
        have hs := t.property.1 (congrArg Subtype.val h)
        exact eq_of_heq (Sigma.mk.inj_iff.mp hs).2 }
  left_inv e := by
    funext j
    apply Function.Embedding.ext
    intro i
    rfl
  right_inv t := by
    apply Subtype.ext
    funext s
    cases s
    rfl

theorem catalogTuple_card {ι α : Type*} [Fintype ι]
    (F : ι → Finset α) (a : ι → ℕ)
    (hF : Pairwise (fun j k => Disjoint (F j) (F k))) :
    Nat.card (CatalogTuple F a) = ∏ j, (F j).card.descFactorial (a j) := by
  rw [← Nat.card_congr (catalogTupleEquiv F a hF), Nat.card_pi]
  apply Finset.prod_congr rfl
  intro j _
  rw [Nat.card_eq_fintype_card, Fintype.card_embedding_eq,
    Fintype.card_coe, Fintype.card_fin]

/-- A fixed enumeration of the union of the ordered blocks. -/
def mixedSlotsEquiv {ι : Type*} [Fintype ι] (a : ι → ℕ) :
    (Σ j, Fin (a j)) ≃ Fin (∑ j, a j) :=
  (Fintype.equivFin _).trans (finCongr (by simp [Fintype.card_sigma]))

/-- Repeat the j-th window once for each of its a_j ordered slots. -/
def expandedWindows {ι : Type*} [Fintype ι] (a : ι → ℕ) (I : ι → Set ℝ) :
    Fin (∑ j, a j) → Set ℝ := fun i => I ((mixedSlotsEquiv a).symm i).1

/-- Products over expanded slots regroup without a multinomial factor. -/
theorem mixedSlots_prod {ι M : Type*} [Fintype ι] [CommMonoid M]
    (a : ι → ℕ) (R : ℕ) (e : (Σ j, Fin (a j)) ≃ Fin R) (w : ι → M) :
    (∏ i : Fin R, w (e.symm i).1) = ∏ j, (w j)^(a j) := by
  calc
    _ = ∏ s : (Σ j, Fin (a j)), w s.1 := e.symm.prod_comp (fun s => w s.1)
    _ = _ := by rw [Fintype.prod_sigma]; simp

variable {P : PsiTheory} {G : WeilPeterssonGeometry.{u,v} P}
    (H : HyperbolicCurveGeometry.{u,v,w} G) {g n : ℕ}

/-- The actual finite catalog of short pants curves in one length window. -/
def pantsWindowCatalog (X : G.Moduli g n (fun _ => 0)) (L : ℝ) (I : Set ℝ) :
    Finset (H.Primitive g n X) :=
  (H.shortPlanar X 2 L).filter (fun γ => H.length γ ∈ I)

lemma pantsWindowCatalog_disjoint {ι : Type*} (X : G.Moduli g n (fun _ => 0))
    (L : ℝ) (I : ι → Set ℝ) (hI : Pairwise (fun j k => Disjoint (I j) (I k))) :
    Pairwise (fun j k => Disjoint (pantsWindowCatalog H X L (I j))
      (pantsWindowCatalog H X L (I k))) := by
  intro j k hjk
  apply Finset.disjoint_left.mpr
  intro γ hγ hδ
  exact Set.disjoint_left.mp (hI hjk) (Finset.mem_filter.mp hγ).2
    (Finset.mem_filter.mp hδ).2

/-- Reindex the block tuple by any finite-slot bijection; no choice of ordering
of blocks changes the resulting window count. -/
def pantsWindowCatalogTupleEquiv {ι : Type*} (X : G.Moduli g n (fun _ => 0))
    (L : ℝ) (I : ι → Set ℝ) (a : ι → ℕ) (R : ℕ)
    (e : (Σ j, Fin (a j)) ≃ Fin R) :
    CatalogTuple (fun j => pantsWindowCatalog H X L (I j)) a ≃
      {γ : H.OrderedPlanarTuple X 2 L R //
        ∀ i, H.length (γ.val i) ∈ I (e.symm i).1} where
  toFun t := ⟨⟨fun i => t.val (e.symm i),
    t.property.1.comp e.symm.injective,
    fun i => (Finset.mem_filter.mp (t.property.2 (e.symm i))).1⟩,
    fun i => (Finset.mem_filter.mp (t.property.2 (e.symm i))).2⟩
  invFun t := ⟨fun s => t.val.val (e s),
    t.val.property.1.comp e.injective, fun s => by
      apply Finset.mem_filter.mpr
      exact ⟨t.val.property.2 (e s), by simpa using t.property (e s)⟩⟩
  left_inv t := by
    apply Subtype.ext
    funext s
    exact congrArg t.val (e.symm_apply_apply s)
  right_inv t := by
    apply Subtype.ext
    apply Subtype.ext
    funext i
    exact congrArg t.val.val (e.apply_symm_apply i)

theorem pantsWindowCount_mixed_catalogs {ι : Type*} [Fintype ι]
    (X : G.Moduli g n (fun _ => 0)) (L : ℝ) (I : ι → Set ℝ) (a : ι → ℕ)
    (hI : Pairwise (fun j k => Disjoint (I j) (I k))) (R : ℕ)
    (e : (Σ j, Fin (a j)) ≃ Fin R) :
    pantsWindowCount H X L (fun i => I (e.symm i).1) =
      ∏ j, (pantsWindowCatalog H X L (I j)).card.descFactorial (a j) := by
  unfold pantsWindowCount
  rw [← Nat.card_congr (pantsWindowCatalogTupleEquiv H X L I a R e)]
  exact catalogTuple_card _ a (pantsWindowCatalog_disjoint H X L I hI)

/-- The catalog cardinal is the literal one-slot actual window count. -/
def pantsWindowCatalogEquivSingleton (X : G.Moduli g n (fun _ => 0))
    (L : ℝ) (I : Set ℝ) :
    {γ // γ ∈ pantsWindowCatalog H X L I} ≃
      {t : H.OrderedPlanarTuple X 2 L 1 // ∀ i, H.length (t.val i) ∈ I} where
  toFun γ := ⟨⟨fun _ => γ.val, Function.injective_of_subsingleton _,
    fun _ => (Finset.mem_filter.mp γ.property).1⟩,
    fun _ => (Finset.mem_filter.mp γ.property).2⟩
  invFun t := ⟨t.val.val 0,
    Finset.mem_filter.mpr ⟨t.val.property.2 0, t.property 0⟩⟩
  left_inv _ := rfl
  right_inv t := by
    apply Subtype.ext
    apply Subtype.ext
    funext i
    have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
    subst i
    rfl

theorem pantsWindowCatalog_card (X : G.Moduli g n (fun _ => 0))
    (L : ℝ) (I : Set ℝ) :
    (pantsWindowCatalog H X L I).card =
      pantsWindowCount H X L (fun _ : Fin 1 => I) := by
  calc
    _ = Nat.card {γ // γ ∈ pantsWindowCatalog H X L I} := by
      simp only [Nat.card_eq_fintype_card, Fintype.card_coe]
    _ = _ := Nat.card_congr (pantsWindowCatalogEquivSingleton H X L I)

/-- Actual mixed falling-factorial counts equal the actual globally distinct
window count, for any chosen enumeration of the ordered blocks. -/
theorem pants_mixed_factorial_eq_windowCount {ι : Type*} [Fintype ι]
    (X : G.Moduli g n (fun _ => 0)) (L : ℝ) (I : ι → Set ℝ) (a : ι → ℕ)
    (hI : Pairwise (fun j k => Disjoint (I j) (I k))) (R : ℕ)
    (e : (Σ j, Fin (a j)) ≃ Fin R) :
    (∏ j, (pantsWindowCount H X L (fun _ : Fin 1 => I j)).descFactorial (a j)) =
      pantsWindowCount H X L (fun i => I (e.symm i).1) := by
  rw [pantsWindowCount_mixed_catalogs H X L I a hI R e]
  simp_rw [pantsWindowCatalog_card]

/-- Canonical-slot version, including zero blocks and the empty multiindex. -/
theorem pants_mixed_factorial_eq_expandedWindowCount {ι : Type*} [Fintype ι]
    (X : G.Moduli g n (fun _ => 0)) (L : ℝ) (I : ι → Set ℝ) (a : ι → ℕ)
    (hI : Pairwise (fun j k => Disjoint (I j) (I k))) :
    (∏ j, (pantsWindowCount H X L (fun _ : Fin 1 => I j)).descFactorial (a j)) =
      pantsWindowCount H X L (expandedWindows a I) :=
  pants_mixed_factorial_eq_windowCount H X L I a hI _ (mixedSlotsEquiv a)

theorem pants_mixed_factorial_eq_expandedWindowCount_real {ι : Type*} [Fintype ι]
    (X : G.Moduli g n (fun _ => 0)) (L : ℝ) (I : ι → Set ℝ) (a : ι → ℕ)
    (hI : Pairwise (fun j k => Disjoint (I j) (I k))) :
    (∏ j, ((pantsWindowCount H X L (fun _ : Fin 1 => I j)).descFactorial (a j) : ℝ)) =
      (pantsWindowCount H X L (expandedWindows a I) : ℝ) := by
  rw [← Nat.cast_prod, pants_mixed_factorial_eq_expandedWindowCount H X L I a hI]

theorem pants_mixed_factorial_eq_expandedWindowCount_ennreal {ι : Type*} [Fintype ι]
    (X : G.Moduli g n (fun _ => 0)) (L : ℝ) (I : ι → Set ℝ) (a : ι → ℕ)
    (hI : Pairwise (fun j k => Disjoint (I j) (I k))) :
    (∏ j, ((pantsWindowCount H X L (fun _ : Fin 1 => I j)).descFactorial (a j) : ℝ≥0∞)) =
      (pantsWindowCount H X L (expandedWindows a I) : ℝ≥0∞) := by
  rw [← Nat.cast_prod, pants_mixed_factorial_eq_expandedWindowCount H X L I a hI]

end WP.RandomGeometry
