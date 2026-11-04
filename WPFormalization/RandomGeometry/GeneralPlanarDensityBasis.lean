import WPFormalization.RandomGeometry.GeneralPlanarDensityIntensity
import WPFormalization.Probability.NNRealWindowBasis

noncomputable section
namespace WP.RandomGeometry
open Set Filter MeasureTheory WP.Probability
open scoped Topology ENNReal NNReal Classical

/-- A genuine bounded length window carrying its original integer cusp type. -/
def generalPlanarTypeWindow (k : ℕ) (B : RelCompactBorelWindow ℝ≥0) :
    RelCompactBorelWindow (ℝ≥0 × ℕ) where
  carrier := B.carrier ×ˢ {k}
  measurableSet := B.measurableSet.prod (measurableSet_singleton k)
  compactClosure := by
    rw [closure_prod_eq,closure_singleton]
    exact B.compactClosure.prod isCompact_singleton

lemma general_planar_type_window_disjoint_iff (k l : ℕ)
    (A B : RelCompactBorelWindow ℝ≥0) :
    Disjoint (generalPlanarTypeWindow k A).carrier (generalPlanarTypeWindow l B).carrier ↔
      (k=l → Disjoint A.carrier B.carrier) := by
  constructor
  · intro hd heq
    subst l
    apply Set.disjoint_left.mpr
    intro x hA hB
    exact Set.disjoint_left.mp hd
      (show (x,k) ∈ (generalPlanarTypeWindow k A).carrier from ⟨hA,rfl⟩)
      (show (x,k) ∈ (generalPlanarTypeWindow k B).carrier from ⟨hB,rfl⟩)
  · intro hd
    apply Set.disjoint_left.mpr
    intro x hA hB
    exact Set.disjoint_left.mp (hd (hA.2.symm.trans hB.2)) hA.1 hB.1

def generalPlanarRationalWindows : Set (RelCompactBorelWindow (ℝ≥0 × ℕ)) :=
  range (fun z : ℕ × (ℚ × ℚ) => generalPlanarTypeWindow z.1 (nnrealRationalWindow z.2.1 z.2.2))

lemma general_planar_type_window_mem (k : ℕ) (B : RelCompactBorelWindow ℝ≥0)
    (hB : B ∈ nnrealRationalWindows) :
    generalPlanarTypeWindow k B ∈ generalPlanarRationalWindows := by
  obtain ⟨⟨a,b⟩,rfl⟩ := hB
  exact ⟨(k,a,b),rfl⟩

lemma general_planar_type_window_union (k : ℕ) (F : Finset (RelCompactBorelWindow ℝ≥0)) :
    (⋃ B ∈ F.image (generalPlanarTypeWindow k),B.carrier) =
      (⋃ B ∈ F,B.carrier) ×ˢ {k} := by
  ext x
  simp only [mem_iUnion,Finset.mem_image,mem_prod,mem_singleton_iff]
  constructor
  · rintro ⟨B,⟨A,hAF,rfl⟩,hx⟩
    exact ⟨⟨A,hAF,hx.1⟩,hx.2⟩
  · rintro ⟨⟨A,hAF,hx⟩,hk⟩
    exact ⟨generalPlanarTypeWindow k A,⟨A,hAF,rfl⟩,hx,hk⟩

lemma general_planar_type_window_difference (k : ℕ)
    (A B : RelCompactBorelWindow ℝ≥0)
    (hA : A ∈ nnrealRationalWindows) (hB : B ∈ nnrealRationalWindows) :
    ∃ F : Finset (RelCompactBorelWindow (ℝ≥0 × ℕ)),
      (∀ C ∈ F,C ∈ generalPlanarRationalWindows) ∧
      (∀ C ∈ F,∀ D ∈ F,C ≠ D → Disjoint C.carrier D.carrier) ∧
      (⋃ C ∈ F,C.carrier)=(generalPlanarTypeWindow k A).carrier \ (generalPlanarTypeWindow k B).carrier := by
  obtain ⟨F,hF,hd,hU⟩ := (nnrealRationalWindows_basis quadraticLengthIntensity).difference A hA B hB
  refine ⟨F.image (generalPlanarTypeWindow k),?_,?_,?_⟩
  · intro C hC
    obtain ⟨C,hCF,rfl⟩ := Finset.mem_image.mp hC
    exact general_planar_type_window_mem k C (hF C hCF)
  · intro C hC D hD hne
    obtain ⟨C,hCF,rfl⟩ := Finset.mem_image.mp hC
    obtain ⟨D,hDF,rfl⟩ := Finset.mem_image.mp hD
    apply (general_planar_type_window_disjoint_iff k k C D).mpr
    intro _
    exact hd C hCF D hDF (fun h => hne (h ▸ rfl))
  · rw [general_planar_type_window_union,hU]
    ext x
    simp only [generalPlanarTypeWindow,mem_prod,Set.mem_sdiff,mem_singleton_iff]
    tauto

lemma general_planar_rational_window_continuity (P : PsiTheory) (l : ℝ≥0∞)
    (k : ℕ) (a b : ℚ) :
    generalPlanarDensityIntensity P l
      (frontier (generalPlanarTypeWindow k (nnrealRationalWindow a b)).carrier) = 0 := by
  have hf : frontier ({k} : Set ℕ) = ∅ := by
    rw [frontier,closure_singleton,(isOpen_discrete ({k}:Set ℕ)).interior_eq,sdiff_self]
  change generalPlanarDensityIntensity P l
    (frontier ((nnrealRationalWindow a b).carrier ×ˢ {k})) = 0
  rw [frontier_prod_eq,hf,prod_empty,empty_union,closure_singleton,
    general_planar_density_intensity_rect,nnrealRationalWindow_continuity quadraticLengthIntensity]
  exact zero_mul _

lemma exists_general_planar_rational_window (U : Set (ℝ≥0 × ℕ)) (hU : IsOpen U)
    (x : ℝ≥0 × ℕ) (hx : x ∈ U) :
    ∃ k : ℕ,∃ a b : ℚ,
      x ∈ interior (generalPlanarTypeWindow k (nnrealRationalWindow a b)).carrier ∧
      (generalPlanarTypeWindow k (nnrealRationalWindow a b)).carrier ⊆ U := by
  let V : Set ℝ≥0 := (fun y => (y,x.2)) ⁻¹' U
  have hV : IsOpen V := hU.preimage (continuous_id.prodMk continuous_const)
  obtain ⟨a,b,hxi,hsub⟩ := exists_nnrealRationalWindow V hV x.1 hx
  refine ⟨x.2,a,b,?_,?_⟩
  · change x ∈ interior ((nnrealRationalWindow a b).carrier ×ˢ {x.2})
    rw [interior_prod_eq,(isOpen_discrete ({x.2}:Set ℕ)).interior_eq]
    exact ⟨hxi,rfl⟩
  · rintro ⟨y,k⟩ ⟨hy,hk⟩
    have heq : k=x.2 := hk
    subst k
    exact hsub hy

lemma general_planar_rational_windows_localApproximation
    (K U : Set (ℝ≥0 × ℕ)) (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ F : Finset (RelCompactBorelWindow (ℝ≥0 × ℕ)),
      (∀ B ∈ F,B ∈ generalPlanarRationalWindows) ∧
      K ⊆ interior (⋃ B ∈ F,B.carrier) ∧ (⋃ B ∈ F,B.carrier) ⊆ U := by
  let I := {z : ℕ × (ℚ × ℚ) //
    (generalPlanarTypeWindow z.1 (nnrealRationalWindow z.2.1 z.2.2)).carrier ⊆ U}
  let W : I → RelCompactBorelWindow (ℝ≥0 × ℕ) :=
    fun i => generalPlanarTypeWindow i.val.1 (nnrealRationalWindow i.val.2.1 i.val.2.2)
  have hcover : K ⊆ ⋃ i : I,interior (W i).carrier := by
    intro x hx
    obtain ⟨k,a,b,hxi,hsub⟩ := exists_general_planar_rational_window U hU x (hKU hx)
    exact mem_iUnion.mpr ⟨⟨(k,a,b),hsub⟩,hxi⟩
  obtain ⟨t,ht⟩ := hK.elim_finite_subcover
    (fun i : I => interior (W i).carrier) (fun _ => isOpen_interior) hcover
  refine ⟨t.image W,?_,?_,?_⟩
  · intro B hB
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hB
    exact ⟨i.val,rfl⟩
  · intro x hx
    obtain ⟨i,hi,hxi⟩ := mem_iUnion₂.mp (ht hx)
    exact interior_mono (subset_biUnion_of_mem (Finset.mem_image.mpr ⟨i,hi,rfl⟩)) hxi
  · intro x hx
    obtain ⟨B,hB,hxB⟩ := mem_iUnion₂.mp hx
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hB
    exact i.property hxB

theorem general_planar_rational_windows_basis (P : PsiTheory) (l : ℝ≥0∞) :
    ContinuityWindowBasis (ℝ≥0 × ℕ) (generalPlanarDensityIntensity P l)
      generalPlanarRationalWindows := by
  refine ⟨countable_range _,?_,?_,?_,?_,general_planar_rational_windows_localApproximation⟩
  · refine ⟨generalPlanarTypeWindow 0 (nnrealRationalWindow 0 0),⟨(0,0,0),rfl⟩,?_⟩
    simp [generalPlanarTypeWindow,nnrealRationalWindow_empty]
  · rintro A ⟨⟨k,a,b⟩,rfl⟩ B ⟨⟨l,c,d⟩,rfl⟩
    by_cases hkl : k=l
    · subst l
      refine ⟨generalPlanarTypeWindow k (nnrealRationalWindow (max a c) (min b d)),
        ⟨(k,max a c,min b d),rfl⟩,?_⟩
      rw [show (generalPlanarTypeWindow k (nnrealRationalWindow (max a c) (min b d))).carrier =
        (nnrealRationalWindow (max a c) (min b d)).carrier ×ˢ {k} by rfl,
        nnrealRationalWindow_inter]
      ext x
      simp only [generalPlanarTypeWindow,mem_prod,mem_inter_iff,mem_singleton_iff]
      tauto
    · refine ⟨generalPlanarTypeWindow 0 (nnrealRationalWindow 0 0),⟨(0,0,0),rfl⟩,?_⟩
      rw [((general_planar_type_window_disjoint_iff k l _ _).mpr (fun h => (hkl h).elim)).inter_eq]
      simp [generalPlanarTypeWindow,nnrealRationalWindow_empty]
  · rintro A ⟨⟨k,a,b⟩,rfl⟩ B ⟨⟨l,c,d⟩,rfl⟩
    by_cases hkl : k=l
    · subst l
      exact general_planar_type_window_difference k _ _ ⟨(a,b),rfl⟩ ⟨(c,d),rfl⟩
    · refine ⟨{generalPlanarTypeWindow k (nnrealRationalWindow a b)},?_,?_,?_⟩
      · intro C hC
        obtain rfl := Finset.mem_singleton.mp hC
        exact ⟨(k,a,b),rfl⟩
      · intro C hC D hD hne
        exact (hne ((Finset.mem_singleton.mp hC).trans (Finset.mem_singleton.mp hD).symm)).elim
      · rw [sdiff_eq_left.mpr ((general_planar_type_window_disjoint_iff k l _ _).mpr (fun h => (hkl h).elim))]
        simp
  · rintro B ⟨⟨k,a,b⟩,rfl⟩
    exact general_planar_rational_window_continuity P l k a b

end WP.RandomGeometry
