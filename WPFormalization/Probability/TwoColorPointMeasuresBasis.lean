import WPFormalization.Probability.TwoColorPointMeasuresTopology

/-! The two clopen copies of the already proved half-line continuity semiring. -/
noncomputable section
namespace WP.Probability
open MeasureTheory Filter Set Topology
open scoped Topology CompactlySupported ENNReal NNReal Classical

def twoColorWindow (b : Bool) (B : RelCompactBorelWindow ℝ≥0) : RelCompactBorelWindow TwoColorSpace :=
  if b then twoColorRightWindow B else twoColorLeftWindow B

def twoColorInjection (b : Bool) : ℝ≥0 → TwoColorSpace := if b then Sum.inr else Sum.inl

lemma twoColorInjection_injective (b : Bool) : Function.Injective (twoColorInjection b) := by
  cases b <;> exact (by first | exact Sum.inl_injective | exact Sum.inr_injective)

lemma twoColorWindow_carrier (b : Bool) (B : RelCompactBorelWindow ℝ≥0) :
    (twoColorWindow b B).carrier=twoColorInjection b '' B.carrier := by cases b <;> rfl

lemma twoColorInjection_continuous (b : Bool) : Continuous (twoColorInjection b) := by
  cases b <;> first | exact continuous_inl | exact continuous_inr

lemma twoColorInjection_openEmbedding (b : Bool) : IsOpenEmbedding (twoColorInjection b) := by
  cases b <;> first | exact IsOpenEmbedding.inl | exact IsOpenEmbedding.inr

lemma twoColorInjection_closedEmbedding (b : Bool) : IsClosedEmbedding (twoColorInjection b) := by
  cases b <;> first | exact IsClosedEmbedding.inl | exact IsClosedEmbedding.inr

lemma twoColorWindow_disjoint (b : Bool) (A B : RelCompactBorelWindow ℝ≥0)
    (h : Disjoint A.carrier B.carrier) :
    Disjoint (twoColorWindow b A).carrier (twoColorWindow b B).carrier := by
  rw [twoColorWindow_carrier,twoColorWindow_carrier]
  exact (Set.disjoint_image_iff (twoColorInjection_injective b)).mpr h

lemma twoColorWindow_disjoint_iff (a b : Bool) (A B : RelCompactBorelWindow ℝ≥0) :
    Disjoint (twoColorWindow a A).carrier (twoColorWindow b B).carrier ↔
      (a=b → Disjoint A.carrier B.carrier) := by
  by_cases hab : a=b
  · subst b
    rw [twoColorWindow_carrier,twoColorWindow_carrier,
      Set.disjoint_image_iff (twoColorInjection_injective a)]
    simp
  · have hb : b = !a := by cases a <;> cases b <;> simp_all
    constructor
    · intro h hsame;exact (hab hsame).elim
    · intro h
      rw [hb]
      cases a <;> apply Set.disjoint_left.mpr
      all_goals intro z hz hz'; rcases hz with ⟨x,hx,rfl⟩; rcases hz' with ⟨y,hy,hxy⟩; cases hxy

lemma twoColorWindow_cross_disjoint (b : Bool) (A B : RelCompactBorelWindow ℝ≥0) :
    Disjoint (twoColorWindow b A).carrier (twoColorWindow (!b) B).carrier := by
  cases b <;> simp only [twoColorWindow,Bool.false_eq_true,if_false,if_true,Bool.not_false,Bool.not_true,
    twoColorLeftWindow,twoColorRightWindow]
  all_goals apply Set.disjoint_left.mpr; intro z hz hz'; rcases hz with ⟨x,hx,rfl⟩; rcases hz' with ⟨y,hy,hxy⟩; cases hxy

lemma twoColorWindow_union (b : Bool) (F : Finset (RelCompactBorelWindow ℝ≥0)) :
    (⋃ B ∈ F.image (twoColorWindow b),B.carrier)=twoColorInjection b '' (⋃ A ∈ F,A.carrier) := by
  ext z
  constructor
  · intro hz
    obtain ⟨B,hB,hzB⟩ := mem_iUnion₂.mp hz
    obtain ⟨A,hA,rfl⟩ := Finset.mem_image.mp hB
    rw [twoColorWindow_carrier] at hzB
    obtain ⟨x,hx,rfl⟩ := hzB
    exact ⟨x,mem_iUnion₂.mpr ⟨A,hA,hx⟩,rfl⟩
  · rintro ⟨x,hx,rfl⟩
    obtain ⟨A,hA,hxA⟩ := mem_iUnion₂.mp hx
    apply mem_iUnion₂.mpr
    refine ⟨twoColorWindow b A,Finset.mem_image.mpr ⟨A,hA,rfl⟩,?_⟩
    rw [twoColorWindow_carrier]
    exact ⟨x,hxA,rfl⟩

def twoColorRationalWindows : Set (RelCompactBorelWindow TwoColorSpace) :=
  Set.range (fun z : Bool × (ℚ × ℚ) => twoColorWindow z.1 (nnrealRationalWindow z.2.1 z.2.2))

lemma twoColorWindow_mem (b : Bool) (B : RelCompactBorelWindow ℝ≥0)
    (hB : B ∈ nnrealRationalWindows) : twoColorWindow b B ∈ twoColorRationalWindows := by
  obtain ⟨⟨a,d⟩,rfl⟩ := hB
  exact ⟨(b,a,d),rfl⟩

lemma twoColorRationalWindows_cases {B : RelCompactBorelWindow TwoColorSpace}
    (hB : B ∈ twoColorRationalWindows) :
    ∃ b A,A ∈ nnrealRationalWindows ∧ twoColorWindow b A=B := by
  obtain ⟨⟨b,a,d⟩,rfl⟩ := hB
  exact ⟨b,nnrealRationalWindow a d,⟨(a,d),rfl⟩,rfl⟩

lemma twoColorWindow_inter (b : Bool) (A B C : RelCompactBorelWindow ℝ≥0)
    (hC : C.carrier=A.carrier ∩ B.carrier) :
    (twoColorWindow b C).carrier=(twoColorWindow b A).carrier ∩ (twoColorWindow b B).carrier := by
  simp only [twoColorWindow_carrier,hC]
  exact Set.image_inter (twoColorInjection_injective b)

lemma twoColorWindow_difference (b : Bool) (A B : RelCompactBorelWindow ℝ≥0)
    (hA : A ∈ nnrealRationalWindows) (hB : B ∈ nnrealRationalWindows) :
    ∃ F : Finset (RelCompactBorelWindow TwoColorSpace),
      (∀ C ∈ F,C ∈ twoColorRationalWindows) ∧
      (∀ C ∈ F,∀ D ∈ F,C ≠ D → Disjoint C.carrier D.carrier) ∧
      (⋃ C ∈ F,C.carrier)=(twoColorWindow b A).carrier \ (twoColorWindow b B).carrier := by
  classical
  letI : NullSingletonClass (0:Measure ℝ≥0) := ⟨fun x => by simp⟩
  obtain ⟨F,hF,hd,hU⟩ := (nnrealRationalWindows_basis (0:Measure ℝ≥0)).difference A hA B hB
  refine ⟨F.image (twoColorWindow b),?_,?_,?_⟩
  · intro C hC
    obtain ⟨D,hDF,rfl⟩ := Finset.mem_image.mp hC
    exact twoColorWindow_mem b D (hF D hDF)
  · intro C hC D hD hne
    obtain ⟨C,hCF,rfl⟩ := Finset.mem_image.mp hC
    obtain ⟨D,hDF,rfl⟩ := Finset.mem_image.mp hD
    exact twoColorWindow_disjoint b C D (hd C hCF D hDF (fun h => hne (h ▸ rfl)))
  · rw [twoColorWindow_union,hU,twoColorWindow_carrier,twoColorWindow_carrier]
    exact Set.image_sdiff (twoColorInjection_injective b) A.carrier B.carrier

lemma twoColorRationalWindows_continuity (νN νP : Measure ℝ≥0)
    [NullSingletonClass νN] [NullSingletonClass νP]
    (b : Bool) (B : RelCompactBorelWindow ℝ≥0) (hB : B ∈ nnrealRationalWindows) :
    twoColorMeasure νN νP (frontier (twoColorWindow b B).carrier)=0 := by
  rw [twoColorMeasure_apply _ _ _ isClosed_frontier.measurableSet]
  rw [isOpenMap_inl.preimage_frontier_eq_frontier_preimage continuous_inl,
    isOpenMap_inr.preimage_frontier_eq_frontier_preimage continuous_inr]
  cases b
  · simp only [twoColorWindow,Bool.false_eq_true,if_false,twoColorLeftWindow,
      Sum.inl_injective.preimage_image,Set.preimage_inr_image_inl,frontier_empty,measure_empty,add_zero]
    exact (nnrealRationalWindows_basis νN).continuity B hB
  · simp only [twoColorWindow,if_true,twoColorRightWindow,Sum.inr_injective.preimage_image,
      Set.preimage_inl_image_inr,frontier_empty,measure_empty,zero_add]
    exact (nnrealRationalWindows_basis νP).continuity B hB

lemma twoColorRationalWindows_localApproximation (νN νP : Measure ℝ≥0)
    [NullSingletonClass νN] [NullSingletonClass νP]
    (K U : Set TwoColorSpace) (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ F : Finset (RelCompactBorelWindow TwoColorSpace),
      (∀ B ∈ F,B ∈ twoColorRationalWindows) ∧
      K ⊆ interior (⋃ B ∈ F,B.carrier) ∧ (⋃ B ∈ F,B.carrier) ⊆ U := by
  classical
  have hs (b : Bool) : ∃ F : Finset (RelCompactBorelWindow ℝ≥0),
      (∀ B ∈ F,B ∈ nnrealRationalWindows) ∧
      twoColorInjection b ⁻¹' K ⊆ interior (⋃ B ∈ F,B.carrier) ∧
      (⋃ B ∈ F,B.carrier) ⊆ twoColorInjection b ⁻¹' U := by
    apply (nnrealRationalWindows_basis νN).localApproximation
    · exact (twoColorInjection_closedEmbedding b).isCompact_preimage hK
    · exact hU.preimage (twoColorInjection_continuous b)
    · exact preimage_mono hKU
  obtain ⟨FN,hFN,hKN,hUN⟩ := hs false
  obtain ⟨FP,hFP,hKP,hUP⟩ := hs true
  let FN' := FN.image (twoColorWindow false)
  let FP' := FP.image (twoColorWindow true)
  refine ⟨FN' ∪ FP',?_,?_,?_⟩
  · intro B hB
    rcases Finset.mem_union.mp hB with hB|hB
    · obtain ⟨A,hA,rfl⟩ := Finset.mem_image.mp hB
      exact twoColorWindow_mem false A (hFN A hA)
    · obtain ⟨A,hA,rfl⟩ := Finset.mem_image.mp hB
      exact twoColorWindow_mem true A (hFP A hA)
  · intro z hz
    have hsub (b : Bool) (F : Finset (RelCompactBorelWindow ℝ≥0))
        (hF : F.image (twoColorWindow b) ⊆ FN' ∪ FP') :
        twoColorInjection b '' interior (⋃ B ∈ F,B.carrier) ⊆
          interior (⋃ B ∈ FN' ∪ FP',B.carrier) := by
      apply (twoColorInjection_openEmbedding b).isOpenMap _ isOpen_interior |>.subset_interior_iff.mpr
      intro z hz
      have hh : z ∈ twoColorInjection b '' (⋃ B ∈ F,B.carrier) := image_mono interior_subset hz
      rw [←twoColorWindow_union] at hh
      obtain ⟨B,hB,hzB⟩ := mem_iUnion₂.mp hh
      exact mem_iUnion₂.mpr ⟨B,hF hB,hzB⟩
    cases z with
    | inl x => exact hsub false FN (Finset.subset_union_left) ⟨x,hKN hz,rfl⟩
    | inr x => exact hsub true FP (Finset.subset_union_right) ⟨x,hKP hz,rfl⟩
  · intro z hz
    obtain ⟨B,hB,hzB⟩ := mem_iUnion₂.mp hz
    rcases Finset.mem_union.mp hB with hB|hB
    · have hh : z ∈ ⋃ B ∈ FN',B.carrier := mem_iUnion₂.mpr ⟨B,hB,hzB⟩
      rw [twoColorWindow_union] at hh
      obtain ⟨x,hx,rfl⟩ := hh
      exact hUN hx
    · have hh : z ∈ ⋃ B ∈ FP',B.carrier := mem_iUnion₂.mpr ⟨B,hB,hzB⟩
      rw [twoColorWindow_union] at hh
      obtain ⟨x,hx,rfl⟩ := hh
      exact hUP hx

/-- The genuine two-color rational windows form a countable continuity
semiring; the components remain disjoint even when physical windows overlap. -/
lemma twoColorRationalWindows_basis (νN νP : Measure ℝ≥0)
    [NullSingletonClass νN] [NullSingletonClass νP] :
    ContinuityWindowBasis TwoColorSpace (twoColorMeasure νN νP) twoColorRationalWindows := by
  classical
  refine ⟨Set.countable_range _,?_,?_,?_,?_,twoColorRationalWindows_localApproximation νN νP⟩
  · refine ⟨twoColorWindow false (nnrealRationalWindow 0 0),⟨(false,0,0),rfl⟩,?_⟩
    simp [twoColorWindow_carrier,nnrealRationalWindow_empty]
  · intro A hA B hB
    obtain ⟨a,A,hAN,rfl⟩ := twoColorRationalWindows_cases hA
    obtain ⟨b,B,hBN,rfl⟩ := twoColorRationalWindows_cases hB
    by_cases hab : a=b
    · subst b
      obtain ⟨C,hC,hcar⟩ := (nnrealRationalWindows_basis νN).intersection A hAN B hBN
      exact ⟨twoColorWindow a C,twoColorWindow_mem a C hC,twoColorWindow_inter a A B C hcar⟩
    · refine ⟨twoColorWindow false (nnrealRationalWindow 0 0),⟨(false,0,0),rfl⟩,?_⟩
      have hb : b = !a := by cases a <;> cases b <;> simp_all
      rw [hb,(twoColorWindow_cross_disjoint a A B).inter_eq]
      simp [twoColorWindow_carrier,nnrealRationalWindow_empty]
  · intro A hA B hB
    obtain ⟨a,A,hAN,rfl⟩ := twoColorRationalWindows_cases hA
    obtain ⟨b,B,hBN,rfl⟩ := twoColorRationalWindows_cases hB
    by_cases hab : a=b
    · subst b
      exact twoColorWindow_difference a A B hAN hBN
    · have hb : b = !a := by cases a <;> cases b <;> simp_all
      refine ⟨{twoColorWindow a A},?_,?_,?_⟩
      · intro C hC
        have he := Finset.mem_singleton.mp hC
        subst C
        exact twoColorWindow_mem a A hAN
      · intro C hC D hD hne
        exact (hne ((Finset.mem_singleton.mp hC).trans (Finset.mem_singleton.mp hD).symm)).elim
      · rw [hb,sdiff_eq_left.mpr (twoColorWindow_cross_disjoint a A B)]
        simp
  · intro B hB
    obtain ⟨b,A,hA,rfl⟩ := twoColorRationalWindows_cases hB
    exact twoColorRationalWindows_continuity νN νP b A hA

end WP.Probability
