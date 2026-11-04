import WPFormalization.Critical.PhysicalPrimitivePointMeasure

/- Exact finite geometric catalog partition. The unique piece assignment is
an explicit internal premise, to be supplied by the actual short-support
geometry; this lemma alone does not prove the Appendix G good-event identity. -/
noncomputable section
set_option maxHeartbeats 0
universe u v w z
namespace WP.Critical
open WP.External WP.RandomGeometry WP.Probability MeasureTheory Set
open scoped ENNReal NNReal
variable {P : PsiTheory} {G : WeilPeterssonGeometry.{u,v} P}
  (H : HyperbolicCurveGeometry.{u,v,w} G) {g n : ℕ}
  (X : G.Moduli g n (fun _ => 0))
  {ι : Type z} [Fintype ι] (q : ι → H.Primitive g n X → Prop)
  (L : ℝ≥0) (B : Set ℝ≥0) (hB : B ⊆ Iic L)
  (hpartition : ∀γ : H.Primitive g n X, H.length γ≤L → ∃!i,q i γ)

include hB in
private lemma physicalWindow_short (γ : H.Primitive g n X)
    (hγ : Real.toNNReal (1*H.length γ)∈B) : H.length γ≤L := by
  simpa only [one_mul] using Real.toNNReal_le_iff_le_coe.mp (hB hγ)

def physicalWindowPartitionEquiv :
    {γ : {_γ : H.Primitive g n X // True} // Real.toNNReal (1*H.length γ.val)∈B} ≃
      Σi : ι,{γ : {γ : H.Primitive g n X // q i γ} //
        Real.toNNReal (1*H.length γ.val)∈B} := by
  let f : (Σi : ι,{γ : {γ : H.Primitive g n X // q i γ} //
        Real.toNNReal (1*H.length γ.val)∈B}) →
      {γ : {_γ : H.Primitive g n X // True} // Real.toNNReal (1*H.length γ.val)∈B} :=
    fun γ => ⟨⟨γ.2.val.val,True.intro⟩,γ.2.property⟩
  refine (Equiv.ofBijective f ⟨?_,?_⟩).symm
  · rintro ⟨i,γ⟩ ⟨j,δ⟩ he
    have hv : γ.val.val=δ.val.val := congrArg (fun γ => γ.val.val) he
    obtain ⟨l,_,hu⟩ := hpartition γ.val.val (physicalWindow_short H X L B hB _ γ.property)
    have hij : i=j := (hu i γ.val.property).trans
      (hu j (hv.symm ▸ δ.val.property)).symm
    subst j
    exact congrArg (Sigma.mk i) (Subtype.ext (Subtype.ext hv))
  · intro γ
    obtain ⟨i,hi,_⟩ := hpartition γ.val.val (physicalWindow_short H X L B hB _ γ.property)
    exact ⟨⟨i,⟨⟨γ.val.val,hi⟩,γ.property⟩⟩,rfl⟩

include hB hpartition in
lemma physicalPrimitiveLengthPointMeasure_window_eq_sum
    (hBm : MeasurableSet B) :
    (physicalPrimitiveLengthPointMeasure H X).toMeasure B =
      ∑i : ι,curveNNLengthMeasure H X 1 (q i) B := by
  classical
  have := curveNNLengthMeasure_finite_window H X 1 (by norm_num)
    (fun _ => True) B ⟨L,fun _ hx => hB hx⟩
  have (i : ι) := curveNNLengthMeasure_finite_window H X 1 (by norm_num)
    (q i) B ⟨L,fun _ hx => hB hx⟩
  change curveNNLengthMeasure H X 1 (fun _ => True) B = _
  simp_rw [curveNNLengthMeasure, sum_dirac_apply_eq_natCard _ B hBm]
  rw [←Nat.cast_sum]
  congr 1
  rw [←Nat.card_sigma]
  exact Nat.card_congr (physicalWindowPartitionEquiv H X q L B hB hpartition)

include hpartition in
lemma physicalPrimitiveLengthPointMeasure_prefix_eq_sum :
    (physicalPrimitiveLengthPointMeasure H X).toMeasure (Iic L) =
      ∑i : ι,curveNNLengthMeasure H X 1 (q i) (Iic L) :=
  physicalPrimitiveLengthPointMeasure_window_eq_sum H X q L (Iic L) subset_rfl
    hpartition measurableSet_Iic

include hpartition in
lemma physicalPrimitiveLengthPointMeasure_restrict_eq_sum :
    (physicalPrimitiveLengthPointMeasure H X).toMeasure.restrict (Iic L) =
      (Measure.sum (fun i : ι => curveNNLengthMeasure H X 1 (q i))).restrict (Iic L) := by
  apply Measure.ext
  intro U hU
  rw [Measure.restrict_apply hU,Measure.restrict_apply hU,
    Measure.sum_apply _ (hU.inter measurableSet_Iic),tsum_fintype]
  exact physicalPrimitiveLengthPointMeasure_window_eq_sum H X q L (U∩Iic L)
    inter_subset_right hpartition (hU.inter measurableSet_Iic)

end WP.Critical
