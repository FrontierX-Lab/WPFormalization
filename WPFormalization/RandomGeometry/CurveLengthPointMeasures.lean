import WPFormalization.RandomGeometry.CurveLengthMeasures
import WPFormalization.Probability.PointMeasureDefinitions

/-! The actual length counting measures as genuine locally finite Radon point
measures on [0,∞). Positive physical lengths are unchanged by `toNNReal`. -/
noncomputable section
universe u v w
namespace WP.RandomGeometry
open WP.External MeasureTheory Filter Set
open scoped ENNReal NNReal Topology
variable {P : PsiTheory} {G : WeilPeterssonGeometry.{u,v} P}
    (H : HyperbolicCurveGeometry.{u,v,w} G) {g n : ℕ}

def curveNNLengthMeasure (X : G.Moduli g n (fun _ => 0)) (s : ℝ)
    (p : H.Primitive g n X → Prop) : Measure ℝ≥0 :=
  Measure.sum (fun γ : {γ : H.Primitive g n X // p γ} =>
    Measure.dirac (Real.toNNReal (s*H.length γ.val)))

lemma curveNNLengthMeasure_atom_coe (X : G.Moduli g n (fun _ => 0))
    (s : ℝ) (hs : 0<s) (γ : H.Primitive g n X) :
    (Real.toNNReal (s*H.length γ) : ℝ)=s*H.length γ :=
  Real.coe_toNNReal _ (mul_pos hs (H.length_pos γ)).le

lemma curveNNLengthMeasure_finite_below (X : G.Moduli g n (fun _ => 0))
    (s : ℝ) (hs : 0<s) (p : H.Primitive g n X → Prop) (B : ℝ≥0) :
    Finite {γ : {γ : H.Primitive g n X // p γ} //
      Real.toNNReal (s*H.length γ.val) ≤ B} := by
  letI := curveLengthMeasure_finite_below H X s hs p (B : ℝ)
  let f : {γ : {γ : H.Primitive g n X // p γ} //
      Real.toNNReal (s*H.length γ.val) ≤ B} →
      {γ : {γ : H.Primitive g n X // p γ} // s*H.length γ.val ≤ (B : ℝ)} :=
    fun γ => ⟨γ.val,Real.toNNReal_le_iff_le_coe.mp γ.property⟩
  exact Finite.of_injective f (by
    intro a b h
    apply Subtype.ext
    have hh := congrArg Subtype.val h
    change a.val=b.val at hh
    exact hh)

lemma curveNNLengthMeasure_Iic (X : G.Moduli g n (fun _ => 0))
    (s : ℝ) (hs : 0<s) (p : H.Primitive g n X → Prop) (B : ℝ≥0) :
    curveNNLengthMeasure H X s p (Iic B) =
      (Nat.card {γ : H.Primitive g n X // H.length γ ≤ (B : ℝ)/s ∧ p γ} : ℝ≥0∞) := by
  letI : Finite {γ : {γ : H.Primitive g n X // p γ} //
      Real.toNNReal (s*H.length γ.val) ∈ Iic B} := by
    change Finite {γ : {γ : H.Primitive g n X // p γ} //
      Real.toNNReal (s*H.length γ.val) ≤ B}
    exact curveNNLengthMeasure_finite_below H X s hs p B
  rw [curveNNLengthMeasure,sum_dirac_apply_eq_natCard _ _ measurableSet_Iic]
  congr 1
  apply Nat.card_congr
  exact {
    toFun := fun γ => ⟨γ.val.val,
      (le_div_iff₀ hs).mpr (by
        simpa [mul_comm] using Real.toNNReal_le_iff_le_coe.mp γ.property),γ.val.property⟩
    invFun := fun γ => ⟨⟨γ.val,γ.property.2⟩, Real.toNNReal_le_iff_le_coe.mpr (by
      simpa [mul_comm] using (le_div_iff₀ hs).mp γ.property.1)⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }

lemma curveNNLengthMeasure_isLocallyFinite (X : G.Moduli g n (fun _ => 0))
    (s : ℝ) (hs : 0<s) (p : H.Primitive g n X → Prop) :
    IsLocallyFiniteMeasure (curveNNLengthMeasure H X s p) := by
  constructor
  intro x
  refine ⟨Iic (x+1),Iic_mem_nhds (by simp),?_⟩
  rw [curveNNLengthMeasure_Iic H X s hs p]
  exact ENNReal.natCast_lt_top _

lemma curveNNLengthMeasure_finite_window (X : G.Moduli g n (fun _ => 0))
    (s : ℝ) (hs : 0<s) (p : H.Primitive g n X → Prop) (B : Set ℝ≥0)
    (hB : BddAbove B) :
    Finite {γ : {γ : H.Primitive g n X // p γ} //
      Real.toNNReal (s*H.length γ.val) ∈ B} := by
  rcases hB with ⟨U,hU⟩
  letI := curveNNLengthMeasure_finite_below H X s hs p U
  let f : {γ : {γ : H.Primitive g n X // p γ} //
      Real.toNNReal (s*H.length γ.val) ∈ B} →
      {γ : {γ : H.Primitive g n X // p γ} //
      Real.toNNReal (s*H.length γ.val) ≤ U} := fun γ => ⟨γ.val,hU γ.property⟩
  exact Finite.of_injective f (by
    intro a b h
    apply Subtype.ext
    have hh := congrArg Subtype.val h
    change a.val=b.val at hh
    exact hh)

lemma curveNNLengthMeasure_integerOnRelCompact (X : G.Moduli g n (fun _ => 0))
    (s : ℝ) (hs : 0<s) (p : H.Primitive g n X → Prop) (B : Set ℝ≥0)
    (hB : MeasurableSet B) (hcomp : IsCompact (closure B)) :
    ∃N : ℕ, curveNNLengthMeasure H X s p B=(N : ℝ≥0∞) := by
  letI := curveNNLengthMeasure_finite_window H X s hs p B
    (hcomp.bddAbove.mono subset_closure)
  exact ⟨_,sum_dirac_apply_eq_natCard _ B hB⟩

/- The dependent positive-scale argument guarantees that the atoms are exactly
scaled physical lengths; it is not a Poisson or moment hypothesis. -/
def curveLengthPointMeasure (X : G.Moduli g n (fun _ => 0))
    (s : ℝ) (hs : 0<s) (p : H.Primitive g n X → Prop) :
    WP.Probability.PointMeasure ℝ≥0 where
  toMeasure := curveNNLengthMeasure H X s p
  locallyFinite := curveNNLengthMeasure_isLocallyFinite H X s hs p
  regular := by
    letI := curveNNLengthMeasure_isLocallyFinite H X s hs p
    infer_instance
  integerOnRelCompact := curveNNLengthMeasure_integerOnRelCompact H X s hs p

def primitiveLengthPointMeasure (X : G.Moduli g n (fun _ => 0))
    (s : ℝ) (hs : 0<s) : WP.Probability.PointMeasure ℝ≥0 :=
  curveLengthPointMeasure H X s hs (fun _ => True)

def planarLengthPointMeasure (X : G.Moduli g n (fun _ => 0))
    (s : ℝ) (hs : 0<s) (k : ℕ) : WP.Probability.PointMeasure ℝ≥0 :=
  curveLengthPointMeasure H X s hs (fun γ =>
    ∃S : Finset (Fin n), H.planarSide γ=some S ∧ S.card=k)

lemma primitiveLengthPointMeasure_Iic (X : G.Moduli g n (fun _ => 0))
    (s : ℝ) (hs : 0<s) (B : ℝ≥0) :
    (primitiveLengthPointMeasure H X s hs).toMeasure (Iic B) =
      (H.primitiveCount X ((B : ℝ)/s) : ℝ≥0∞) := by
  change curveNNLengthMeasure H X s _ (Iic B)=_
  rw [curveNNLengthMeasure_Iic H X s hs]
  congr 1
  exact Nat.card_congr (Equiv.subtypeEquivRight (fun _ => by simp))

lemma planarLengthPointMeasure_Iic (X : G.Moduli g n (fun _ => 0))
    (s : ℝ) (hs : 0<s) (k : ℕ) (B : ℝ≥0) :
    (planarLengthPointMeasure H X s hs k).toMeasure (Iic B) =
      (H.planarCount X k ((B : ℝ)/s) : ℝ≥0∞) :=
  curveNNLengthMeasure_Iic H X s hs _ B

lemma planarLengthPointMeasure_prefix_measurable (s : ℝ) (hs : 0<s) (k : ℕ) (B : ℝ≥0) :
    Measurable (fun X : G.Moduli g n (fun _ => 0) =>
      (planarLengthPointMeasure H X s hs k).toMeasure (Iic B)) := by
  simp_rw [planarLengthPointMeasure_Iic H _ s hs k B]
  exact (measurable_of_countable (fun N : ℕ => (N : ℝ≥0∞))).comp
    (H.measurable_planarCount g n k ((B : ℝ)/s))

lemma primitiveLengthPointMeasure_prefix_measurable (s : ℝ) (hs : 0<s) (B : ℝ≥0) :
    Measurable (fun X : G.Moduli g n (fun _ => 0) =>
      (primitiveLengthPointMeasure H X s hs).toMeasure (Iic B)) := by
  simp_rw [primitiveLengthPointMeasure_Iic H _ s hs B]
  exact (measurable_of_countable (fun N : ℕ => (N : ℝ≥0∞))).comp
    (H.measurable_primitiveCount g n ((B : ℝ)/s))

end WP.RandomGeometry
