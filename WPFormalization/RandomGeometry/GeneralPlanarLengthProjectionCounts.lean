import WPFormalization.RandomGeometry.GeneralPlanarMarkedPointProcess

/-! Actual length counts split into finitely many original integer cusp
marks whenever the actual window contains no larger mark. This is a catalog
identity, independent of all integration and probability limits. -/
noncomputable section
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false
universe u v w
namespace WP.RandomGeometry
open WP.External WP.Probability MeasureTheory Filter Set
open scoped ENNReal NNReal Topology Classical
variable {P : PsiTheory} {G : WeilPeterssonGeometry.{u,v} P}
    (H : HyperbolicCurveGeometry.{u,v,w} G) {g n : ℕ}

lemma curveLengthPointMeasure_count_eq_natCard (X : G.Moduli g n (fun _=>0))
    (s : ℝ) (hs : 0<s) (p : H.Primitive g n X→Prop) (B : RelCompactBorelWindow ℝ≥0) :
    (curveLengthPointMeasure H X s hs p).count ℝ≥0 B=
      Nat.card {γ : {γ : H.Primitive g n X //p γ} //Real.toNNReal (s*H.length γ.val)∈B.carrier} := by
  letI := curveNNLengthMeasure_finite_window H X s hs p B.carrier (B.compactClosure.bddAbove.mono subset_closure)
  apply Nat.cast_injective (R:=ℝ≥0∞)
  rw [←PointMeasure.count_spec]
  change curveNNLengthMeasure H X s p B.carrier=_
  rw [curveNNLengthMeasure,sum_dirac_apply_eq_natCard _ _ B.measurableSet]

def generalPlanarLengthPointProcess (X : G.Moduli g n (fun _=>0)) : PointMeasure ℝ≥0 :=
  curveLengthPointMeasure H X (pantsLengthScale g n) (pantsLengthScale_pos g n) (IsPlanarPrimitive H)

lemma generalPlanarLengthPointProcess_window_partition (X : G.Moduli g n (fun _=>0))
    (B : RelCompactBorelWindow ℝ≥0) (N : ℕ)
    (hN : ∀γ : H.Primitive g n X,IsPlanarPrimitive H γ→
      Real.toNNReal (pantsLengthScale g n*H.length γ)∈B.carrier→planarPrimitiveCuspType H γ<N) :
    (generalPlanarLengthPointProcess H X).count ℝ≥0 B=
      ∑k : Fin N,(planarLengthPointMeasure H X (pantsLengthScale g n) (pantsLengthScale_pos g n) k.val).count ℝ≥0 B := by
  let p := IsPlanarPrimitive H (g:=g) (n:=n) (X:=X)
  let s := pantsLengthScale g n
  have hs : 0<s := pantsLengthScale_pos g n
  let A := {γ : {γ : H.Primitive g n X //p γ} //Real.toNNReal (s*H.length γ.val)∈B.carrier}
  let F := fun k : Fin N=>{γ : {γ : H.Primitive g n X //p γ ∧planarPrimitiveCuspType H γ=k.val} //
    Real.toNNReal (s*H.length γ.val)∈B.carrier}
  letI : Finite A := curveNNLengthMeasure_finite_window H X s hs p B.carrier (B.compactClosure.bddAbove.mono subset_closure)
  letI (k : Fin N) : Finite (F k) := curveNNLengthMeasure_finite_window H X s hs
    (fun γ=>p γ ∧planarPrimitiveCuspType H γ=k.val) B.carrier (B.compactClosure.bddAbove.mono subset_closure)
  let e : A≃Σk : Fin N,F k := {
    toFun:=fun γ=>⟨⟨planarPrimitiveCuspType H γ.val.val,hN _ γ.val.property γ.property⟩,
      ⟨⟨γ.val.val,γ.val.property,rfl⟩,γ.property⟩⟩
    invFun:=fun γ=>⟨⟨γ.2.val.val,γ.2.val.property.1⟩,γ.2.property⟩
    left_inv:=fun _=>rfl
    right_inv:=by
      rintro ⟨⟨k,hk⟩,⟨⟨γ,hp,hm⟩,hB⟩⟩
      cases hm
      rfl }
  have hc : Nat.card A=∑k : Fin N,Nat.card (F k) := by
    letI : Fintype A := Fintype.ofFinite A
    letI (k : Fin N) : Fintype (F k) := Fintype.ofFinite (F k)
    simpa only [Nat.card_eq_fintype_card,Fintype.card_sigma] using Fintype.card_congr e
  change (curveLengthPointMeasure H X s hs p).count ℝ≥0 B=_
  rw [curveLengthPointMeasure_count_eq_natCard]
  change Nat.card A=_
  rw [hc]
  apply Finset.sum_congr rfl
  intro k _
  rw [←curveLengthPointMeasure_count_eq_natCard H X s hs (fun γ=>p γ ∧planarPrimitiveCuspType H γ=k.val) B]
  simp_rw [p,planarPrimitiveCuspType_spec]
  rfl

lemma generalPlanarLengthPointProcess_prefix_count_measurable (b : ℝ≥0) :
    Measurable (fun X : G.Moduli g n (fun _=>0)=>
      (generalPlanarLengthPointProcess H X).count ℝ≥0 (nnrealPrefixWindow b)) := by
  have he (X : G.Moduli g n (fun _=>0)) := generalPlanarLengthPointProcess_window_partition H X (nnrealPrefixWindow b) (n+1)
    (fun γ hγ _=>Nat.lt_succ_of_le (planarPrimitiveCuspType_le_cusps H γ hγ))
  simp_rw [he]
  exact Finset.measurable_sum _ (fun k _=>generalPlanarLengthPointMeasure_prefix_count_measurable H _ (pantsLengthScale_pos g n) k.val b)

lemma generalPlanarLengthPointProcess_rational_count_measurable (a b : ℚ) :
    Measurable (fun X : G.Moduli g n (fun _=>0)=>
      (generalPlanarLengthPointProcess H X).count ℝ≥0 (nnrealRationalWindow a b)) := by
  have he (X : G.Moduli g n (fun _=>0)) := generalPlanarLengthPointProcess_window_partition H X (nnrealRationalWindow a b) (n+1)
    (fun γ hγ _=>Nat.lt_succ_of_le (planarPrimitiveCuspType_le_cusps H γ hγ))
  simp_rw [he]
  exact Finset.measurable_sum _ (fun k _=>generalPlanarLengthPointMeasure_rational_count_measurable H _ (pantsLengthScale_pos g n) k.val a b)


lemma generalPlanarLengthPointProcess_Ioc_count_measurable (a b : ℝ≥0) :
    Measurable (fun X : G.Moduli g n (fun _=>0)=>
      (generalPlanarLengthPointProcess H X).count ℝ≥0 (lengthIocWindow a b)) := by
  change Measurable (fun X : G.Moduli g n (fun _=>0)=>
    (generalPlanarLengthPointProcess H X).count ℝ≥0 (nnrealIocWindow a b))
  simp_rw [PointMeasure.count_nnrealIoc]
  exact (generalPlanarLengthPointProcess_prefix_count_measurable H b).sub
    (generalPlanarLengthPointProcess_prefix_count_measurable H a)

end WP.RandomGeometry
