import WPFormalization.Tight.SpectrumTupleExtensionsActualProcess
import WPFormalization.Tight.SpectrumTupleExtensionsGoodMoments
import WPFormalization.Tight.SpectrumTupleExtensionsFactorialIdentification
import WPFormalization.Probability.TwoColorPointMeasuresIntensities
noncomputable section
set_option maxHeartbeats 0
universe u v w z
namespace WP.Tight
open External Set MeasureTheory Filter SpectrumTupleExtensions WP.Probability
open scoped ENNReal NNReal Topology Classical
variable {P : PsiTheory} {G : WeilPeterssonGeometry.{u,v} P}
  {T : TightRegions G} {H : HyperbolicCurveGeometry.{u,v,w} G}
  (Q : TightGeodesicGeometry G T H)

def offBadWindowCountVector (g n : ℕ) {d : ℕ} (B : ℝ)
    (W : Fin d→RelCompactBorelWindow ℝ≥0)
    (X : TightSurface G g 0 n (fun _=>0) (fun _=>0)) : Fin d→ℕ :=
  fun i=>if BadConfiguration Q X (B/tightScale ((n:ℝ)/g)) then 0 else
    (scaledTightPointMeasure Q g n X).count ℝ≥0 (W i)

lemma measurable_offBadWindowCountVector (g n : ℕ) (hg : 2≤g)
    (BM : TightGeodesicBorelModel G T H Q g n hg) {d : ℕ} (B : ℝ)
    (W : Fin d→RelCompactBorelWindow ℝ≥0) :
    Measurable (offBadWindowCountVector Q g n B W) := by
  apply measurable_pi_lambda
  intro i
  exact Measurable.ite (measurableSet_actual_bad_configuration BM _) measurable_const
    (measurable_tightLengthPointMeasure_window_count Q BM _
      (TightConnected.tightScale_pos _ (by positivity)) (W i))

def flatNNRealWindows {d : ℕ} (W : Fin d→RelCompactBorelWindow ℝ≥0) (m : Fin d→ℕ) :
    Fin (∑i,m i)→Set ℝ := fun j=>NNReal.toReal '' (W ((blockIndexEquiv m).symm j).1).carrier

lemma flattened_physical_count_eq_scaled_good_count {g n d : ℕ}
    (X : TightSurface G g 0 n (fun _=>0) (fun _=>0))
    (W : Fin d→RelCompactBorelWindow ℝ≥0) (m : Fin d→ℕ) :
    Nat.card {Γ : Fin (∑i,m i)→Curve Q X // GoodSetTuple Q X
      (flattenedPhysicalWindows (tightScale ((n:ℝ)/g)) W m) Γ} =
    scaledGoodSetCount Q g (∑i,m i) n (flatNNRealWindows W m) X := by
  apply Nat.card_congr
  apply Equiv.subtypeEquivRight
  intro Γ
  apply and_congr_right
  intro hg
  apply forall_congr'
  intro j
  have hp : 0≤tightScale ((n:ℝ)/g)*Q.length (Γ j) :=
    mul_nonneg (TightConnected.tightScale_pos _ (by positivity)).le (Q.length_pos _).le
  constructor
  · intro h
    exact ⟨Real.toNNReal (tightScale ((n:ℝ)/g)*Q.length (Γ j)),h,Real.coe_toNNReal _ hp⟩
  · rintro ⟨b,hb,heq⟩
    change Real.toNNReal (tightScale ((n:ℝ)/g)*Q.length (Γ j))∈
      (W ((blockIndexEquiv m).symm j).1).carrier
    dsimp only at heq
    rw [←heq,Real.toNNReal_coe]
    exact hb

lemma flat_intensity_product {d : ℕ} (W : Fin d→RelCompactBorelWindow ℝ≥0) (m : Fin d→ℕ) :
    (∏j : Fin (∑i,m i),tightIntensity (flatNNRealWindows W m j)) =
      ∏i : Fin d,((windowRates ℝ≥0 nonseparatingLengthIntensity W i : ℝ≥0):ℝ≥0∞)^(m i) := by
  simp only [windowRates_coe]
  calc
    _ = ∏j : Fin (∑i,m i),nonseparatingLengthIntensity (W ((blockIndexEquiv m).symm j).1).carrier := by
      apply Finset.prod_congr rfl
      intro j hj
      exact (nonnegativeIntensity_apply tightIntensity _).symm
    _ = _ := product_flattened_repetitions m (fun i=>nonseparatingLengthIntensity (W i).carrier)

lemma off_bad_mixed_factorial_eq_scaled_good_count {g n d : ℕ}
    (X : TightSurface G g 0 n (fun _=>0) (fun _=>0))
    (W : Fin d→RelCompactBorelWindow ℝ≥0) (hd : DisjointWindows ℝ≥0 W)
    (m : Fin d→ℕ) (hm : ¬∀i,m i=0) (B : ℝ≥0) (hW : ∀i,(W i).carrier⊆Iic B) :
    (∏i : Fin d,(offBadWindowCountVector Q g n (B:ℝ) W X i).descFactorial (m i)) =
      if BadConfiguration Q X ((B:ℝ)/tightScale ((n:ℝ)/g)) then 0 else
        scaledGoodSetCount Q g (∑i,m i) n (flatNNRealWindows W m) X := by
  by_cases hb : BadConfiguration Q X ((B:ℝ)/tightScale ((n:ℝ)/g))
  · simp only [offBadWindowCountVector,hb,ite_true]
    obtain ⟨i,hi⟩:=not_forall.mp hm
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    obtain ⟨k,hk⟩:=Nat.exists_eq_succ_of_ne_zero hi
    rw [hk,Nat.zero_descFactorial_succ]
  · simp only [offBadWindowCountVector,hb,ite_false]
    exact (mixed_factorial_eq_good_set_count_of_not_bad Q X _
      (TightConnected.tightScale_pos _ (by positivity)) W hd m B hW hb).trans
      (flattened_physical_count_eq_scaled_good_count Q X W m)

end WP.Tight
