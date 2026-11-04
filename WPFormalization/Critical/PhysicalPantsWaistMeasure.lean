import WPFormalization.Critical.PhysicalPantsWaistCatalog
import WPFormalization.Critical.PhysicalPrimitivePointMeasure

/- The genuine physical pants parent point measure restricted to a compact
prefix is exactly the finite Dirac sum of the actual complete waist catalog. -/
noncomputable section
set_option maxHeartbeats 0
universe u v w
namespace WP.Critical
open WP.External WP.RandomGeometry MeasureTheory Set
open scoped Classical ENNReal NNReal
variable {P : PsiTheory} {G : WeilPeterssonGeometry.{u,v} P}
  (H : HyperbolicCurveGeometry.{u,v,w} G) {g n : ℕ}
  (X : G.Moduli g n (fun _ => 0))

lemma physicalPantsWaistMeasure_restrict_eq_catalog (K : ℝ≥0) :
    (planarLengthPointMeasure H X 1 (by norm_num) 2).toMeasure.restrict (Iic K) =
      Measure.sum (fun γ : PhysicalPantsWaistCatalog H X K =>
        Measure.dirac (Real.toNNReal (H.length γ.val))) := by
  apply Measure.ext
  intro B hB
  rw [Measure.restrict_apply hB]
  let p := fun γ : H.Primitive g n X =>
    ∃S : Finset (Fin n),H.planarSide γ=some S ∧ S.card=2
  have := curveNNLengthMeasure_finite_window H X 1 (by norm_num) p (B∩Iic K)
    ⟨K,fun _ hx => hx.2⟩
  change curveNNLengthMeasure H X 1 p (B∩Iic K)=_
  rw [curveNNLengthMeasure,sum_dirac_apply_eq_natCard _ _ (hB.inter measurableSet_Iic),
    sum_dirac_apply_eq_natCard _ _ hB]
  congr 1
  apply Nat.card_congr
  exact {
    toFun := fun γ => ⟨⟨γ.val.val,(H.mem_shortPlanar X 2 K _).mpr
      ⟨by simpa only [one_mul] using Real.toNNReal_le_iff_le_coe.mp γ.property.2,
        γ.val.property⟩⟩,by simpa only [one_mul] using γ.property.1⟩
    invFun := fun γ => ⟨⟨γ.val.val,((H.mem_shortPlanar X 2 K _).mp γ.val.property).2⟩,
      by simpa only [one_mul,Set.mem_inter_iff,Set.mem_Iic] using
        And.intro γ.property (Real.toNNReal_le_iff_le_coe.mpr
          ((H.mem_shortPlanar X 2 K _).mp γ.val.property).1)⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }

lemma physicalPantsWaistMeasure_restrict_eq_tuple (K : ℝ≥0) :
    (planarLengthPointMeasure H X 1 (by norm_num) 2).toMeasure.restrict (Iic K) =
      Measure.sum (fun e : Fin (H.shortPlanar X 2 K).card =>
        Measure.dirac (Real.toNNReal (H.length (physicalPantsWaistTuple H X K e)))) := by
  rw [physicalPantsWaistMeasure_restrict_eq_catalog]
  exact (Measure.sum_comp_equiv (physicalPantsWaistEquiv H X K)
    (fun γ : PhysicalPantsWaistCatalog H X K =>
      Measure.dirac (Real.toNNReal (H.length γ.val)))).symm

end WP.Critical
