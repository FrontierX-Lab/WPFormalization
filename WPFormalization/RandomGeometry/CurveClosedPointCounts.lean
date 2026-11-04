import WPFormalization.RandomGeometry.CurveLengthPointMeasures
import WPFormalization.RandomGeometry.CurveWindowPointCounts

/-! Point-measure window counts coincide with the original finite geometric
window catalogs. The cutoff only exhibits their finite support. -/
noncomputable section
universe u v w
namespace WP.RandomGeometry
open WP.External MeasureTheory Filter Set WP.Probability
open scoped ENNReal NNReal Topology

/- This half-open bounded window is a genuine relatively compact Borel set. -/
def lengthIccWindow (a b : ℝ≥0) : RelCompactBorelWindow ℝ≥0 where
  carrier := Icc a b
  measurableSet := measurableSet_Icc
  compactClosure := by
    apply (isCompact_Icc (a := (0:ℝ≥0)) (b := b)).of_isClosed_subset isClosed_closure
    apply closure_minimal
    · intro x hx
      exact ⟨bot_le,hx.2⟩
    · exact isClosed_Icc

variable {P : PsiTheory} {G : WeilPeterssonGeometry.{u,v} P}
    (H : HyperbolicCurveGeometry.{u,v,w} G) {g n : ℕ}

lemma scaled_length_mem_Icc (s : ℝ) (hs : 0<s) (a b : ℝ≥0) (ℓ : ℝ) (hℓ : 0≤ℓ) :
    Real.toNNReal (s*ℓ) ∈ Icc a b ↔ ℓ ∈ Icc ((a : ℝ)/s) ((b : ℝ)/s) := by
  simp only [mem_Icc,Real.le_toNNReal_iff_coe_le (mul_nonneg hs.le hℓ),Real.toNNReal_le_iff_le_coe,
    div_le_iff₀ hs,le_div_iff₀ hs]
  rw [mul_comm ℓ s]

lemma planarLengthPointMeasure_Icc_eq_windowCount (X : G.Moduli g n (fun _ => 0))
    (s : ℝ) (hs : 0<s) (L : ℝ) (a b : ℝ≥0) (hcut : (b : ℝ)/s ≤ L) :
    (planarLengthPointMeasure H X s hs 2).toMeasure (Icc a b) =
      (pantsWindowCount H X L
        (fun _ : Fin 1 => Icc ((a : ℝ)/s) ((b : ℝ)/s)) : ℝ≥0∞) := by
  classical
  let p := fun γ : H.Primitive g n X =>
    ∃S : Finset (Fin n), H.planarSide γ=some S ∧ S.card=2
  letI := curveNNLengthMeasure_finite_window H X s hs p (Icc a b)
    ⟨b,fun _ hx => hx.2⟩
  change curveNNLengthMeasure H X s p (Icc a b)=_
  rw [curveNNLengthMeasure,sum_dirac_apply_eq_natCard _ _ measurableSet_Icc]
  rw [←pantsWindowCatalog_card H X L (Icc ((a : ℝ)/s) ((b : ℝ)/s))]
  have hc : Nat.card {γ // γ ∈ pantsWindowCatalog H X L
      (Icc ((a : ℝ)/s) ((b : ℝ)/s))} =
      (pantsWindowCatalog H X L (Icc ((a : ℝ)/s) ((b : ℝ)/s))).card := by
    simp [Nat.card_eq_fintype_card]
  rw [←hc]
  have hcat (γ : H.Primitive g n X) :
      γ ∈ pantsWindowCatalog H X L (Icc ((a : ℝ)/s) ((b : ℝ)/s)) ↔
      γ ∈ H.shortPlanar X 2 L ∧ H.length γ ∈ Icc ((a : ℝ)/s) ((b : ℝ)/s) := by
    simp [pantsWindowCatalog]
  congr 1
  apply Nat.card_congr
  exact {
    toFun := fun γ => ⟨γ.val.val,(hcat _).mpr ⟨
      (H.mem_shortPlanar X 2 L γ.val.val).mpr ⟨
        ((scaled_length_mem_Icc s hs a b _ (H.length_pos _).le).mp γ.property).2.trans hcut,γ.val.property⟩,
      (scaled_length_mem_Icc s hs a b _ (H.length_pos _).le).mp γ.property⟩⟩
    invFun := fun γ => ⟨⟨γ.val,
      (H.mem_shortPlanar X 2 L γ.val).mp ((hcat _).mp γ.property).1 |>.2⟩,
      (scaled_length_mem_Icc s hs a b _ (H.length_pos _).le).mpr ((hcat _).mp γ.property).2⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }

lemma planarLengthPointMeasure_Icc_count_eq_windowCount (X : G.Moduli g n (fun _ => 0))
    (s : ℝ) (hs : 0<s) (L : ℝ) (a b : ℝ≥0) (hcut : (b : ℝ)/s ≤ L) :
    (planarLengthPointMeasure H X s hs 2).count ℝ≥0 (lengthIccWindow a b) =
      pantsWindowCount H X L
        (fun _ : Fin 1 => Icc ((a : ℝ)/s) ((b : ℝ)/s)) := by
  apply Nat.cast_injective (R := ℝ≥0∞)
  exact ((planarLengthPointMeasure H X s hs 2).count_spec ℝ≥0
    (lengthIccWindow a b)).symm.trans
      (planarLengthPointMeasure_Icc_eq_windowCount H X s hs L a b hcut)

end WP.RandomGeometry
