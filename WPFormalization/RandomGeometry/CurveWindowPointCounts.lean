import WPFormalization.RandomGeometry.CurveLengthPointMeasures
import WPFormalization.RandomGeometry.PantsWindowIntegrability

/-! Point-measure window counts coincide with the original finite geometric
window catalogs. The cutoff only exhibits their finite support. -/
noncomputable section
universe u v w
namespace WP.RandomGeometry
open WP.External MeasureTheory Filter Set WP.Probability
open scoped ENNReal NNReal Topology

/- This half-open bounded window is a genuine relatively compact Borel set. -/
def lengthIocWindow (a b : ℝ≥0) : RelCompactBorelWindow ℝ≥0 where
  carrier := Ioc a b
  measurableSet := measurableSet_Ioc
  compactClosure := by
    apply (isCompact_Icc (a := (0:ℝ≥0)) (b := b)).of_isClosed_subset isClosed_closure
    apply closure_minimal
    · intro x hx
      exact ⟨bot_le,hx.2⟩
    · exact isClosed_Icc

variable {P : PsiTheory} {G : WeilPeterssonGeometry.{u,v} P}
    (H : HyperbolicCurveGeometry.{u,v,w} G) {g n : ℕ}

lemma curveNNLengthMeasure_singleton_zero (X : G.Moduli g n (fun _ => 0))
    (s : ℝ) (hs : 0<s) (p : H.Primitive g n X → Prop) :
    curveNNLengthMeasure H X s p {0}=0 := by
  classical
  unfold curveNNLengthMeasure
  rw [Measure.sum_apply _ (measurableSet_singleton 0)]
  apply ENNReal.tsum_eq_zero.mpr
  intro γ
  rw [Measure.dirac_apply' _ (measurableSet_singleton 0)]
  apply Set.indicator_of_notMem
  simpa only [Set.mem_singleton_iff,ne_eq] using
    (ne_of_gt (Real.toNNReal_pos.mpr (mul_pos hs (H.length_pos γ.val))))

lemma planarLengthPointMeasure_prefix_count (X : G.Moduli g n (fun _ => 0))
    (s : ℝ) (hs : 0<s) (k : ℕ) (B : ℝ≥0) :
    (planarLengthPointMeasure H X s hs k).count ℝ≥0 (nnrealPrefixWindow B) =
      H.planarCount X k ((B : ℝ)/s) := by
  apply Nat.cast_injective (R := ℝ≥0∞)
  exact ((planarLengthPointMeasure H X s hs k).count_spec ℝ≥0
    (nnrealPrefixWindow B)).symm.trans (planarLengthPointMeasure_Iic H X s hs k B)

lemma primitiveLengthPointMeasure_prefix_count (X : G.Moduli g n (fun _ => 0))
    (s : ℝ) (hs : 0<s) (B : ℝ≥0) :
    (primitiveLengthPointMeasure H X s hs).count ℝ≥0 (nnrealPrefixWindow B) =
      H.primitiveCount X ((B : ℝ)/s) := by
  apply Nat.cast_injective (R := ℝ≥0∞)
  exact ((primitiveLengthPointMeasure H X s hs).count_spec ℝ≥0
    (nnrealPrefixWindow B)).symm.trans (primitiveLengthPointMeasure_Iic H X s hs B)

lemma scaled_length_mem_Ioc (s : ℝ) (hs : 0<s) (a b : ℝ≥0) (ℓ : ℝ) :
    Real.toNNReal (s*ℓ) ∈ Ioc a b ↔ ℓ ∈ Ioc ((a : ℝ)/s) ((b : ℝ)/s) := by
  simp only [mem_Ioc,Real.lt_toNNReal_iff_coe_lt,Real.toNNReal_le_iff_le_coe,
    div_lt_iff₀ hs,le_div_iff₀ hs]
  rw [mul_comm ℓ s]

lemma planarLengthPointMeasure_Ioc_eq_windowCount (X : G.Moduli g n (fun _ => 0))
    (s : ℝ) (hs : 0<s) (L : ℝ) (a b : ℝ≥0) (hcut : (b : ℝ)/s ≤ L) :
    (planarLengthPointMeasure H X s hs 2).toMeasure (Ioc a b) =
      (pantsWindowCount H X L
        (fun _ : Fin 1 => Ioc ((a : ℝ)/s) ((b : ℝ)/s)) : ℝ≥0∞) := by
  classical
  let p := fun γ : H.Primitive g n X =>
    ∃S : Finset (Fin n), H.planarSide γ=some S ∧ S.card=2
  letI := curveNNLengthMeasure_finite_window H X s hs p (Ioc a b)
    ⟨b,fun _ hx => hx.2⟩
  change curveNNLengthMeasure H X s p (Ioc a b)=_
  rw [curveNNLengthMeasure,sum_dirac_apply_eq_natCard _ _ measurableSet_Ioc]
  rw [←pantsWindowCatalog_card H X L (Ioc ((a : ℝ)/s) ((b : ℝ)/s))]
  have hc : Nat.card {γ // γ ∈ pantsWindowCatalog H X L
      (Ioc ((a : ℝ)/s) ((b : ℝ)/s))} =
      (pantsWindowCatalog H X L (Ioc ((a : ℝ)/s) ((b : ℝ)/s))).card := by
    simp [Nat.card_eq_fintype_card]
  rw [←hc]
  have hcat (γ : H.Primitive g n X) :
      γ ∈ pantsWindowCatalog H X L (Ioc ((a : ℝ)/s) ((b : ℝ)/s)) ↔
      γ ∈ H.shortPlanar X 2 L ∧ H.length γ ∈ Ioc ((a : ℝ)/s) ((b : ℝ)/s) := by
    simp [pantsWindowCatalog]
  congr 1
  apply Nat.card_congr
  exact {
    toFun := fun γ => ⟨γ.val.val,(hcat _).mpr ⟨
      (H.mem_shortPlanar X 2 L γ.val.val).mpr ⟨
        ((scaled_length_mem_Ioc s hs a b _).mp γ.property).2.trans hcut,γ.val.property⟩,
      (scaled_length_mem_Ioc s hs a b _).mp γ.property⟩⟩
    invFun := fun γ => ⟨⟨γ.val,
      (H.mem_shortPlanar X 2 L γ.val).mp ((hcat _).mp γ.property).1 |>.2⟩,
      (scaled_length_mem_Ioc s hs a b _).mpr ((hcat _).mp γ.property).2⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }

lemma planarLengthPointMeasure_Ioc_count_eq_windowCount (X : G.Moduli g n (fun _ => 0))
    (s : ℝ) (hs : 0<s) (L : ℝ) (a b : ℝ≥0) (hcut : (b : ℝ)/s ≤ L) :
    (planarLengthPointMeasure H X s hs 2).count ℝ≥0 (lengthIocWindow a b) =
      pantsWindowCount H X L
        (fun _ : Fin 1 => Ioc ((a : ℝ)/s) ((b : ℝ)/s)) := by
  apply Nat.cast_injective (R := ℝ≥0∞)
  exact ((planarLengthPointMeasure H X s hs 2).count_spec ℝ≥0
    (lengthIocWindow a b)).symm.trans
      (planarLengthPointMeasure_Ioc_eq_windowCount H X s hs L a b hcut)

end WP.RandomGeometry
