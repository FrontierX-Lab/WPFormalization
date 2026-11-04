import WPFormalization.HigherOrder.ActualRatioScalarStep
import WPFormalization.HigherOrder.KdVRemainderStep
import WPFormalization.HigherOrder.StrictLossConvolution
/-! The actual KdV scalar row of the C.3 induction. The genuine C.14 product estimate is instantiated with the strict previous-order scalar induction data. The true small-component Gamma/label bound, finite loss count, central C.5 tail and common order weights are all supplied internally. The only local error inputs are the current actual profile bound and actual cusp/genus bounds at orders m<L. No ratio-defect bound, arbitrary recurrence, or full recursive-remainder target is assumed. This is one scalar induction step, not the complete C.3 producer. -/
set_option maxHeartbeats 800000
noncomputable section
namespace WP.HigherOrder
open Set
lemma actual_genus_kdv_uniform_remainder_step (P : PsiTheory) :
    ∃ D B δ₀ : ℝ, ∃ M₀ : ℕ, 0 < D ∧ 0 < B ∧ 0 < δ₀ ∧ δ₀ ≤ 1 ∧ 2 ≤ M₀ ∧
      ∀ M : ℕ, M₀ ≤ M → ∀ g p L : ℕ, 2 ≤ p → 1 ≤ L →
      0 < (complexity g p : ℝ) → ∀ Y ∈ Icc (0 : ℝ) y₀,
      scalarOrderWeight (M : ℝ) L p ^ 2 / (complexity g p : ℝ) < δ₀ →
      ∀ H : ℝ, 0 ≤ H → ∀ EC EG : ℕ → ℝ, (∀ q, 0 ≤ EC q) → (∀ q, 0 ≤ EG q) →
      (|profile P g (1 :: List.replicate (p - 1) 0) Y -
          truncationValue (formalProfile P Y (1 :: List.replicate (p - 1) 0)) L (1 / (complexity g p : ℝ))| ≤
        H * profileOrderWeight (M : ℝ) L (1 :: List.replicate (p - 1) 0) ^ (2 * L) / (complexity g p : ℝ) ^ L) →
      (∀ g' p' m : ℕ, 1 ≤ p' → Stable g' p' → 1 ≤ m → m < L →
        |cuspCorrection P g' p' Y - truncationValue (formalCusp P Y p') m (1 / (complexity g' p' : ℝ))| ≤
          EC m * scalarOrderWeight (M : ℝ) m p' ^ (2 * m) / (complexity g' p' : ℝ) ^ m) →
      (∀ g' p' m : ℕ, 1 ≤ p' → Stable g' p' → 1 ≤ m → m < L →
        |genusCorrection P g' p' Y - truncationValue (formalGenus P Y p') m (1 / (complexity g' p' : ℝ))| ≤
          EG m * scalarOrderWeight (M : ℝ) m p' ^ (2 * m) / (complexity g' p' : ℝ) ^ m) →
      |genusCorrection P g p Y - truncationValue (formalGenus P Y p) L (1 / (complexity g p : ℝ))| ≤
        D * (H + (∑ k ∈ Finset.range L, if 1 ≤ k then B ^ k * (EC (L - k) + EG (L - k)) else 0) + B ^ L) *
          scalarOrderWeight (M : ℝ) L p ^ (2 * L) / (complexity g p : ℝ) ^ L := by
  obtain ⟨T, Ct, Bt, δ₀, hT, hCt, hBt, hδ₀, hδ₀1, hkdv⟩ := actual_genus_kdv_remainder_step_of_ratio_errors P
  obtain ⟨Dr, Br, M₀, hDr, hBr, hM₀, hratio⟩ := actual_large_component_ratio_previous_scalar_step P
  let A : ℝ := 2 * T * Dr
  let R : ℝ := 2 * max A Br
  let B : ℝ := max 1 (max R Bt)
  let D : ℝ := Real.exp 6 + 3 + Ct + 1
  have hA : 0 ≤ A := by
    dsimp [A]
    have hT0 : 0 ≤ T := by linarith
    exact mul_nonneg (mul_nonneg (by norm_num) hT0) hDr.le
  have hR : 0 ≤ R := by dsimp [R]; exact mul_nonneg (by norm_num) (hA.trans (le_max_left _ _))
  have hB : 0 < B := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hRB : R ≤ B := (le_max_left _ _).trans (le_max_right _ _)
  have hBtB : Bt ≤ B := (le_max_right _ _).trans (le_max_right _ _)
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨D, B, δ₀, M₀, hD, hB, hδ₀, hδ₀1, hM₀, ?_⟩
  intro M hM g p L hp hL hh Y hY hsmall H hH EC EG hEC hEG hprofile hcusp hgenus
  have hM2 : (2 : ℝ) ≤ M := by exact_mod_cast hM₀.trans hM
  let S := scalarOrderWeight (M : ℝ) L p
  let h : ℝ := complexity g p
  let E : ℕ → ℝ := fun q => (∑ i ∈ Finset.range q, Br ^ i * (EC (q - i) + EG (q - i))) + Br ^ q
  let V : ℝ := ∑ k ∈ Finset.range L, if 1 ≤ k then B ^ k * (EC (L - k) + EG (L - k)) else 0
  have hS0 : 0 ≤ S := by dsimp [S, scalarOrderWeight]; positivity
  have hS : (p : ℝ) + 2 * L ≤ S := by
    have hm := mul_le_mul_of_nonneg_right hM2 (Nat.cast_nonneg L : (0 : ℝ) ≤ L)
    dsimp [S, scalarOrderWeight]
    linarith
  have hs : Stable g p := by
    have hn : 0 < complexity g p := by exact_mod_cast hh
    unfold Stable complexity at *
    omega
  have hsmall1 : S ^ 2 / h < 1 := hsmall.trans_le hδ₀1
  have hE : ∀ q, 0 ≤ E q := by
    intro q
    dsimp [E]
    exact add_nonneg (Finset.sum_nonneg (fun i hi => mul_nonneg (pow_nonneg hBr.le _) (add_nonneg (hEC _) (hEG _))))
      (pow_nonneg hBr.le _)
  have hratios : ∀ j ∈ Finset.range L, ∀ s ∈ Finset.range (p - 1),
      Stable j (s + 2) → 1 ≤ 2 * j + s → 2 * j + s < L →
      |W P (g - j) (p - s) Y / W P g p Y -
        truncationValue (ratioSeries Y (formalHierarchyJet P Y) p j s) L (1 / h)| ≤
        Dr ^ (2 * j + s) * S ^ (2 * (L - (2 * j + s))) / h ^ L * E (L - (2 * j + s)) := by
    intro j hj s hsMem hstable hr1 hr
    have hsp : s < p := by have ht := Finset.mem_range.mp hsMem; omega
    have hvalid := small_weight_split_child_valid g p j s L S (by omega) hL hs hS hsmall1 hr.le hsp
    exact hratio M hM g p j s L hvalid.1 hsp hvalid.2 hr1 hr Y hY hsmall1.le EC EG hEC hEG hcusp hgenus
  have hk := hkdv (M : ℝ) hM2 g p L hp hL hh Y hY hsmall H Dr hH hDr.le E hE hprofile hratios
  have hcollapse := finite_strict_loss_geometric_convolution A Br hA hBr.le 1 L (fun q => EC q + EG q)
    (fun q => add_nonneg (hEC q) (hEG q))
  have hconv : (∑ k ∈ Finset.range L, if 1 ≤ k then R ^ k * (EC (L - k) + EG (L - k)) else 0) ≤ V := by
    apply Finset.sum_le_sum
    intro k hk
    split_ifs
    · exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hR hRB _) (add_nonneg (hEC _) (hEG _))
    · exact le_rfl
  have hforce := pow_le_pow_left₀ hR hRB L
  have hloss : (∑ r ∈ Finset.range L, if 1 ≤ r then A ^ r * E (L - r) else 0) ≤ V + B ^ L := by
    exact hcollapse.trans (add_le_add hconv hforce)
  have htail := pow_le_pow_left₀ hBt.le hBtB L
  have hV : 0 ≤ V := by
    apply Finset.sum_nonneg
    intro k hk
    split_ifs
    · exact mul_nonneg (pow_nonneg hB.le _) (add_nonneg (hEC _) (hEG _))
    · exact le_rfl
  have hcoeff : Real.exp 6 * H + 3 * (∑ r ∈ Finset.range L, if 1 ≤ r then A ^ r * E (L - r) else 0) + Ct * Bt ^ L ≤
      D * (H + V + B ^ L) := by
    have hp1 : Real.exp 6 ≤ D := by dsimp [D]; linarith
    have hp2 : (3 : ℝ) ≤ D := by dsimp [D]; linarith [Real.exp_pos (6 : ℝ)]
    have hp3 : 3 + Ct ≤ D := by dsimp [D]; linarith [Real.exp_pos (6 : ℝ)]
    have hc1 := mul_le_mul_of_nonneg_right hp1 hH
    have hc2 := mul_le_mul_of_nonneg_right hp2 hV
    have hc3 := mul_le_mul_of_nonneg_right hp3 (pow_nonneg hB.le L)
    have hc4 := mul_le_mul_of_nonneg_left hloss (by norm_num : (0 : ℝ) ≤ 3)
    have hc5 := mul_le_mul_of_nonneg_left htail hCt.le
    nlinarith only [hc1, hc2, hc3, hc4, hc5]
  apply hk.trans
  convert mul_le_mul_of_nonneg_left hcoeff (by positivity : 0 ≤ S ^ (2 * L) / h ^ L) using 1 <;> ring
end WP.HigherOrder
