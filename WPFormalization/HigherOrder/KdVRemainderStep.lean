import WPFormalization.HigherOrder.KdVLossBounds
import WPFormalization.HigherOrder.ScalarTailBounds
import WPFormalization.HigherOrder.ComplexCuspMajorant
/-! The actual KdV scalar remainder from its actual profile, low-loss ratio errors and central C.5 tail. The tail, every finite cutoff, the label Gamma bound, and the small-weight geometry are proved inputs. The displayed local ratio-error assumption is explicit and must still be supplied from the actual C.14 product recurrence; this is not a completed C.3 producer. Only strictly previous orders L-r, r>=1, occur in this part of the bound. -/
noncomputable section
namespace WP.HigherOrder
open Set
lemma scalar_weight_offset_one_pow (M : ℝ) (hM : 2 ≤ M) (L p : ℕ) (hp : 1 ≤ p) :
    (scalarOrderWeight M L p + 1) ^ (2 * L) ≤
      Real.exp 6 * scalarOrderWeight M L p ^ (2 * L) := by
  have hm : scalarOrderWeight M L p + 1 ≤ (p : ℝ) + M * (L + 1) + 2 := by
    unfold scalarOrderWeight
    linarith
  exact (pow_le_pow_left₀ (by unfold scalarOrderWeight; positivity) hm _).trans
    (ComplexCanonical.scalar_weight_succ_offset_pow M (by linarith) L p hp)

lemma actual_genus_kdv_remainder_step_of_ratio_errors (P : PsiTheory) :
    ∃ T C B δ₀ : ℝ, 1 ≤ T ∧ 0 < C ∧ 0 < B ∧ 0 < δ₀ ∧ δ₀ ≤ 1 ∧
      ∀ M : ℝ, 2 ≤ M → ∀ g p L : ℕ, 2 ≤ p → 1 ≤ L →
      0 < (complexity g p : ℝ) → ∀ Y ∈ Icc (0 : ℝ) y₀,
      scalarOrderWeight M L p ^ 2 / (complexity g p : ℝ) < δ₀ →
      ∀ H D : ℝ, 0 ≤ H → 0 ≤ D → ∀ E : ℕ → ℝ, (∀ q, 0 ≤ E q) →
      (|profile P g (1 :: List.replicate (p - 1) 0) Y -
          truncationValue (formalProfile P Y (1 :: List.replicate (p - 1) 0)) L (1 / (complexity g p : ℝ))| ≤
        H * profileOrderWeight M L (1 :: List.replicate (p - 1) 0) ^ (2 * L) / (complexity g p : ℝ) ^ L) →
      (∀ j ∈ Finset.range L, ∀ s ∈ Finset.range (p - 1),
        Stable j (s + 2) → 1 ≤ 2 * j + s → 2 * j + s < L →
        |W P (g - j) (p - s) Y / W P g p Y -
          truncationValue (ratioSeries Y (formalHierarchyJet P Y) p j s) L (1 / (complexity g p : ℝ))| ≤
          D ^ (2 * j + s) * scalarOrderWeight M L p ^ (2 * (L - (2 * j + s))) /
            (complexity g p : ℝ) ^ L * E (L - (2 * j + s))) →
      |genusCorrection P g p Y - truncationValue (formalGenus P Y p) L (1 / (complexity g p : ℝ))| ≤
        (scalarOrderWeight M L p ^ (2 * L) / (complexity g p : ℝ) ^ L) *
          (Real.exp 6 * H + 3 * (∑ r ∈ Finset.range L, if 1 ≤ r then (2 * T * D) ^ r * E (L - r) else 0) + C * B ^ L) := by
  obtain ⟨T, hT, hlow⟩ := kdv_low_mass_remainder_scaled_bound P
  obtain ⟨C, B, δ₀, hC, hB, hδ₀, hδ₀1, htail⟩ := kdv_central_tail_small_weight_uniform P
  refine ⟨T, 3 / 2 * C, B, δ₀, hT, by positivity, hB, hδ₀, hδ₀1, ?_⟩
  intro M hM g p L hp hL hh Y hY hsmall H D hH hD E hE hprofile hratio
  let h : ℝ := complexity g p
  let S := scalarOrderWeight M L p
  have hp1 : 1 ≤ p := by omega
  have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hM0 : 0 ≤ M := by linarith
  have hMS : (p : ℝ) + 2 * L ≤ S := by
    have hm := mul_le_mul_of_nonneg_right hM (Nat.cast_nonneg L : (0 : ℝ) ≤ L)
    dsimp [S, scalarOrderWeight]
    linarith
  have hS : 1 ≤ S := by linarith [Nat.cast_nonneg (α := ℝ) L]
  have hSp : (p : ℝ) + L ≤ S := by linarith [Nat.cast_nonneg (α := ℝ) L]
  obtain ⟨hg2, hLg, h2L, hproot, hLroot⟩ :=
    scalar_small_weight_kdv_geometry M hM g p L hp hL hh (hsmall.trans_le hδ₀1)
  have hPweight : profileOrderWeight M L (1 :: List.replicate (p - 1) 0) = S + 1 := by
    simp only [profileOrderWeight, List.sum_cons, List.sum_replicate, nsmul_zero, add_zero,
      List.length_cons, List.length_replicate, Nat.cast_add, Nat.cast_one, Nat.cast_sub hp1]
    dsimp [S, scalarOrderWeight]
    ring
  have hprof : |profile P g (1 :: List.replicate (p - 1) 0) Y -
      truncationValue (formalProfile P Y (1 :: List.replicate (p - 1) 0)) L (1 / h)| ≤
      (S ^ (2 * L) / h ^ L) * (Real.exp 6 * H) := by
    rw [hPweight] at hprofile
    apply hprofile.trans
    convert div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (scalar_weight_offset_one_pow M hM L p hp1) hH)
      (pow_nonneg hh.le L) using 1 <;> ring
  have hlo := hlow g p L hp hL Y hY S h D hS hh hD hSp E hE hratio
  have hta := htail M hM g p L hp hL hh hsmall Y hY
  have hid := actual_genus_kdv_remainder_pairing P g p L (by omega) hp hL hLg h2L Y hY (1 / h)
  rw [hid]
  have hb :
      |(profile P g (1 :: List.replicate (p - 1) 0) Y -
          truncationValue (formalProfile P Y (1 :: List.replicate (p - 1) 0)) L (1 / h)) -
        3 * (kdvActualLowMass P g p L Y - truncationValue (kdvFormalLowSeries P Y p L) L (1 / h)) -
        3 / 2 * markedSplitLossTail P g p 2 L Y| ≤
      |profile P g (1 :: List.replicate (p - 1) 0) Y -
          truncationValue (formalProfile P Y (1 :: List.replicate (p - 1) 0)) L (1 / h)| +
        3 * |kdvActualLowMass P g p L Y - truncationValue (kdvFormalLowSeries P Y p L) L (1 / h)| +
        3 / 2 * |markedSplitLossTail P g p 2 L Y| := by
    have hs := abs_sub
      (profile P g (1 :: List.replicate (p - 1) 0) Y -
        truncationValue (formalProfile P Y (1 :: List.replicate (p - 1) 0)) L (1 / h))
      (3 * (kdvActualLowMass P g p L Y - truncationValue (kdvFormalLowSeries P Y p L) L (1 / h)))
    have ht := abs_sub
      ((profile P g (1 :: List.replicate (p - 1) 0) Y -
          truncationValue (formalProfile P Y (1 :: List.replicate (p - 1) 0)) L (1 / h)) -
        3 * (kdvActualLowMass P g p L Y - truncationValue (kdvFormalLowSeries P Y p L) L (1 / h)))
      (3 / 2 * markedSplitLossTail P g p 2 L Y)
    norm_num [abs_mul] at hs ht
    simpa only [one_div] using ht.trans (add_le_add hs le_rfl)
  apply hb.trans
  apply (add_le_add (add_le_add hprof (mul_le_mul_of_nonneg_left hlo (by norm_num)))
    (mul_le_mul_of_nonneg_left hta (by norm_num))).trans_eq
  ring
end WP.HigherOrder
