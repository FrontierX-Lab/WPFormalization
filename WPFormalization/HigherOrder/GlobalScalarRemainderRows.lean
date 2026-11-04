import WPFormalization.HigherOrder.RemainderStateBounds
import WPFormalization.HigherOrder.CuspRemainderStep
import WPFormalization.HigherOrder.KdVScalarRemainderStep
import WPFormalization.HigherOrder.DescentScalarRemainderStep
import WPFormalization.HigherOrder.LargeWeightScales
import WPFormalization.HigherOrder.ProfileLowCore
/-! The genuine three global scalar rows for C.3. Each local small-weight step is combined with the proved all-scales large-weight estimate. The rows quantify over every stable positive-complexity state and physical Y, including small genus and invalid-profile children. Their only inputs are the appropriate current stage bound and strict previous-order stage bounds. Constants are chosen before every larger common Nat scale M. These are implication rows for the simultaneous induction; the final full remainder target is supplied separately. -/
noncomputable section
namespace WP.HigherOrder
open Set PowerSeries
lemma scalar_state_error_coefficient_mono (M L g p : ℕ) (a b : ℝ) (hab : a ≤ b) :
    a * scalarOrderWeight (M : ℝ) L p ^ (2 * L) / (complexity g p : ℝ) ^ L ≤
      b * scalarOrderWeight (M : ℝ) L p ^ (2 * L) / (complexity g p : ℝ) ^ L :=
  div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right hab (by unfold scalarOrderWeight; positivity)) (by positivity)

lemma strict_geometric_loss_sum_le_Icc (B : ℝ) (hB : 0 ≤ B) (L : ℕ) (e : ℕ → ℝ)
    (he : ∀ q, 0 ≤ e q) :
    (∑ i ∈ Finset.range L, if 1 ≤ i then B ^ i * e (L - i) else 0) ≤
      ∑ i ∈ Finset.Icc 1 L, B ^ i * e (L - i) := by
  classical
  rw [← Finset.sum_filter]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro i hi
    obtain ⟨hiL, hi1⟩ := Finset.mem_filter.mp hi
    exact Finset.mem_Icc.mpr ⟨hi1, (Finset.mem_range.mp hiL).le⟩
  · intro i hi hnot
    exact mul_nonneg (pow_nonneg hB _) (he _)

lemma large_scalar_component_remainders_all_scales (P : PsiTheory) (δ₀ : ℝ) (hδ₀ : 0 < δ₀) :
    ∃ C B : ℝ, ∃ M₀ : ℕ, 0 < C ∧ 0 < B ∧ 2 ≤ M₀ ∧ ∀ M : ℕ, M₀ ≤ M →
      ∀ g p L : ℕ, 1 ≤ p → Stable g p → 1 ≤ complexity g p → 1 ≤ L →
      ∀ Y ∈ Icc (0 : ℝ) y₀, δ₀ ≤ scalarOrderWeight (M : ℝ) L p ^ 2 / (complexity g p : ℝ) →
      |cuspCorrection P g p Y - truncationValue (formalCusp P Y p) L (1 / (complexity g p : ℝ))| ≤
        C * B ^ L * scalarOrderWeight (M : ℝ) L p ^ (2 * L) / (complexity g p : ℝ) ^ L ∧
      |genusCorrection P g p Y - truncationValue (formalGenus P Y p) L (1 / (complexity g p : ℝ))| ≤
        C * B ^ L * scalarOrderWeight (M : ℝ) L p ^ (2 * L) / (complexity g p : ℝ) ^ L := by
  obtain ⟨C, B, M₀, hC, hB, hM₀, hlarge⟩ := canonical_large_weight_remainders_all_scales P δ₀ hδ₀
  refine ⟨C, B, M₀, hC, hB, hM₀, ?_⟩
  intro M hM g p L hp hs hh hL Y hY hδ
  have ht := (hlarge M hM).2 g p hp hs hh L hL Y hY hδ
  have he :
      |cuspCorrection P g p Y - truncationValue (formalCusp P Y p) L (1 / (complexity g p : ℝ))| +
      |genusCorrection P g p Y - truncationValue (formalGenus P Y p) L (1 / (complexity g p : ℝ))| ≤
        C * B ^ L * scalarOrderWeight (M : ℝ) L p ^ (2 * L) / (complexity g p : ℝ) ^ L := by
    simpa only [truncationValue_at_inverse, formalCusp, formalGenus, PowerSeries.coeff_mk] using ht
  exact ⟨(le_add_of_nonneg_right (abs_nonneg _)).trans he, (le_add_of_nonneg_left (abs_nonneg _)).trans he⟩

lemma global_cusp_remainder_stage (P : PsiTheory) :
    ∃ D B : ℝ, ∃ M₀ : ℕ, 0 < D ∧ 0 < B ∧ 2 ≤ M₀ ∧ ∀ M : ℕ, M₀ ≤ M →
      ∀ L : ℕ, 1 ≤ L → ∀ E : ℝ, 0 ≤ E →
      RemainderStageBound P M 0 L E → RemainderStageBound P M 1 L (D * (E + B ^ L)) := by
  obtain ⟨Ds, Bs, Ms, hDs, hBs, hMs, hsmall⟩ := actual_cusp_uniform_remainder_step_exponential P
  obtain ⟨Cl, Bl, Ml, hCl, hBl, hMl, hlarge⟩ := large_scalar_component_remainders_all_scales P 1 (by norm_num)
  let D := Ds + Cl
  let B := max Bs Bl
  have hD : 0 < D := by dsimp [D]; positivity
  have hB : 0 < B := lt_of_lt_of_le hBs (le_max_left _ _)
  refine ⟨D, B, max Ms Ml, hD, hB, hMs.trans (le_max_left _ _), ?_⟩
  intro M hM L hL E hE hprofile
  have hMsM : Ms ≤ M := (le_max_left _ _).trans hM
  have hMlM : Ml ≤ M := (le_max_right _ _).trans hM
  intro g p _ hp hs hh Y hY
  by_cases hδ : scalarOrderWeight (M : ℝ) L p ^ 2 / (complexity g p : ℝ) ≤ 1
  · have hchildren (d : ℕ) :
        |profile P g (d :: List.replicate p 0) Y -
          truncationValue (formalProfile P Y (d :: List.replicate p 0)) L (1 / (complexity g (p + 1) : ℝ))| ≤
        E * profileOrderWeight (M : ℝ) L (d :: List.replicate p 0) ^ (2 * L) / (complexity g (p + 1) : ℝ) ^ L := by
      have hsc : Stable g (d :: List.replicate p 0).length := by
        simp only [List.length_cons, List.length_replicate]
        unfold Stable at *
        omega
      have hhc : 1 ≤ complexity g (d :: List.replicate p 0).length := by
        simp only [List.length_cons, List.length_replicate]
        unfold Stable complexity at *
        omega
      simpa only [List.length_cons, List.length_replicate] using
        hprofile g (d :: List.replicate p 0) (by simp) hsc hhc Y hY
    have hb := hsmall M hMsM g p L hp hs hL hh Y hY hδ E hE hchildren
    apply hb.trans
    apply scalar_state_error_coefficient_mono
    have hpow := pow_le_pow_left₀ hBs.le (le_max_left Bs Bl) L
    have hc1 : Ds ≤ D := by dsimp [D]; linarith
    exact mul_le_mul hc1 (add_le_add le_rfl hpow) (by positivity) hD.le
  · have hδ' : (1 : ℝ) ≤ scalarOrderWeight (M : ℝ) L p ^ 2 / (complexity g p : ℝ) := le_of_lt (lt_of_not_ge hδ)
    have hb := (hlarge M hMlM g p L hp hs hh hL Y hY hδ').1
    apply hb.trans
    apply scalar_state_error_coefficient_mono
    have hpow := pow_le_pow_left₀ hBl.le (le_max_right Bs Bl) L
    have hc1 : Cl ≤ D := by dsimp [D]; linarith
    have he1 := mul_le_mul hc1 hpow (pow_nonneg hBl.le L) hD.le
    have he2 := mul_nonneg hD.le hE
    nlinarith
end WP.HigherOrder

namespace WP.HigherOrder
open Set
lemma global_high_genus_remainder_stage (P : PsiTheory) :
    ∃ D B : ℝ, ∃ M₀ : ℕ, 0 < D ∧ 0 < B ∧ 2 ≤ M₀ ∧ ∀ M : ℕ, M₀ ≤ M →
      ∀ L : ℕ, 1 ≤ L → ∀ e : ℕ → ℝ, (∀ q, 0 ≤ e q) →
      (∀ q : ℕ, 1 ≤ q → q < L → ∀ s, RemainderStageBound P M s q (e q)) →
      ∀ E : ℝ, 0 ≤ E → RemainderStageBound P M 0 L E →
      RemainderStageBound P M 2 L
        (D * (E + (∑ i ∈ Finset.Icc 1 L, B ^ i * e (L - i)) + B ^ L)) := by
  obtain ⟨Ds, Bs, δ₀, Ms, hDs, hBs, hδ₀, hδ₀1, hMs, hsmall⟩ := actual_genus_kdv_uniform_remainder_step P
  obtain ⟨Cl, Bl, Ml, hCl, hBl, hMl, hlarge⟩ := large_scalar_component_remainders_all_scales P δ₀ hδ₀
  let D := 2 * Ds + Cl
  let B := max Bs Bl
  have hD : 0 < D := by dsimp [D]; positivity
  have hB : 0 < B := lt_of_lt_of_le hBs (le_max_left _ _)
  refine ⟨D, B, max Ms Ml, hD, hB, hMs.trans (le_max_left _ _), ?_⟩
  intro M hM L hL e he hprev E hE hprofile
  have hMsM : Ms ≤ M := (le_max_left _ _).trans hM
  have hMlM : Ml ≤ M := (le_max_right _ _).trans hM
  let V : ℝ := ∑ i ∈ Finset.Icc 1 L, B ^ i * e (L - i)
  have hV : 0 ≤ V := Finset.sum_nonneg (fun i hi => mul_nonneg (pow_nonneg hB.le _) (he _))
  intro g p hp2 hp hs hh Y hY
  have hhR : (0 : ℝ) < complexity g p := by exact_mod_cast (show 0 < complexity g p by omega)
  by_cases hδ : scalarOrderWeight (M : ℝ) L p ^ 2 / (complexity g p : ℝ) < δ₀
  · have holdcusp (g' p' q : ℕ) (hp' : 1 ≤ p') (hs' : Stable g' p') (hq : 1 ≤ q) (hqL : q < L) :
        |cuspCorrection P g' p' Y - truncationValue (formalCusp P Y p') q (1 / (complexity g' p' : ℝ))| ≤
        e q * scalarOrderWeight (M : ℝ) q p' ^ (2 * q) / (complexity g' p' : ℝ) ^ q := by
      have hh' : 1 ≤ complexity g' p' := by unfold Stable complexity at *; omega
      exact hprev q hq hqL 1 g' p' trivial hp' hs' hh' Y hY
    have holdgenus (g' p' q : ℕ) (hp' : 1 ≤ p') (hs' : Stable g' p') (hq : 1 ≤ q) (hqL : q < L) :
        |genusCorrection P g' p' Y - truncationValue (formalGenus P Y p') q (1 / (complexity g' p' : ℝ))| ≤
        e q * scalarOrderWeight (M : ℝ) q p' ^ (2 * q) / (complexity g' p' : ℝ) ^ q := by
      have hh' : 1 ≤ complexity g' p' := by unfold Stable complexity at *; omega
      by_cases hp1 : p' = 1
      · exact hprev q hq hqL 3 g' p' hp1 hp' hs' hh' Y hY
      · exact hprev q hq hqL 2 g' p' (by omega) hp' hs' hh' Y hY
    have hlength : (1 :: List.replicate (p - 1) 0).length = p := by simp; omega
    have hprof : |profile P g (1 :: List.replicate (p - 1) 0) Y -
        truncationValue (formalProfile P Y (1 :: List.replicate (p - 1) 0)) L (1 / (complexity g p : ℝ))| ≤
        E * profileOrderWeight (M : ℝ) L (1 :: List.replicate (p - 1) 0) ^ (2 * L) / (complexity g p : ℝ) ^ L := by
      have ht := hprofile g (1 :: List.replicate (p - 1) 0) (by rw [hlength]; omega)
        (by rw [hlength]; exact hs) (by rw [hlength]; exact hh) Y hY
      simpa only [hlength] using ht
    have hb := hsmall M hMsM g p L hp2 hL hhR Y hY hδ E hE e e he he hprof holdcusp holdgenus
    apply hb.trans
    apply scalar_state_error_coefficient_mono
    have hsum : (∑ i ∈ Finset.range L, if 1 ≤ i then Bs ^ i * (e (L - i) + e (L - i)) else 0) ≤ 2 * V := by
      apply (strict_geometric_loss_sum_le_Icc Bs hBs.le L (fun q => e q + e q) (fun q => add_nonneg (he q) (he q))).trans
      calc
        _ ≤ ∑ i ∈ Finset.Icc 1 L, B ^ i * (e (L - i) + e (L - i)) := by
          apply Finset.sum_le_sum
          intro i hi
          exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hBs.le (le_max_left Bs Bl) _) (add_nonneg (he _) (he _))
        _ = _ := by dsimp [V]; rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i hi; ring
    have hpow := pow_le_pow_left₀ hBs.le (le_max_left Bs Bl) L
    have hcoef : 2 * Ds ≤ D := by dsimp [D]; linarith
    have hh1 := mul_le_mul_of_nonneg_left hsum hDs.le
    have hh2 := mul_le_mul_of_nonneg_left hpow hDs.le
    have hh3 := mul_le_mul_of_nonneg_right hcoef (show 0 ≤ E + V + B ^ L by positivity)
    have hh4 := mul_nonneg hDs.le (show 0 ≤ E + B ^ L by positivity)
    nlinarith only [hh1, hh2, hh3, hh4]
  · have hδ' : δ₀ ≤ scalarOrderWeight (M : ℝ) L p ^ 2 / (complexity g p : ℝ) := le_of_not_gt hδ
    have hb := (hlarge M hMlM g p L hp hs hh hL Y hY hδ').2
    apply hb.trans
    apply scalar_state_error_coefficient_mono
    have hpow := pow_le_pow_left₀ hBl.le (le_max_right Bs Bl) L
    have hc1 : Cl ≤ D := by dsimp [D]; linarith
    have he1 := mul_le_mul hc1 hpow (pow_nonneg hBl.le L) hD.le
    have he2 := mul_nonneg hD.le (add_nonneg hE hV)
    nlinarith
end WP.HigherOrder


namespace WP.HigherOrder
open Set
lemma global_one_genus_remainder_stage (P : PsiTheory) :
    ∃ D B : ℝ, ∃ M₀ : ℕ, 0 < D ∧ 0 < B ∧ 2 ≤ M₀ ∧ ∀ M : ℕ, M₀ ≤ M →
      ∀ L : ℕ, 1 ≤ L → ∀ e : ℕ → ℝ, (∀ q, 0 ≤ e q) →
      (∀ q : ℕ, 1 ≤ q → q < L → ∀ s, RemainderStageBound P M s q (e q)) →
      ∀ C H : ℝ, 0 ≤ C → 0 ≤ H →
      RemainderStageBound P M 1 L C → RemainderStageBound P M 2 L H →
      RemainderStageBound P M 3 L
        (D * (H + C + (∑ i ∈ Finset.Icc 1 L, B ^ i * e (L - i)) + B ^ L)) := by
  obtain ⟨Ds, Bs, δ₀, Ms, hDs, hBs, hδ₀, hδ₀1, hMs, hsmall⟩ := actual_genus_one_uniform_scalar_row P
  obtain ⟨Cl, Bl, Ml, hCl, hBl, hMl, hlarge⟩ := large_scalar_component_remainders_all_scales P δ₀ hδ₀
  let D := Ds + Cl
  let B := max Bs Bl
  have hD : 0 < D := by dsimp [D]; positivity
  have hB : 0 < B := lt_of_lt_of_le hBs (le_max_left _ _)
  refine ⟨D, B, max Ms Ml, hD, hB, hMs.trans (le_max_left _ _), ?_⟩
  intro M hM L hL e he hprev C H hC hH hcurrent hhigh
  have hMsM : Ms ≤ M := (le_max_left _ _).trans hM
  have hMlM : Ml ≤ M := (le_max_right _ _).trans hM
  have hM2 : (2 : ℝ) ≤ M := by exact_mod_cast hMs.trans hMsM
  let V : ℝ := ∑ i ∈ Finset.Icc 1 L, B ^ i * e (L - i)
  have hV : 0 ≤ V := Finset.sum_nonneg (fun i hi => mul_nonneg (pow_nonneg hB.le _) (he _))
  intro g p hpEq hp hs hh Y hY
  subst p
  by_cases hδ : scalarOrderWeight (M : ℝ) L 1 ^ 2 / (complexity g 1 : ℝ) < δ₀
  · have hS : (1 : ℝ) + 2 * L ≤ scalarOrderWeight (M : ℝ) L 1 := by
      have hm := mul_le_mul_of_nonneg_right hM2 (Nat.cast_nonneg L : (0 : ℝ) ≤ L)
      unfold scalarOrderWeight
      norm_num only [Nat.cast_one]
      linarith
    have hglarge := small_weight_parent_genus_large g 1 L (scalarOrderWeight (M : ℝ) L 1)
      (by omega) hL hs (by simpa only [Nat.cast_one] using hS) (hδ.trans_le hδ₀1)
    have hg2 : 2 ≤ g := by omega
    have hgenus : |genusCorrection P g 2 Y - truncationValue (formalGenus P Y 2) L (1 / (complexity g 2 : ℝ))| ≤
        H * scalarOrderWeight (M : ℝ) L 2 ^ (2 * L) / (complexity g 2 : ℝ) ^ L :=
      hhigh g 2 (by omega) (by omega) (by unfold Stable; omega) (by unfold complexity; omega) Y hY
    have hCcurrent (g' p' : ℕ) (hp' : 1 ≤ p') (hs' : Stable g' p') :
        |cuspCorrection P g' p' Y - truncationValue (formalCusp P Y p') L (1 / (complexity g' p' : ℝ))| ≤
        C * scalarOrderWeight (M : ℝ) L p' ^ (2 * L) / (complexity g' p' : ℝ) ^ L := by
      have hh' : 1 ≤ complexity g' p' := by unfold Stable complexity at *; omega
      exact hcurrent g' p' trivial hp' hs' hh' Y hY
    have hCold (g' p' q : ℕ) (hp' : 1 ≤ p') (hs' : Stable g' p') (hq : 1 ≤ q) (hqL : q < L) :
        |cuspCorrection P g' p' Y - truncationValue (formalCusp P Y p') q (1 / (complexity g' p' : ℝ))| ≤
        e q * scalarOrderWeight (M : ℝ) q p' ^ (2 * q) / (complexity g' p' : ℝ) ^ q := by
      have hh' : 1 ≤ complexity g' p' := by unfold Stable complexity at *; omega
      exact hprev q hq hqL 1 g' p' trivial hp' hs' hh' Y hY
    have hb := hsmall M hMsM g L hg2 hL Y hY hδ H C hH hC e he hgenus hCcurrent hCold
    apply hb.trans
    apply scalar_state_error_coefficient_mono
    have hsum : (∑ i ∈ Finset.range L, if 1 ≤ i then Bs ^ i * e (L - i) else 0) ≤ V := by
      apply (strict_geometric_loss_sum_le_Icc Bs hBs.le L e he).trans
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hBs.le (le_max_left Bs Bl) _) (he _)
    have hpow := pow_le_pow_left₀ hBs.le (le_max_left Bs Bl) L
    have hcoef : Ds ≤ D := by dsimp [D]; linarith
    have holdsum : 0 ≤ ∑ i ∈ Finset.range L, if 1 ≤ i then Bs ^ i * e (L - i) else 0 := by
      apply Finset.sum_nonneg
      intro i hi
      split_ifs
      · exact mul_nonneg (pow_nonneg hBs.le _) (he _)
      · exact le_rfl
    exact mul_le_mul hcoef (add_le_add (add_le_add le_rfl hsum) hpow)
      (add_nonneg (add_nonneg (add_nonneg hH hC) holdsum) (pow_nonneg hBs.le L)) hD.le
  · have hδ' : δ₀ ≤ scalarOrderWeight (M : ℝ) L 1 ^ 2 / (complexity g 1 : ℝ) := le_of_not_gt hδ
    have hb := (hlarge M hMlM g 1 L (by omega) hs hh hL Y hY hδ').2
    apply hb.trans
    apply scalar_state_error_coefficient_mono
    have hpow := pow_le_pow_left₀ hBl.le (le_max_right Bs Bl) L
    have hc1 : Cl ≤ D := by dsimp [D]; linarith
    have he1 := mul_le_mul hc1 hpow (pow_nonneg hBl.le L) hD.le
    have he2 := mul_nonneg hD.le (add_nonneg (add_nonneg hH hC) hV)
    nlinarith
end WP.HigherOrder
