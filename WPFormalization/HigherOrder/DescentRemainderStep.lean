import WPFormalization.HigherOrder.DescentCoefficientBounds
import WPFormalization.HigherOrder.DescentRemainderAlgebra
import WPFormalization.HigherOrder.CuspRemainderStep
import WPFormalization.HigherOrder.SmallWeightRegion
/-! The genuine one-marking genus step in the C.3 induction. C.4 supplies all known coefficient bounds; the true C.6 estimate supplies the actual inverse-cusp domain. Cross multiplication leaves a single exponential convolution of the actual cusp induction errors and the current two-marking genus error. Constants precede all order, genus and physical parameter choices. This step does not assert the complete recursive remainder target. -/
set_option maxHeartbeats 800000
noncomputable section
namespace WP.HigherOrder
open Set PowerSeries

lemma descent_scalar_weight_cap (M : ℝ) (hM : 2 ≤ M) (p q L : ℕ)
    (hp : p ≤ 3) (hq : q ≤ L) :
    scalarOrderWeight M q p ^ (2 * q) ≤
      Real.exp 6 * scalarOrderWeight M L 1 ^ (2 * q) := by
  have hM0 : 0 ≤ M := by linarith
  have hleft : scalarOrderWeight M q p ≤ (1 : ℝ) + M * (q + 1) + 2 := by
    have hpR : (p : ℝ) ≤ 3 := by exact_mod_cast hp
    unfold scalarOrderWeight
    linarith
  have hcap : scalarOrderWeight M q 1 ≤ scalarOrderWeight M L 1 := by
    unfold scalarOrderWeight
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (by exact_mod_cast hq) hM0)
  calc
    _ ≤ ((1 : ℝ) + M * (q + 1) + 2) ^ (2 * q) :=
      pow_le_pow_left₀ (by unfold scalarOrderWeight; positivity) hleft _
    _ ≤ Real.exp 6 * scalarOrderWeight M q 1 ^ (2 * q) := by
      simpa only [Nat.cast_one] using ComplexCanonical.scalar_weight_succ_offset_pow M (by linarith) q 1 (by omega)
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by unfold scalarOrderWeight; positivity) hcap _) (Real.exp_pos _).le

lemma descent_remainder_summand_scaled (a R C B E S h : ℝ) (L i : ℕ)
    (hi : i < L) (hC : 0 ≤ C) (hB : 0 ≤ B) (hE : 0 ≤ E)
    (hS : 0 ≤ S) (hh : 0 < h)
    (ha : |a| ≤ C * B ^ i * S ^ (2 * i))
    (hR : |R| ≤ Real.exp 6 * E * S ^ (2 * (L - i)) / h ^ (L - i)) :
    |a| * |1 / h| ^ i * |R| ≤
      (S ^ (2 * L) / h ^ L) * (Real.exp 6 * C * B ^ i * E) := by
  have hc : |a| * |1 / h| ^ i ≤ C * B ^ i * S ^ (2 * i) / h ^ i := by
    rw [abs_of_pos (one_div_pos.mpr hh)]
    convert mul_le_mul_of_nonneg_right ha (pow_nonneg (one_div_pos.mpr hh).le i) using 1 <;>
      rw [div_pow, one_pow] <;> ring
  apply (mul_le_mul hc hR (abs_nonneg _) (by positivity)).trans_eq
  have hSp : S ^ (2 * i) * S ^ (2 * (L - i)) = S ^ (2 * L) := by
    rw [← pow_add]
    congr 1
    omega
  have hhp : h ^ i * h ^ (L - i) = h ^ L := by rw [← pow_add, Nat.add_sub_of_le hi.le]
  calc
    _ = (Real.exp 6 * C * B ^ i * E) *
        (S ^ (2 * i) * S ^ (2 * (L - i))) / (h ^ i * h ^ (L - i)) := by ring
    _ = _ := by rw [hSp, hhp]; ring

lemma actual_genus_one_uniform_remainder_step (P : PsiTheory) :
    ∃ D B M₀ δ₀ : ℝ, 0 < D ∧ 0 < B ∧ 2 ≤ M₀ ∧ 0 < δ₀ ∧ δ₀ ≤ 1 ∧
      ∀ M : ℝ, M₀ ≤ M → ∀ g L : ℕ, 2 ≤ g → 1 ≤ L →
      ∀ Y ∈ Icc (0 : ℝ) y₀,
      scalarOrderWeight M L 1 ^ 2 / (complexity g 1 : ℝ) < δ₀ →
      ∀ H : ℝ, 0 ≤ H → ∀ E : ℕ → ℝ, (∀ q, 0 ≤ E q) →
      (|genusCorrection P g 2 Y - truncationValue (formalGenus P Y 2) L (1 / (complexity g 2 : ℝ))| ≤
        H * scalarOrderWeight M L 2 ^ (2 * L) / (complexity g 2 : ℝ) ^ L) →
      (∀ q : ℕ, 1 ≤ q → q ≤ L →
        |cuspCorrection P g 1 Y - truncationValue (formalCusp P Y 1) q (1 / (complexity g 1 : ℝ))| ≤
          E q * scalarOrderWeight M q 1 ^ (2 * q) / (complexity g 1 : ℝ) ^ q ∧
        |cuspCorrection P (g - 1) 3 Y - truncationValue (formalCusp P Y 3) q (1 / (complexity g 1 : ℝ))| ≤
          E q * scalarOrderWeight M q 3 ^ (2 * q) / (complexity g 1 : ℝ) ^ q) →
      |genusCorrection P g 1 Y - truncationValue (formalGenus P Y 1) L (1 / (complexity g 1 : ℝ))| ≤
        D * (H + (∑ i ∈ Finset.range L, B ^ i * E (L - i)) + B ^ L) *
          scalarOrderWeight M L 1 ^ (2 * L) / (complexity g 1 : ℝ) ^ L := by
  obtain ⟨C, B, M₀, hC, hB, hM₀, hcoef⟩ := descent_formal_coefficients_uniform P
  obtain ⟨X, hX, hcusp⟩ := cuspCorrection_abs_uniform
  obtain ⟨δ₀, hδ₀, hδ₀1, hlower⟩ := cusp_inverse_small_weight_uniform P
  let D := 2 * X * Real.exp 6 + 2 * X * Real.exp 2 * C + 4 * Real.exp 6 * C + 1
  have hD : 0 < D := by dsimp [D]; positivity
  have hB0 : 0 < B := by linarith
  refine ⟨D, 2 * B, M₀, δ₀, hD, by positivity, hM₀, hδ₀, hδ₀1, ?_⟩
  intro M hM g L hg hL Y hY hsmall H hH E hE hgenus hc
  have hM2 : 2 ≤ M := hM₀.trans hM
  have hM0 : 0 ≤ M := by linarith
  let h : ℝ := complexity g 1
  let S := scalarOrderWeight M L 1
  let V := ∑ i ∈ Finset.range L, (2 * B) ^ i * E (L - i)
  have hh : 0 < h := by dsimp [h]; exact_mod_cast (show 0 < complexity g 1 by unfold complexity; omega)
  have hS : 0 < S := by dsimp [S, scalarOrderWeight]; positivity
  have hLR : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hMS : 2 * (L : ℝ) ≤ S := by
    have hm := mul_le_mul_of_nonneg_right hM2 (Nat.cast_nonneg L : (0 : ℝ) ≤ L)
    dsimp [S, scalarOrderWeight]
    linarith
  have hsmall1 : S ^ 2 / h ≤ 1 := hsmall.le.trans hδ₀1
  have hhalf : 1 / 2 ≤ cuspCorrection P g 1 Y :=
    (hlower M h hM2 hh 1 L (by omega) hL hsmall g 1 (by omega) (by dsimp [h]; linarith) (by omega) Y hY).1
  have hcomp : (complexity g 2 : ℝ) = h + 1 := by
    have he : complexity g 2 = complexity g 1 + 1 := by unfold complexity; omega
    rw [he, Nat.cast_add, Nat.cast_one]
  have hgscaled : |genusCorrection P g 2 Y - truncationValue (formalGenus P Y 2) L (1 / (h + 1))| ≤
      Real.exp 6 * H * S ^ (2 * L) / h ^ L := by
    rw [hcomp] at hgenus
    apply hgenus.trans
    calc
      _ ≤ H * (Real.exp 6 * S ^ (2 * L)) / (h + 1) ^ L :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left (descent_scalar_weight_cap M hM2 2 L L (by omega) le_rfl) hH) (by positivity)
      _ ≤ H * (Real.exp 6 * S ^ (2 * L)) / h ^ L :=
        div_le_div_of_nonneg_left (by positivity) (pow_pos hh _) (pow_le_pow_left₀ hh.le (by linarith) _)
      _ = _ := by ring
  let e : ℕ → ℝ := fun i => C * B ^ i
  have he : ∀ i : ℕ, 0 ≤ e i := by intro i; dsimp [e]; positivity
  have hknown (i : ℕ) (hi : i < L) := hcoef M hM L i hi.le Y hY
  have hshift := shift_truncation_remainder_bound (formalGenus P Y 2) e L hL (-1) S h 1
    (by norm_num; exact_mod_cast hL) hMS hh hsmall1 le_rfl he (fun i hi => (hknown i hi).1)
  norm_num only [sub_neg_eq_add, sub_neg_eq_add] at hshift
  have hsumknown : (∑ i ∈ Finset.range L, e i / ((L - i).factorial : ℝ)) ≤ C * (2 * B) ^ L := by
    dsimp [e]
    simp_rw [mul_div_assoc]
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left
      ((finite_exp_geometric_convolution_bound B hB0.le L).trans_eq (by rw [max_eq_left hB])) hC.le
  have hshifted : |genusCorrection P g 2 Y - truncationValue (complexityShift (-1) (formalGenus P Y 2)) L (1 / h)| ≤
      (S ^ (2 * L) / h ^ L) * (Real.exp 6 * H + Real.exp 2 * C * (2 * B) ^ L) := by
    apply (abs_sub_le _ _ _).trans
    apply (add_le_add hgscaled (hshift.trans (mul_le_mul_of_nonneg_left hsumknown (by positivity)))).trans_eq
    ring
  have hcusps (q : ℕ) (hq : 1 ≤ q) (hql : q ≤ L) :
      |cuspCorrection P g 1 Y - truncationValue (formalCusp P Y 1) q (1 / h)| ≤
        Real.exp 6 * E q * S ^ (2 * q) / h ^ q ∧
      |cuspCorrection P (g - 1) 3 Y - truncationValue (formalCusp P Y 3) q (1 / h)| ≤
        Real.exp 6 * E q * S ^ (2 * q) / h ^ q := by
    obtain ⟨hc1, hc3⟩ := hc q hq hql
    constructor
    · apply hc1.trans
      convert div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (descent_scalar_weight_cap M hM2 1 q L (by omega) hql) (hE q))
        (pow_nonneg hh.le q) using 1 <;> ring
    · apply hc3.trans
      convert div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (descent_scalar_weight_cap M hM2 3 q L (by omega) hql) (hE q))
        (pow_nonneg hh.le q) using 1 <;> ring
  have hterm (i : ℕ) (hi : i ∈ Finset.range L) (a R : ℝ)
      (ha : |a| ≤ e i * S ^ (2 * i))
      (hR : |R| ≤ Real.exp 6 * E (L - i) * S ^ (2 * (L - i)) / h ^ (L - i)) :
      |a| * |1 / h| ^ i * |R| ≤
        (S ^ (2 * L) / h ^ L) * (Real.exp 6 * C * (2 * B) ^ i * E (L - i)) := by
    have hit : i < L := Finset.mem_range.mp hi
    have ht := descent_remainder_summand_scaled a R C B (E (L - i)) S h L i hit hC.le hB0.le (hE _) hS.le hh ha hR
    apply ht.trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hB0.le (by linarith : B ≤ 2 * B) i) (by positivity)) (hE _)
  have hsum (f : Series) (x : ℝ) (g : Series)
      (hf : ∀ i < L, |PowerSeries.coeff i f| ≤ e i * S ^ (2 * i))
      (hx : ∀ q : ℕ, 1 ≤ q → q ≤ L → |x - truncationValue g q (1 / h)| ≤
        Real.exp 6 * E q * S ^ (2 * q) / h ^ q) :
      (∑ i ∈ Finset.range L, |PowerSeries.coeff i f| * |1 / h| ^ i * |x - truncationValue g (L - i) (1 / h)|) ≤
        (S ^ (2 * L) / h ^ L) * (Real.exp 6 * C * V) := by
    calc
      _ ≤ ∑ i ∈ Finset.range L, (S ^ (2 * L) / h ^ L) * (Real.exp 6 * C * (2 * B) ^ i * E (L - i)) := by
        apply Finset.sum_le_sum
        intro i hi
        have hiL : i < L := Finset.mem_range.mp hi
        exact hterm i hi _ _ (hf i hiL) (hx (L - i) (by omega) (by omega))
      _ = _ := by dsimp [V]; simp_rw [mul_assoc]; rw [← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
  have hsum3 := hsum (complexityShift (-1) (formalGenus P Y 2)) (cuspCorrection P (g - 1) 3 Y) (formalCusp P Y 3)
    (fun i hi => (hknown i hi).2.1) (fun q hq hql => (hcusps q hq hql).2)
  have hsum1 := hsum (formalGenus P Y 1) (cuspCorrection P g 1 Y) (formalCusp P Y 1)
    (fun i hi => (hknown i hi).2.2.2.2) (fun q hq hql => (hcusps q hq hql).1)
  have hXactual : |cuspCorrection P (g - 1) 3 Y| ≤ X :=
    hcusp P (g - 1) 3 (by omega) (by unfold Stable; omega) Y hY
  have hv0 : 0 ≤ V := Finset.sum_nonneg (fun i hi => mul_nonneg (by positivity) (hE _))
  have hbound := actual_genus_one_cross_remainder_bound P g hg Y hY hhalf L (1 / h)
  apply hbound.trans
  apply (mul_le_mul_of_nonneg_left (add_le_add
    (add_le_add (mul_le_mul hshifted hXactual (abs_nonneg _) (by positivity)) hsum3) hsum1) (by norm_num)).trans
  have hscale : 0 ≤ S ^ (2 * L) / h ^ L := by positivity
  have hcoeff : 2 * (X * (Real.exp 6 * H + Real.exp 2 * C * (2 * B) ^ L) + 2 * Real.exp 6 * C * V) ≤
      D * (H + V + (2 * B) ^ L) := by
    have hp1 : 0 ≤ 2 * X * Real.exp 6 := by positivity
    have hp2 : 0 ≤ 2 * X * Real.exp 2 * C := by positivity
    have hp3 : 0 ≤ 4 * Real.exp 6 * C := by positivity
    have h1 : 2 * X * Real.exp 6 ≤ D := by dsimp [D]; linarith
    have h2 : 2 * X * Real.exp 2 * C ≤ D := by dsimp [D]; linarith
    have h3 : 4 * Real.exp 6 * C ≤ D := by dsimp [D]; linarith
    have hh1 := mul_le_mul_of_nonneg_right h1 hH
    have hh2 := mul_le_mul_of_nonneg_right h2 (pow_nonneg (by positivity : 0 ≤ 2 * B) L)
    have hh3 := mul_le_mul_of_nonneg_right h3 hv0
    nlinarith only [hh1, hh2, hh3]
  convert mul_le_mul_of_nonneg_left hcoeff hscale using 1 <;> ring
end WP.HigherOrder
