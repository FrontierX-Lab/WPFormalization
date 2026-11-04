import WPFormalization.HigherOrder.OrderWeights
import WPFormalization.Marked.UniformTopologyTails
/-! The actual KdV central tail in the small-weight remainder domain.
The proved uniform C.5 tail estimate is instantiated with its full growing-marking
range. The small-weight geometry supplies every cutoff and converts the result
to the true S_L^(2L)/h^L scale. No remainder hypothesis is used. -/
noncomputable section
namespace WP.HigherOrder
open Set

lemma scalar_small_weight_kdv_geometry (M : ℝ) (hM : 2 ≤ M) (g p L : ℕ)
    (hp : 2 ≤ p) (hL : 1 ≤ L) (hh : 0 < (complexity g p : ℝ))
    (hsmall : scalarOrderWeight M L p ^ 2 / (complexity g p : ℝ) < 1) :
    2 ≤ g ∧ L ≤ g + 1 ∧ 2 * L ≤ complexity g p ∧
      (p : ℝ) ≤ Real.sqrt (complexity g p : ℝ) ∧
      (L : ℝ) ≤ Real.sqrt (complexity g p : ℝ) := by
  let S := scalarOrderWeight M L p
  have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hLR : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hMmul := mul_le_mul_of_nonneg_right hM (Nat.cast_nonneg L : (0 : ℝ) ≤ L)
  have hS : (p : ℝ) + 2 * L ≤ S := by dsimp [S, scalarOrderWeight]; linarith
  have hS0 : 0 ≤ S := by linarith
  have hs2 : S ^ 2 < (complexity g p : ℝ) := (div_lt_one hh).mp hsmall
  have hcomp : (complexity g p : ℝ) = 2 * (g : ℝ) + p - 2 := by
    unfold complexity
    rw [Nat.cast_sub (by omega : 2 ≤ 2 * g + p)]
    push_cast
    ring
  have hSp : (p : ℝ) ≤ S := by linarith
  have hSL : (L : ℝ) ≤ S := by linarith
  have hS1 : 1 ≤ S := by linarith
  have hSle : S ≤ S ^ 2 := by nlinarith
  have h2L : 2 * (L : ℝ) ≤ complexity g p := by linarith
  have htwoNat : 2 * L ≤ complexity g p := by exact_mod_cast h2L
  have hSsqLower : ((p : ℝ) + 2 * L) ^ 2 ≤ S ^ 2 :=
    pow_le_pow_left₀ (by positivity) hS 2
  have hg2 : 2 ≤ g := by
    by_contra hn
    have hgR : (g : ℝ) ≤ 1 := by exact_mod_cast (show g ≤ 1 by omega)
    nlinarith [sq_nonneg ((p : ℝ) + 2 * L)]
  have hLg : L ≤ g + 1 := by
    have hLRg : (L : ℝ) ≤ (g : ℝ) + 1 := by
      nlinarith [sq_nonneg ((p : ℝ) + 2 * L - 1)]
    exact_mod_cast hLRg
  refine ⟨hg2, hLg, htwoNat, ?_, ?_⟩
  · apply (Real.le_sqrt (Nat.cast_nonneg p) hh.le).2
    exact (pow_le_pow_left₀ (Nat.cast_nonneg p) hSp 2).trans hs2.le
  · apply (Real.le_sqrt (Nat.cast_nonneg L) hh.le).2
    exact (pow_le_pow_left₀ (Nat.cast_nonneg L) hSL 2).trans hs2.le

lemma kdv_central_tail_small_weight_uniform (P : PsiTheory) :
    ∃ C B δ₀ : ℝ, 0 < C ∧ 0 < B ∧ 0 < δ₀ ∧ δ₀ ≤ 1 ∧
      ∀ M : ℝ, 2 ≤ M → ∀ g p L : ℕ, 2 ≤ p → 1 ≤ L →
      0 < (complexity g p : ℝ) →
      scalarOrderWeight M L p ^ 2 / (complexity g p : ℝ) < δ₀ →
      ∀ Y ∈ Icc (0 : ℝ) y₀,
      |markedSplitLossTail P g p 2 L Y| ≤
        C * B ^ L * scalarOrderWeight M L p ^ (2 * L) / (complexity g p : ℝ) ^ L := by
  obtain ⟨C, B, hC, hB, H, ht⟩ := uniform_topology_tail_two_markings P 1 (by norm_num) 2 (Or.inr rfl)
  let δ₀ : ℝ := 1 / ((H : ℝ) + 1)
  have hδ : 0 < δ₀ := by dsimp [δ₀]; positivity
  have hδ1 : δ₀ ≤ 1 := by
    dsimp [δ₀]
    apply (div_le_one (by positivity : (0 : ℝ) < (H : ℝ) + 1)).2
    linarith [Nat.cast_nonneg (α := ℝ) H]
  refine ⟨C, B, δ₀, hC, hB, hδ, hδ1, ?_⟩
  intro M hM g p L hp hL hh hsmall Y hY
  obtain ⟨hg2, hLg, h2L, hpRoot, hLRoot⟩ :=
    scalar_small_weight_kdv_geometry M hM g p L hp hL hh (hsmall.trans_le hδ1)
  let S := scalarOrderWeight M L p
  have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hLR : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hMmul := mul_le_mul_of_nonneg_right hM (Nat.cast_nonneg L : (0 : ℝ) ≤ L)
  have hS : (p : ℝ) + 2 * L ≤ S := by dsimp [S, scalarOrderWeight]; linarith
  have hS1 : 1 ≤ S := by linarith
  have hSsq : 1 ≤ S ^ 2 := by nlinarith
  have hlargeR : (H : ℝ) ≤ complexity g p := by
    have hprod : S ^ 2 * ((H : ℝ) + 1) < complexity g p := by
      simpa only [one_mul] using (div_lt_div_iff₀ hh (by positivity : (0 : ℝ) < (H : ℝ) + 1)).mp hsmall
    nlinarith [Nat.cast_nonneg (α := ℝ) H]
  have hlarge : H ≤ complexity g p := by exact_mod_cast hlargeR
  have htail := ht g p hp hlarge (by simpa using hpRoot) L hL hLRoot Y hY
  have hnonneg : 0 ≤ markedSplitLossTail P g p 2 L Y :=
    Finset.sum_nonneg (fun j _ => markedSplitLossTailGenus_nonneg P g p 2 L j hg2 hp (Or.inr rfl) Y hY)
  rw [abs_of_nonneg hnonneg]
  apply htail.trans
  have hbase : (p : ℝ) + L ≤ S ^ 2 := by
    nlinarith [sq_nonneg S]
  have hb : B * ((p : ℝ) + L) / (complexity g p : ℝ) ≤
      B * S ^ 2 / (complexity g p : ℝ) :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hbase hB.le) hh.le
  have hpw := pow_le_pow_left₀ (by positivity : 0 ≤ B * ((p : ℝ) + L) / (complexity g p : ℝ)) hb L
  convert mul_le_mul_of_nonneg_left hpw hC.le using 1
  rw [div_pow, mul_pow, ← pow_mul]
  ring
end WP.HigherOrder
