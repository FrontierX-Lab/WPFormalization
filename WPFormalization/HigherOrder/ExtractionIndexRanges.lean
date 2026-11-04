import WPFormalization.HigherOrder.CanonicalExtractionStatement

/-! Appendix D.3 and D.4, with their original frequency ranges.  The full
canonical extraction theorem was proved independently of these lemmas, so its
zero-order specialization supplies another proof of both stated estimates. -/
noncomputable section
namespace WP.HigherOrder

theorem extraction_zero_order (P : PsiTheory) (p : ℕ) (hp : 1 ≤ p) :
    ∃ C H : ℝ, 0 < C ∧ 0 < H ∧
      ∀ g k : ℕ, H ≤ (complexity g p : ℝ) →
        |realCoeff (iteratedDeriv p (Phi P g)) k / extractionQ g p k - 1| ≤
          C / (complexity g p : ℝ) := by
  obtain ⟨C, B, c, H, hC, hB, hc, hH, _, _, _, herror, _⟩ :=
    canonical_expansion P p hp
  refine ⟨C * B, H, mul_pos hC hB, hH, ?_⟩
  intro g k hg
  have hzero : (0 : ℝ) ≤ c * Real.sqrt (complexity g p) :=
    mul_nonneg hc.le (Real.sqrt_nonneg _)
  have he := herror g k 0 hg (by simpa only [Nat.cast_zero] using hzero)
  simpa using he

/- Lemma D.3: the original coefficient estimate, uniformly in the large-index
range.  The threshold and constant precede both genus and coefficient index. -/
@[blueprint "lem:large-indices"]
theorem extraction_large_indices (P : PsiTheory) (p : ℕ) (hp : 1 ≤ p) :
    ∃ C H : ℝ, 0 < C ∧ 0 < H ∧
      ∀ g k : ℕ, H ≤ (complexity g p : ℝ) →
        (complexity g p : ℝ) ^ (1 / 4 : ℝ) ≤ (k : ℝ) →
        |realCoeff (iteratedDeriv p (Phi P g)) k / extractionQ g p k - 1| ≤
          C / (complexity g p : ℝ) := by
  obtain ⟨C, H, hC, hH, he⟩ := extraction_zero_order P p hp
  exact ⟨C, H, hC, hH, fun g k hg _ => he g k hg⟩

/- Lemma D.4: the same original estimate uniformly in the entire small-index
range, including the actual coefficient at index zero. -/
@[blueprint "lem:small-indices"]
theorem extraction_small_indices (P : PsiTheory) (p : ℕ) (hp : 1 ≤ p) :
    ∃ C H : ℝ, 0 < C ∧ 0 < H ∧
      ∀ g k : ℕ, H ≤ (complexity g p : ℝ) →
        (k : ℝ) ≤ (complexity g p : ℝ) ^ (1 / 4 : ℝ) →
        |realCoeff (iteratedDeriv p (Phi P g)) k / extractionQ g p k - 1| ≤
          C / (complexity g p : ℝ) := by
  obtain ⟨C, H, hC, hH, he⟩ := extraction_zero_order P p hp
  exact ⟨C, H, hC, hH, fun g k hg _ => he g k hg⟩

end WP.HigherOrder
