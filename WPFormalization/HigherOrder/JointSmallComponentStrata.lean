import WPFormalization.HigherOrder.BoundaryAffineStatus
import WPFormalization.HigherOrder.SmallThetaData
/-! Actual bounded components are constant in the free high parent degrees on each finite stratum: dimension support forces such selected high states to zero. They have genuine uniform finite-theta polynomial recipes with explicit finite head support. The actual separating inner series is exactly cut to this bounded head range. No coefficientwise positivity is asserted. -/
noncomputable section
namespace WP.HigherOrder.JointBoundary
open Set

lemma smallW_eq_representative (P : PsiTheory) (p q g B u : ℕ)
    (hB : dimension g (q + 1) ≤ B) (d : Fin p → ℕ) (e : Fin q → Fin p) (Y : ℝ) :
    smallW P Y g (u :: List.ofFn (fun j => d (e j))) =
      smallW P Y g (u :: List.ofFn (fun j => representative p B (classify p B d) (e j))) := by
  by_cases hh : ∃ j : Fin q, B < d (e j)
  · obtain ⟨j, hj⟩ := hh
    have hd : dimension g (q + 1) < (u :: List.ofFn (fun j => d (e j))).sum := by
      simp only [List.sum_cons, List.sum_ofFn]
      have he : d (e j) ≤ ∑ k : Fin q, d (e k) :=
        Finset.single_le_sum (f := fun k : Fin q => d (e k))
          (fun k hk => Nat.zero_le _) (Finset.mem_univ j)
      omega
    have hr : dimension g (q + 1) <
        (u :: List.ofFn (fun j => representative p B (classify p B d) (e j))).sum := by
      simp only [List.sum_cons, List.sum_ofFn]
      have hrep := representative_classify_high B d (e j) hj
      have he : representative p B (classify p B d) (e j) ≤
          ∑ k : Fin q, representative p B (classify p B d) (e k) :=
        Finset.single_le_sum
          (f := fun k : Fin q => representative p B (classify p B d) (e k))
          (fun k hk => Nat.zero_le _) (Finset.mem_univ j)
      omega
    have hd0 := normalized_excess P g (u :: List.ofFn (fun j => d (e j))) Y
      (by simpa only [List.length_cons, List.length_ofFn] using hd)
    have hr0 := normalized_excess P g
      (u :: List.ofFn (fun j => representative p B (classify p B d) (e j))) Y
      (by simpa only [List.length_cons, List.length_ofFn] using hr)
    simp only [smallW, hd0, hr0, mul_zero]
  · have he : (fun j : Fin q => d (e j)) =
        (fun j => representative p B (classify p B d) (e j)) := by
      funext j
      exact (representative_classify_low B d (e j) (by
        by_contra hn
        exact hh ⟨j, by omega⟩)).symm
    rw [he]

lemma smallW_eq_zero_large_head (P : PsiTheory) (g u : ℕ) (d : List ℕ) (Y : ℝ)
    (hu : dimension g (d.length + 1) < u) : smallW P Y g (u :: d) = 0 := by
  unfold smallW
  rw [normalized_excess P g (u :: d) Y (by
    simp only [List.length_cons, List.sum_cons]
    omega), mul_zero]

lemma smallW_stratum_theta_polynomials (P : PsiTheory) (p q g K B : ℕ)
    (hs : Stable g (q + 1)) (hK : complexity g (q + 1) ≤ K)
    (hB : dimension g (q + 1) ≤ B) (e : Fin q → Fin p) :
    ∃ Q : (Fin p → Option (Fin (B + 1))) → ℕ → KernelFiniteData.ThetaPolynomial ((3 * K) / 2 + 1),
      (∀ σ u, (Q σ u).totalDegree ≤ (3 * K) / 2) ∧
      (∀ σ u, dimension g (q + 1) < u → Q σ u = 0) ∧
      ∀ Y ∈ Icc (0 : ℝ) y₀, ∀ d : Fin p → ℕ, ∀ u : ℕ,
        smallW P Y g (u :: List.ofFn (fun j => d (e j))) =
          MvPolynomial.eval (fun i : Fin ((3 * K) / 2 + 2) => theta Y i.val)
            (Q (classify p B d) u) := by
  have hp (σ : Fin p → Option (Fin (B + 1))) (u : ℕ) :=
    KernelFiniteData.smallW_polynomial_in_finite_theta_data P K g
      (u :: List.ofFn (fun j => representative p B σ (e j)))
      (by simpa only [List.length_cons, List.length_ofFn] using hs) (by simp)
      (by simpa only [List.length_cons, List.length_ofFn] using hK)
  let Q : (Fin p → Option (Fin (B + 1))) → ℕ →
      KernelFiniteData.ThetaPolynomial ((3 * K) / 2 + 1) := fun σ u =>
    if u ≤ dimension g (q + 1) then Classical.choose (hp σ u) else 0
  have hdim : dimension g (q + 1) ≤ (3 * K) / 2 := by
    unfold dimension complexity Stable at *
    omega
  refine ⟨Q, ?_, ?_, ?_⟩
  · intro σ u
    dsimp [Q]
    split_ifs with hu
    · apply (Classical.choose_spec (hp σ u)).1.trans
      unfold deficit
      simp only [List.length_cons, List.length_ofFn]
      omega
    · simp
  · intro σ u hu
    simp only [Q, ite_eq_right (by omega : ¬u ≤ dimension g (q + 1))]
  · intro Y hY d u
    by_cases hu : u ≤ dimension g (q + 1)
    · dsimp only [Q]
      rw [ite_eq_left hu, smallW_eq_representative P p q g B u hB d e Y]
      exact (Classical.choose_spec (hp (classify p B d) u)).2 Y hY
    · dsimp only [Q]
      rw [ite_eq_right hu, map_zero]
      apply smallW_eq_zero_large_head
      simpa only [List.length_ofFn] using (show dimension g (q + 1) < u by omega)
end WP.HigherOrder.JointBoundary

namespace WP.HigherOrder.JointBoundary
lemma sum_range_support_cutoff {R : Type*} [AddCommMonoid R]
    (f : ℕ → R) (D n : ℕ) (hf : ∀ u, D < u → f u = 0) :
    (∑ u ∈ Finset.range n, f u) =
      ∑ u ∈ Finset.range (D + 1), if u < n then f u else 0 := by
  have hsmall : (∑ u ∈ (Finset.range n).filter (fun u => u ≤ D), f u) =
      ∑ u ∈ Finset.range n, f u := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro u hu hnot
    apply hf u
    have hn : ¬u ≤ D := by simpa only [Finset.mem_filter, hu, true_and] using hnot
    omega
  have hsets : (Finset.range n).filter (fun u => u ≤ D) =
      (Finset.range (D + 1)).filter (fun u => u < n) := by
    ext u
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  rw [← hsmall, hsets, Finset.sum_filter]

lemma sum_pair_support_cutoff {R : Type*} [AddCommMonoid R]
    (f : ℕ → R) (D N : ℕ) (hf : ∀ u, D < u → f u = 0) :
    (∑ u ∈ Finset.range (N - 1), f u) =
      ∑ u ∈ Finset.range (D + 1), if u + 2 ≤ N then f u else 0 := by
  rw [sum_range_support_cutoff f D (N - 1) hf]
  apply Finset.sum_congr rfl
  intro u hu
  simp only [show (u < N - 1) ↔ u + 2 ≤ N by omega]
end WP.HigherOrder.JointBoundary

namespace WP.HigherOrder.JointBoundary
open PowerSeries
lemma separating_kernel_finite_component_support (P : PsiTheory) (Y : ℝ)
    (j t l : ℕ) (s : ℝ) (small big : List ℕ) :
    (∑ u ∈ Finset.range (t + l - 1), C (smallW P Y j (u :: small)) *
      complexityShift s (formalProfile P Y ((t + l - 2 - u) :: big))) =
      ∑ u ∈ Finset.range (dimension j (small.length + 1) + 1),
        if u + 2 ≤ t + l then C (smallW P Y j (u :: small)) *
          complexityShift s (formalProfile P Y ((t + l - 2 - u) :: big)) else 0 := by
  apply sum_pair_support_cutoff
  intro u hu
  rw [smallW_eq_zero_large_head P j u small Y hu, map_zero, zero_mul]
end WP.HigherOrder.JointBoundary
