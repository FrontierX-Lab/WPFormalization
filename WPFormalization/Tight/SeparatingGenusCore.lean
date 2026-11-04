import WPFormalization.Tight.SeparatingScale
import WPFormalization.Critical.CutStableGenusAllocation

noncomputable section
namespace WP.TightSeparating
open Finset
open scoped BigOperators

/-- The full ordered positive-complexity allocation on the actual vertex set. -/
def gammaAllocationFin (Q N : ℕ) : ℝ :=
  ∑ l ∈ finsuppAntidiag (univ : Finset (Fin Q)) N,
    ∏ i : Fin Q, gammaWeight (l i+1)

lemma gammaAllocationFin_eq (Q N : ℕ) : gammaAllocationFin Q N = gammaAllocation Q N := by
  let f : PowerSeries ℝ := PowerSeries.mk (fun j => gammaWeight (j+1))
  have hfin : gammaAllocationFin Q N = PowerSeries.coeff N (f^Q) := by
    have he : f^Q = ∏ _i : Fin Q, f := by simp
    rw [he,PowerSeries.coeff_prod]
    simp only [gammaAllocationFin,gammaAllocation,f,PowerSeries.coeff_mk]
  have hnat : gammaAllocation Q N = PowerSeries.coeff N (f^Q) := by
    have he : f^Q = ∏ _i ∈ range Q, f := by simp
    rw [he,PowerSeries.coeff_prod]
    simp only [gammaAllocationFin,gammaAllocation,f,PowerSeries.coeff_mk]
  exact hfin.trans hnat.symm

/-- A genuine stable genus allocation retains all its Gamma/square-root factors
and injects into the full positive-complexity sum; only parity is discarded. -/
lemma stable_genus_gamma_majorant {Q N : ℕ} (p : Fin Q → ℕ)
    (s : Finset (Fin Q → ℕ))
    (hs : ∀ a ∈ s, (∀ i, Stable (a i) (p i)) ∧
      (∑ i : Fin Q, complexity (a i) (p i)) = N+Q) :
    (∑ a ∈ s, ∏ i : Fin Q, gammaWeight (complexity (a i) (p i))) ≤
      gammaAllocation Q N := by
  classical
  let weight : (Fin Q →₀ ℕ) → ℝ := fun l =>
    ∏ i : Fin Q, gammaWeight (l i+1)
  have hinj : Set.InjOn (Critical.cutStableGenusAllocation p) s := by
    intro a ha b hb he
    exact Critical.cutStableGenusAllocation_inj p a b (hs a ha).1 (hs b hb).1 he
  have hsub : s.image (Critical.cutStableGenusAllocation p) ⊆ finsuppAntidiag univ N := by
    intro l hl
    obtain ⟨a,ha,rfl⟩ := mem_image.mp hl
    exact Critical.cutStableGenusAllocation_mem p a (hs a ha).1 (hs a ha).2
  have hnonneg (l : Fin Q →₀ ℕ) : 0 ≤ weight l :=
    prod_nonneg (fun i _ => (gammaWeight_pos _ (by omega)).le)
  calc
    _ = ∑ a ∈ s, weight (Critical.cutStableGenusAllocation p a) := by
      apply sum_congr rfl
      intro a ha
      dsimp only [weight]
      apply prod_congr rfl
      intro i hi
      rw [Critical.cutStableGenusAllocation_apply]
      have hstable := (hs a ha).1 i
      have hp : 1 ≤ complexity (a i) (p i) := by
        unfold Stable at hstable
        unfold complexity
        omega
      rw [Nat.sub_add_cancel hp]
    _ = ∑ l ∈ s.image (Critical.cutStableGenusAllocation p), weight l := (sum_image hinj).symm
    _ ≤ ∑ l ∈ finsuppAntidiag univ N, weight l :=
      sum_le_sum_of_subset_of_nonneg hsub (fun l _ _ => hnonneg l)
    _ = _ := gammaAllocationFin_eq Q N

/-- The original inverse H^(Q-1) rate for any actual finite family of stable
genus assignments. Constants are independent of every component genus. -/
lemma stable_genus_gamma_rate (Q H : ℕ) (hQ : 2 ≤ Q) (hH : 2*Q ≤ H)
    (p : Fin Q → ℕ) (s : Finset (Fin Q → ℕ))
    (hs : ∀ a ∈ s, (∀ i, Stable (a i) (p i)) ∧
      (∑ i : Fin Q, complexity (a i) (p i)) = H) :
    (∑ a ∈ s, ∏ i : Fin Q, gammaWeight (complexity (a i) (p i))) / gammaWeight H ≤
      (Real.sqrt (Q : ℝ)*(3 : ℝ)^Q*(2 : ℝ)^(Q-1)) / (H : ℝ)^(Q-1) := by
  have he : H-Q+Q=H := Nat.sub_add_cancel (by omega)
  have hm := stable_genus_gamma_majorant (N := H-Q) p s (fun a ha => by simpa only [he] using hs a ha)
  exact (div_le_div_of_nonneg_right hm (gammaWeight_pos H (by omega)).le).trans
    (gamma_allocation_genus_rate Q H hQ hH)

end WP.TightSeparating
