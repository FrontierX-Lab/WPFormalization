import WPFormalization.Critical.CutStableGenusAllocation
import WPFormalization.Critical.CutCuspLabels

/-! Exact local Gamma cusp-allocation series for every positive boundary degree. The two unstable vertex types use the original phi series; invalid low cusp allocations contribute Gamma(0)=0. -/
noncomputable section

namespace WP.Critical
open Finset

/-- The actual local Gamma cusp weights for the two unstable types and all
stable base complexities. -/
def cutLocalCuspSeries (a p:ℕ) : PowerSeries ℝ :=
  if a=0 ∧ p=1 then cutPhi01 else
  if a=0 ∧ p=2 then cutPhi02 else cutStableCuspSeries (complexity a p)

lemma cutLocalCuspSeries_coeff_gamma (a p q:ℕ) (hp:1≤p) :
    (q.factorial:ℝ)*PowerSeries.coeff q (cutLocalCuspSeries a p)=
      Real.Gamma (complexity a (p+q)) := by
  have hqf : (q.factorial:ℝ)≠0 := by exact_mod_cast Nat.factorial_ne_zero q
  unfold cutLocalCuspSeries
  split_ifs with h01 h02
  · obtain ⟨rfl,rfl⟩:=h01
    by_cases hq:2≤q
    · rw [cutPhi01_coeff_gamma q hq]
      have hc : complexity 0 (1+q)=q-1 := by unfold complexity;omega
      rw [hc,Nat.cast_sub (show 1≤q by omega),Nat.cast_one]
      field_simp
    · have hcases : q=0 ∨ q=1 := by omega
      rcases hcases with rfl|rfl <;> norm_num [cutPhi01,PowerSeries.coeff_mk,complexity,Real.Gamma_zero]
  · obtain ⟨rfl,rfl⟩:=h02
    by_cases hq:1≤q
    · rw [cutPhi02_coeff_gamma q hq]
      have hc : complexity 0 (2+q)=q := by unfold complexity;omega
      rw [hc]
      field_simp
    · have hq0:q=0 := by omega
      subst q
      norm_num [cutPhi02,PowerSeries.coeff_mk,complexity,Real.Gamma_zero]
  · have hs:Stable a p := by unfold Stable;omega
    have hh:1≤complexity a p := by unfold Stable complexity at *;omega
    rw [cutStableCuspSeries_coeff_gamma _ q hh]
    have hc : complexity a (p+q)=complexity a p+q := by unfold Stable complexity at *;omega
    rw [hc,Nat.cast_add]
    field_simp

lemma cutLocalCuspSeries_coeff_nonneg (a p:ℕ) (hp:1≤p) :
    ∀q,0≤PowerSeries.coeff q (cutLocalCuspSeries a p) := by
  intro q
  unfold cutLocalCuspSeries
  split_ifs with h01 h02
  · exact (cutPhi01_coeff_bounds q).1
  · exact (cutPhi02_coeff_bounds q).1
  · have hh:1≤complexity a p := by unfold complexity;omega
    exact cutStableCuspSeries_coeff_nonneg _ hh q

/-- The complete original labeled-cusp Gamma sum at fixed component genera. -/
lemma cutCuspLabels_gamma_series (n Q:ℕ) (a p:Fin Q→ℕ) (hp:∀i,1≤p i) :
    (∑σ:Fin n→Fin Q,∏c:Fin Q,
      Real.Gamma (complexity (a c) (p c+cutCuspHistogram σ c))) =
        (n.factorial:ℝ)*PowerSeries.coeff n (∏c:Fin Q,cutLocalCuspSeries (a c) (p c)) := by
  rw [←cutCuspLabels_series_coeff]
  apply sum_congr rfl
  intro σ hσ
  apply prod_congr rfl
  intro c hc
  exact (cutLocalCuspSeries_coeff_gamma (a c) (p c) (cutCuspHistogram σ c) (hp c)).symm

end WP.Critical
