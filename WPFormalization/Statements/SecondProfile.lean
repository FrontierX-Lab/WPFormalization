import WPFormalization.Marked.SecondProfileCoherence

/-! Appendix C.1: the actual second coefficient, its uniform profile remainder,
and independence of arbitrary valid finite coordinate paths. The classical
intersection model remains an explicit parameter. -/
noncomputable section
namespace WP

@[blueprint "lem:second-profile"]
theorem second_profile (P : PsiTheory) (p : ℕ) (hp : 1 ≤ p) :
    ∃ C : ℝ, 0 < C ∧ ∃ G : ℕ, ∀ g ≥ G, ∀ d : List ℕ, d.length = p →
      (d.sum : ℝ) ≤ Real.rpow (complexity g p : ℝ) (1/8 : ℝ) →
      ∀ Y ∈ Set.Icc 0 y₀,
        |profile P g d Y - (1-degreeCorrection d Y/(complexity g p : ℝ)+
          HigherOrder.secondProfile Y d/(complexity g p : ℝ)^2)| ≤
          C*((d.sum : ℝ)+1)^6/(complexity g p : ℝ)^3 := by
  exact second_profile_proof P p hp

@[blueprint "lem:second-profile"]
theorem second_profile_all_degrees (P : PsiTheory) (p : ℕ) (hp : 1 ≤ p) :
    ∃ C : ℝ, 0 < C ∧ ∃ G : ℕ, ∀ g ≥ G, ∀ d : List ℕ, d.length = p →
      ∀ Y ∈ Set.Icc 0 y₀,
        |profile P g d Y - (1-degreeCorrection d Y/(complexity g p : ℝ)+
          HigherOrder.secondProfile Y d/(complexity g p : ℝ)^2)| ≤
          C*((d.sum : ℝ)+1)^6/(complexity g p : ℝ)^3 := by
  exact second_profile_all_degrees_proof P p hp

@[blueprint "lem:second-profile"]
theorem second_profile_adjacent (P : PsiTheory) (p : ℕ) (hp : 1 ≤ p)
    (Y : ℝ) (hY : Y ∈ Set.Icc 0 y₀) (d : List ℕ) (hd : d.length = p)
    (i : ℕ) (hi : i < d.length) :
    HigherOrder.secondProfile Y (HigherOrder.raiseDegree d i)-HigherOrder.secondProfile Y d =
      -HigherOrder.secondIncrement Y i d := by
  exact second_profile_adjacent_proof P p hp Y hY d hd i hi

namespace HigherOrder

@[blueprint "lem:second-profile"]
theorem second_profile_path_independent (P : PsiTheory) (p : ℕ) (hp : 1 ≤ p)
    (Y : ℝ) (hY : Y ∈ Set.Icc 0 y₀) (v w : ℕ → List ℕ) (i j : ℕ → ℕ) (n m : ℕ)
    (hvlen : ∀ s < n, (v s).length = p) (hwlen : ∀ s < m, (w s).length = p)
    (hi : ∀ s < n, i s < (v s).length) (hj : ∀ s < m, j s < (w s).length)
    (hv : ∀ s < n, v (s+1) = raiseDegree (v s) (i s))
    (hw : ∀ s < m, w (s+1) = raiseDegree (w s) (j s))
    (hstart : v 0 = w 0) (hend : v n = w m) :
    (∑ s ∈ Finset.range n, secondIncrement Y (i s) (v s)) =
      ∑ s ∈ Finset.range m, secondIncrement Y (j s) (w s) := by
  exact second_profile_path_independent_proof P p hp Y hY v w i j n m
    hvlen hwlen hi hj hv hw hstart hend

end HigherOrder
end WP
