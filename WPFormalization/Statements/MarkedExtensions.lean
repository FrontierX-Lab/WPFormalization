import WPFormalization.Marked.GenusExtensions
import WPFormalization.Statements.MarkedGenus

/-! The low-marking extensions proved after the original Section 6 estimates.
The original p≥2 and p≥1 statements remain intact. These companions record
precisely the additional marking ranges used by the later sections. -/
noncomputable section
namespace WP

@[blueprint "eq:TL23"]
theorem quadratic_profile_all_markings (P : PsiTheory) (p : ℕ) (hp : 1 ≤ p) :
    ∃ C : ℝ, 0 < C ∧ ∀ g : ℕ, 1 ≤ g → ∀ d : List ℕ, d.length = p →
    ∀ Y ∈ Set.Icc 0 y₀, 0 ≤ 1-profile P g d Y ∧
      1-profile P g d Y ≤ C*(d.sum : ℝ)*(d.sum+1)/g := by
  exact quadratic_profile_all_markings_proof P p hp

@[blueprint "eq:TL24"]
theorem marked_cusp_all (P : PsiTheory) (p : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∃ g₀ : ℕ, ∀ g ≥ g₀, ∀ Y ∈ Set.Icc 0 y₀,
      |(complexity g p : ℝ)*W P g p Y/W P g (p+1) Y - A Y| ≤ C/g := by
  exact marked_cusp_all_proof P p

@[blueprint "eq:TL27"]
theorem marked_genus_all (P : PsiTheory) (p : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∃ g₀ : ℕ, ∀ g ≥ g₀, ∀ Y ∈ Set.Icc 0 y₀,
      |W P (g-1) (p+2) Y / W P g p Y - 1| ≤ C/g := by
  exact marked_genus_all_proof P p

@[blueprint "eq:TL19"]
theorem separating_S_all_markings (P : PsiTheory) (p : ℕ) (hp : 1 ≤ p) :
    ∃ C : ℝ, 0 < C ∧ ∃ g₀ : ℕ, ∀ g ≥ g₀, ∀ Y ∈ Set.Icc 0 y₀,
      |separatingS P g p Y| ≤ C/(complexity g p : ℝ)^2 := by
  exact separatingS_all_complexity_bound P p hp

@[blueprint "eq:TL19"]
theorem separating_T_two_markings (P : PsiTheory) :
    ∃ C : ℝ, 0 < C ∧ ∃ g₀ : ℕ, ∀ g ≥ g₀, ∀ Y ∈ Set.Icc 0 y₀,
      |separatingT P g 2 Y| ≤ C/(g : ℝ)^2 := by
  exact separatingT_two_estimate P

end WP
