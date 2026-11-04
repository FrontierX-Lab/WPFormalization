import WPFormalization.Intersection.StateMaxima
import WPFormalization.Weighted.Clipping
/-! The actual clipped ratio maxima, specialized from the certified finite-state
construction. These are maxima of the original ratio and the original clipped
weight, with attaining states and parameters and a separate complexity-zero
value. -/
noncomputable section
open Set

namespace WP
noncomputable def clippedComplexityMaximum (P : PsiTheory) (c : ℝ) (h : ℕ) : ℝ :=
  ratioComplexityMaximum P (clippedWeight c) h

lemma clippedComplexityMaximum_zero (P : PsiTheory) (c : ℝ) :
    clippedComplexityMaximum P c 0 = 0 := ratioComplexityMaximum_zero P _

lemma clippedComplexityMaximum_attained (P : PsiTheory) (c : ℝ)
    (h : ℕ) (hh : 1 ≤ h) :
    ∃ g : ℕ, ∃ d : List ℕ, 1 ≤ d.length ∧ Stable g d.length ∧
      d.sum ≤ dimension g d.length ∧ complexity g d.length = h ∧
      ∃ Y ∈ Icc (0:ℝ) y₀,
        clippedComplexityMaximum P c h = ratio P g d Y / clippedWeight c d := by
  obtain ⟨q,hq,Ymax,he⟩ := ratioComplexityMaximum_attained P (clippedWeight c) h hh
  exact ⟨q.1,q.2,hq.1,hq.2.1,hq.2.2.1,hq.2.2.2,Ymax,Ymax.property,he⟩

lemma clippedComplexityMaximum_quotient_bound (P : PsiTheory) (c : ℝ)
    (g : ℕ) (d : List ℕ) (hn : 1 ≤ d.length) (hs : Stable g d.length)
    (hd : d.sum ≤ dimension g d.length) (Y : ℝ) (hY : Y ∈ Icc 0 y₀) :
    ratio P g d Y / clippedWeight c d ≤
      clippedComplexityMaximum P c (complexity g d.length) := by
  exact ratioComplexityMaximum_bounds P (clippedWeight c) (complexity g d.length)
    (g,d) ⟨hn,hs,hd,rfl⟩ ⟨Y,hY⟩

lemma clippedComplexityMaximum_bound (P : PsiTheory) (c : ℝ)
    (g : ℕ) (d : List ℕ) (hn : 1 ≤ d.length) (hs : Stable g d.length)
    (hd : d.sum ≤ dimension g d.length) (Y : ℝ) (hY : Y ∈ Icc 0 y₀) :
    ratio P g d Y ≤
      clippedComplexityMaximum P c (complexity g d.length) * clippedWeight c d := by
  exact ratio_le_complexityMaximum_mul P (clippedWeight c) (complexity g d.length)
    (g,d) ⟨hn,hs,hd,rfl⟩ ⟨Y,hY⟩ (clippedWeight_pos c d)
end WP
