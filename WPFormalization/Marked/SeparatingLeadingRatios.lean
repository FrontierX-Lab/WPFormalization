import WPFormalization.Marked.PrefactorRatios
import WPFormalization.Marked.DilatonRefinement
/-! The actual leading W quotients for the sphere and torus separating components.
Two genuine merging or handle prefactors are multiplied with their correct
complexity shifts; the total remainder is uniform of order h^(-3). -/
noncomputable section
namespace WP.Analysis
lemma shifted_two_prefactors_product (x y A h c d B : ℝ) (hh : 2 ≤ h)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (hB : 0 ≤ B) (hA : |A| ≤ B)
    (hx : |x-A/h| ≤ c/h^2) (hy : |y-A/(h-1)| ≤ d/(h-1)^2) :
    |x*y-A^2/h^2| ≤ (c*(B+(4*d+2*B))+B*(4*d+2*B))/h^3 := by
  have hp : 0<h := by linarith
  have hm : 0<h-1 := by linarith
  have h2 : 0<h^2 := sq_pos_of_pos hp
  have hsq : h^2 ≤ 4*(h-1)^2 := by
    have hi := pow_le_pow_left₀ hp.le (show h ≤ 2*(h-1) by linarith) 2
    nlinarith
  have hshift : |A/(h-1)-A/h| ≤ 2*B/h^2 := by
    have he : A/(h-1)-A/h=A/(h*(h-1)) := by field_simp <;> ring
    rw [he,abs_div,abs_of_pos (mul_pos hp hm)]
    calc _ ≤ B/(h*(h-1)) := div_le_div_of_nonneg_right hA (mul_pos hp hm).le
         _ ≤ _ := by
           apply (div_le_div_iff₀ (mul_pos hp hm) h2).2
           have hi : h^2 ≤ 2*h*(h-1) := by nlinarith
           nlinarith [mul_le_mul_of_nonneg_left hi hB]
  have hdim : d/(h-1)^2 ≤ 4*d/h^2 := by
    apply (div_le_div_iff₀ (sq_pos_of_pos hm) h2).2
    nlinarith [mul_le_mul_of_nonneg_left hsq hd]
  let D : ℝ := 4*d+2*B
  have hD : 0 ≤ D := by dsimp only [D];positivity
  have hy' : |y-A/h| ≤ D/h^2 := by
    calc _ ≤ |y-A/(h-1)|+|A/(h-1)-A/h| := abs_sub_le _ _ _
         _ ≤ d/(h-1)^2+2*B/h^2 := add_le_add hy hshift
         _ ≤ 4*d/h^2+2*B/h^2 := add_le_add_left hdim _
         _ = _ := by dsimp only [D];ring
  have hDy : D/h^2 ≤ D/h := by
    apply (div_le_div_iff₀ h2 hp).2
    have hi : h ≤ h^2 := by nlinarith
    exact mul_le_mul_of_nonneg_left hi hD
  have hyabs : |y| ≤ (B+D)/h := by
    calc _ = |(y-A/h)+A/h| := by congr 1;ring
         _ ≤ |y-A/h|+|A/h| := abs_add_le _ _
         _ ≤ D/h^2+B/h := add_le_add hy' (by rw [abs_div,abs_of_pos hp];exact div_le_div_of_nonneg_right hA hp.le)
         _ ≤ D/h+B/h := add_le_add_left hDy _
         _ = _ := by ring
  have he : x*y-A^2/h^2=(x-A/h)*y+(A/h)*(y-A/h) := by field_simp <;> ring
  rw [he]
  calc _ ≤ |(x-A/h)*y|+|(A/h)*(y-A/h)| := abs_add_le _ _
       _ = |x-A/h| * |y|+|A/h| * |y-A/h| := by rw [abs_mul,abs_mul]
       _ ≤ (c/h^2)*((B+D)/h)+(B/h)*(D/h^2) :=
         add_le_add (mul_le_mul hx hyabs (abs_nonneg _) (by positivity))
           (mul_le_mul (by rw [abs_div,abs_of_pos hp];exact div_le_div_of_nonneg_right hA hp.le)
             hy' (abs_nonneg _) (by positivity))
       _ = _ := by dsimp only [D];field_simp <;> ring
end WP.Analysis
namespace WP
lemma W_two_cusp_leading (P : PsiTheory) (p : ℕ) (hp : 3 ≤ p) :
    ∃ C : ℝ,0<C ∧ ∃ G : ℕ,∀ g≥G,∀ Y ∈ Set.Icc (0:ℝ) y₀,
      |W P g (p-2) Y/W P g p Y-(A Y)^2/(complexity g p:ℝ)^2| ≤ C/(complexity g p:ℝ)^3 := by
  obtain ⟨c,hc,Gc,hx⟩ := W_merge_prefactor_second_order P p (by omega)
  obtain ⟨d,hd,Gd,hy⟩ := W_merge_prefactor_second_order P (p-1) (by omega)
  obtain ⟨B,hB,hA⟩ := dilaton_A_abs_uniform
  refine ⟨c*(B+(4*d+2*B))+B*(4*d+2*B),by positivity,2+Gc+Gd,?_⟩
  intro g hg Y hY
  have hh : (2:ℝ) ≤ complexity g p := by
    exact_mod_cast (show 2 ≤ complexity g p by unfold complexity;omega)
  have hx' := hx g (by omega) Y hY
  have hy' := hy g (by omega) Y hY
  have hs : (complexity g (p-1):ℝ)=(complexity g p:ℝ)-1 := by
    have hi : complexity g p=complexity g (p-1)+1 := by unfold complexity;omega
    rw [hi,Nat.cast_add,Nat.cast_one]
    ring
  rw [show p-1-1=p-2 by omega,hs] at hy'
  have hi := Analysis.shifted_two_prefactors_product _ _ (A Y) (complexity g p) c d B
    hh hc.le hd.le hB.le (hA Y hY) hx' hy'
  have hmid : W P g (p-1) Y≠0 :=
    (W_pos P g (p-1) (by omega) (by unfold Stable;omega) Y hY).ne'
  have hpar : W P g p Y≠0 :=
    (W_pos P g p (by omega) (by unfold Stable;omega) Y hY).ne'
  have he : (W P g (p-1) Y/W P g p Y)*(W P g (p-2) Y/W P g (p-1) Y)=
      W P g (p-2) Y/W P g p Y := by field_simp
  simpa only [he] using hi
lemma W_genus_same_marking_leading (P : PsiTheory) (p : ℕ) (hp : 1 ≤ p) :
    ∃ C : ℝ,0<C ∧ ∃ G : ℕ,∀ g≥G,∀ Y ∈ Set.Icc (0:ℝ) y₀,
      |W P (g-1) p Y/W P g p Y-(A Y)^2/(complexity g p:ℝ)^2| ≤ C/(complexity g p:ℝ)^3 := by
  obtain ⟨c,hc,Gc,hx⟩ := W_handle_prefactor_second_order P p hp
  obtain ⟨d,hd,Gd,hy⟩ := W_merge_prefactor_second_order P (p+1) (by omega)
  obtain ⟨B,hB,hA⟩ := dilaton_A_abs_uniform
  refine ⟨c*(B+(4*d+2*B))+B*(4*d+2*B),by positivity,3+Gc+Gd,?_⟩
  intro g hg Y hY
  have hh : (2:ℝ) ≤ complexity g p := by
    exact_mod_cast (show 2 ≤ complexity g p by unfold complexity;omega)
  have hx' := hx g (by omega) Y hY
  have hy' := hy (g-1) (by omega) Y hY
  have hs : (complexity (g-1) (p+1):ℝ)=(complexity g p:ℝ)-1 := by
    have hi : complexity g p=complexity (g-1) (p+1)+1 := by unfold complexity;omega
    rw [hi,Nat.cast_add,Nat.cast_one]
    ring
  rw [show p+1-1=p by omega,hs] at hy'
  have hi := Analysis.shifted_two_prefactors_product _ _ (A Y) (complexity g p) c d B
    hh hc.le hd.le hB.le (hA Y hY) hx' hy'
  have hmid : W P (g-1) (p+1) Y≠0 :=
    (W_pos P (g-1) (p+1) (by omega) (by unfold Stable;omega) Y hY).ne'
  have hpar : W P g p Y≠0 :=
    (W_pos P g p hp (by unfold Stable;omega) Y hY).ne'
  have he : (W P (g-1) (p+1) Y/W P g p Y)*(W P (g-1) p Y/W P (g-1) (p+1) Y)=
      W P (g-1) p Y/W P g p Y := by field_simp
  simpa only [he] using hi
end WP
