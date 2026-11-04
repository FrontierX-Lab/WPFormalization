import WPFormalization.HigherOrder.SecondKernelSum
import WPFormalization.Marked.SecondDegreeGrowth

/-! The actual first and second kernel coefficients have uniform cubic errors after the dimension cutoff. -/

noncomputable section
open Set

noncomputable section
open Set
namespace WP
lemma second_leading_adjacent_prefix_uniform (p : ℕ) :
    ∃ C : ℝ,0<C ∧ ∀ h : ℝ,1 ≤ h → ∀ t : ℕ,∀ d : List ℕ,(t::d).length=p →
      ∀ N : ℕ,h/2 ≤ (N:ℝ)+1 → ∀ Y∈Icc (0:ℝ) y₀,
      |(∑ l∈Finset.range N,(A Y/h)*(weight Y l*zeroCountLayer t d l))-
        (degreeCorrection ((t+1)::d) Y-degreeCorrection (t::d) Y)/h| ≤
        C*(((t::d).sum:ℝ)+1)^5/h^3 := by
  obtain ⟨M,hM,hA⟩ := dilaton_A_abs_uniform
  obtain ⟨T,hT,hprefix⟩ := Analysis.weighted_polynomial_prefix_error_uniform 1 2
  let K : ℝ := (p:ℝ)+4
  have hK : 0<K := by dsimp [K];positivity
  refine ⟨4*M*K*T,by positivity,?_⟩
  intro h hh t d hd N hN Y hY
  have hhp : 0<h := lt_of_lt_of_le zero_lt_one hh
  have hnp : 0<(N:ℝ)+1 := by positivity
  let D : ℝ := ((t::d).sum:ℝ)+1
  have hD : 1 ≤ D := by dsimp [D];linarith [show (0:ℝ) ≤ (t::d).sum from Nat.cast_nonneg _]
  have hD0 : 0 ≤ D := le_trans zero_le_one hD
  have hcount (l : ℕ) : zeroCountLayer t d l ≤ K*(((t::d).sum:ℝ)+l+1) := by
    have he := zeroCountLayer_polynomial_bound t l d
    have hlen : (d.length:ℝ)+5=K := by
      dsimp [K]
      exact_mod_cast (show d.length+5=p+4 by simpa only [List.length_cons] using congrArg (fun n : ℕ => n+4) hd)
    rwa [hlen] at he
  let f (l : ℕ) : ℝ := (A Y/h)*zeroCountLayer t d l
  have hpoint (l : ℕ) : |f l| ≤ (M*K/h)*(((t::d).sum:ℝ)+l+1)^1 := by
    dsimp [f]
    rw [abs_mul,abs_div,abs_of_pos hhp,abs_of_nonneg (zeroCountLayer_nonneg t d l),pow_one]
    have hm := mul_le_mul (div_le_div_of_nonneg_right (hA Y hY) hhp.le) (hcount l)
      (zeroCountLayer_nonneg t d l) (by positivity : 0 ≤ M/h)
    convert hm using 1 <;> simp only [List.sum_cons,Nat.cast_add] <;> ring
  have hfull : HasSum (fun l : ℕ => weight Y l*f l)
      ((degreeCorrection ((t+1)::d) Y-degreeCorrection (t::d) Y)/h) := by
    have he := degreeCorrection_adjacent_hasSum Y hY t d h
    convert he using 1
    funext l
    dsimp [f]
    ring
  have he := hprefix Y hY (t::d).sum (M*K/h) (by positivity) f _ hpoint hfull N
  simp only [pow_one] at he
  have hsum : (∑ l∈Finset.range N,(A Y/h)*(weight Y l*zeroCountLayer t d l))=
      ∑ l∈Finset.range N,weight Y l*f l := by
    apply Finset.sum_congr rfl
    intro l hl
    dsimp [f]
    ring
  rw [hsum]
  have hden : h^3 ≤ 4*(h*((N:ℝ)+1)^2) := by
    have hp := pow_le_pow_left₀ (show 0 ≤ h/2 by positivity) hN 2
    nlinarith [mul_le_mul_of_nonneg_left hp hhp.le]
  calc
    _ ≤ (M*K/h)*T*D/((N:ℝ)+1)^2 := he
    _ = M*K*T*D/(h*((N:ℝ)+1)^2) := by field_simp <;> ring
    _ ≤ 4*M*K*T*D/h^3 := by
      apply (div_le_div_iff₀ (by positivity : 0<h*((N:ℝ)+1)^2) (pow_pos hhp 3)).2
      nlinarith [mul_le_mul_of_nonneg_left hden (show 0 ≤ M*K*T*D by positivity)]
    _ ≤ _ := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      simpa only [pow_one] using mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hD (by norm_num) : D^1 ≤ D^5) (show 0 ≤ 4*M*K*T by positivity)
end WP

noncomputable section
open Set
namespace WP
lemma second_correction_adjacent_prefix_uniform (p : ℕ) (hp : 1 ≤ p) :
    ∃ C : ℝ,0<C ∧ ∀ h : ℝ,1 ≤ h → ∀ t : ℕ,∀ d : List ℕ,(t::d).length=p →
      ∀ N : ℕ,h/2 ≤ (N:ℝ)+1 → ∀ Y∈Icc (0:ℝ) y₀,
      |(∑ l∈Finset.range N,weight Y l*secondDegreeCountLayer Y t d l)/h^2-
        HigherOrder.secondIncrement Y 0 (t::d)/h^2| ≤
        C*(((t::d).sum:ℝ)+1)^5/h^3 := by
  obtain ⟨K,hK,hGrowth⟩ := secondDegreeCountLayer_abs_uniform p hp
  obtain ⟨T,hT,hprefix⟩ := Analysis.weighted_polynomial_prefix_error_uniform 3 1
  refine ⟨2*K*T,by positivity,?_⟩
  intro h hh t d hd N hN Y hY
  have hhp : 0<h := lt_of_lt_of_le zero_lt_one hh
  have hnp : 0<(N:ℝ)+1 := by positivity
  let D : ℝ := ((t::d).sum:ℝ)+1
  have hD : 1 ≤ D := by dsimp [D];linarith [show (0:ℝ) ≤ (t::d).sum from Nat.cast_nonneg _]
  have hD0 : 0 ≤ D := le_trans zero_le_one hD
  have he := hprefix Y hY (t::d).sum K hK.le (secondDegreeCountLayer Y t d) _
    (fun l => hGrowth t d hd l Y hY) (HigherOrder.secondDegreeCountLayer_hasSum Y hY t d) N
  simp only [pow_one] at he
  rw [←sub_div,abs_div,abs_pow,abs_of_pos hhp]
  have hden : h^3 ≤ 2*(h^2*((N:ℝ)+1)) := by
    nlinarith [mul_le_mul_of_nonneg_left hN (sq_nonneg h)]
  calc
    _ ≤ (K*T*D^3/((N:ℝ)+1))/h^2 := div_le_div_of_nonneg_right he (sq_nonneg h)
    _ = K*T*D^3/(h^2*((N:ℝ)+1)) := by field_simp <;> ring
    _ ≤ 2*K*T*D^3/h^3 := by
      apply (div_le_div_iff₀ (by positivity : 0<h^2*((N:ℝ)+1)) (pow_pos hhp 3)).2
      nlinarith [mul_le_mul_of_nonneg_left hden (show 0 ≤ K*T*D^3 by positivity)]
    _ ≤ _ := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hD (by norm_num) : D^3 ≤ D^5) (by positivity)) (by positivity)
end WP
