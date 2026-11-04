import WPFormalization.Weighted.LabelEntropy

/-! Uniformly summable genus/label envelopes after exponential damping. These finite-series estimates are auxiliary to the original separating bound; they do not assert that the original actual separating mass is already bounded. -/
noncomputable section
namespace WP
lemma summable_separating_polynomial (p : ℕ) :
    Summable (fun k : ℕ => ((k : ℝ)+4)^p*Real.exp (-(k : ℝ)/12)) := by
  have hs := (summable_nat_add_iff 4).mpr
    (Real.summable_pow_mul_exp_neg_nat_mul p (r := 1/12) (by norm_num))
  have ht := hs.mul_right (Real.exp (1/3 : ℝ))
  apply ht.congr
  intro k
  push_cast
  rw [mul_assoc,← Real.exp_add]
  congr 2
  ring
lemma separating_polynomial_sum_bound (p : ℕ) : ∃ C : ℝ, 0<C ∧ ∀ K : ℕ,
    (∑ k ∈ Finset.range (K+1), ((k : ℝ)+4)^p*Real.exp (-(k : ℝ)/12)) ≤ C := by
  let C := ∑' k : ℕ, ((k : ℝ)+4)^p*Real.exp (-(k : ℝ)/12)
  have hC : 0 ≤ C := tsum_nonneg (by intro k; positivity)
  refine ⟨C+1,by positivity,?_⟩
  intro K
  exact (Summable.sum_le_tsum (Finset.range (K+1)) (by intro k hk; positivity)
    (summable_separating_polynomial p)).trans (by dsimp only [C]; linarith)
lemma rpow_three_halves (h : ℝ) (hh : 0<h) : Real.rpow h (3/2 : ℝ)=h*Real.sqrt h := by
  rw [Real.rpow_eq_pow,show (3/2 : ℝ)=1+1/2 by ring,Real.rpow_add hh,Real.rpow_one,← Real.sqrt_eq_rpow]
lemma gamma_denominator_sqrt (h : ℝ) (hh : 3≤h) :
    Real.sqrt h/((h-1)*(h-2)) ≤ 9/Real.rpow h (3/2 : ℝ) := by
  have hh₀ : 0<h := by linarith
  have hs : 0<Real.sqrt h := Real.sqrt_pos_of_pos hh₀
  rw [rpow_three_halves h hh₀]
  apply (div_le_div_iff₀ (mul_pos (by linarith) (by linarith) : 0<(h-1)*(h-2)) (mul_pos hh₀ hs)).mpr
  have h₁ : h/3≤h-1 := by linarith
  have h₂ : h/3≤h-2 := by linarith
  have he := mul_le_mul h₁ h₂ (by positivity : 0≤h/3) (by linarith : 0≤h-1)
  have hr := Real.sq_sqrt hh₀.le
  nlinarith
def separatingLabelEnvelope (I R k g : ℕ) : ℝ :=
  if g=0 then ∑ uv ∈ Finset.HasAntidiagonal.antidiagonal (k+2), if 2≤uv.1 then
    Real.sqrt (I.choose uv.1)*(R.choose uv.2 : ℝ) else 0
  else weightedLabelSum I R (k+2-2*g)
lemma separatingLabelEnvelope_nonneg (I R k g : ℕ) : 0 ≤ separatingLabelEnvelope I R k g := by
  unfold separatingLabelEnvelope weightedLabelSum
  split_ifs <;> positivity
lemma separatingLabelEnvelope_bound (I R N k g : ℕ)
    (hN : 2*k≤N) (hIR : I+R≤N) (hR : 3*R≤2*N) :
    separatingLabelEnvelope I R k g ≤
      (1+(I : ℝ))*(4*((k : ℝ)+1)*(N.choose k : ℝ)*Real.exp (-(k : ℝ)/6)) := by
  by_cases hg : g=0
  · unfold separatingLabelEnvelope
    rw [if_pos hg]
    exact (weightedLabelSum_genus_zero_entropy I R N k hN hIR hR).trans
      (mul_le_mul_of_nonneg_right (by linarith) (by positivity))
  · unfold separatingLabelEnvelope
    rw [if_neg hg]
    exact (weightedLabelSum_entropy_all I R N k (k+2-2*g) hN hIR hR (by omega)).trans
      (by have hnon : 0≤4*((k : ℝ)+1)*(N.choose k : ℝ)*Real.exp (-(k : ℝ)/6) := by positivity
          nlinarith [show (0 : ℝ)≤I by positivity])
def separatingSeriesTerm (I R N k g : ℕ) : ℝ :=
  ((k+2-2*g : ℕ)+2)*separatingLabelEnvelope I R k g/(N.choose k : ℝ)*Real.exp ((k+1 : ℕ)/12)
lemma separatingSeriesTerm_bound (I R N k g : ℕ)
    (hN : 2*k≤N) (hIR : I+R≤N) (hR : 3*R≤2*N) :
    separatingSeriesTerm I R N k g ≤
      4*Real.exp (1/12 : ℝ)*(1+(I : ℝ))*((k : ℝ)+4)^2*Real.exp (-(k : ℝ)/12) := by
  have hch : (0 : ℝ)<(N.choose k : ℝ) := by exact_mod_cast Nat.choose_pos (show k≤N by omega)
  have henv : separatingLabelEnvelope I R k g/(N.choose k : ℝ) ≤
      (1+(I : ℝ))*4*((k : ℝ)+1)*Real.exp (-(k : ℝ)/6) := by
    apply (div_le_iff₀ hch).mpr
    convert separatingLabelEnvelope_bound I R N k g hN hIR hR using 1 <;> ring
  have hs : ((k+2-2*g : ℕ)+2 : ℝ)≤(k : ℝ)+4 := by
    exact_mod_cast (show (k+2-2*g)+2≤k+4 by omega)
  have hnum : ((k+2-2*g : ℕ)+2 : ℝ)*(separatingLabelEnvelope I R k g/(N.choose k : ℝ)) ≤
      ((k : ℝ)+4)*((1+(I : ℝ))*4*((k : ℝ)+1)*Real.exp (-(k : ℝ)/6)) :=
    mul_le_mul hs henv (div_nonneg (separatingLabelEnvelope_nonneg I R k g) hch.le) (by positivity)
  have he := mul_le_mul_of_nonneg_right hnum (Real.exp_pos ((k+1 : ℕ)/12)).le
  have heExp : Real.exp (-(k : ℝ)/6)*Real.exp ((k+1 : ℕ)/12) =
      Real.exp (1/12 : ℝ)*Real.exp (-(k : ℝ)/12) := by
    rw [← Real.exp_add,← Real.exp_add]
    congr 1
    push_cast
    ring
  unfold separatingSeriesTerm
  calc
    _ = (((k+2-2*g : ℕ)+2 : ℝ)*(separatingLabelEnvelope I R k g/(N.choose k : ℝ)))*
        Real.exp ((k+1 : ℕ)/12) := by ring
    _ ≤ _ := he
    _ = 4*Real.exp (1/12 : ℝ)*(1+(I : ℝ))*(((k : ℝ)+4)*((k : ℝ)+1))*Real.exp (-(k : ℝ)/12) := by
      calc
        _ = 4*(1+(I : ℝ))*(((k : ℝ)+4)*((k : ℝ)+1))*
            (Real.exp (-(k : ℝ)/6)*Real.exp ((k+1 : ℕ)/12)) := by ring
        _ = _ := by rw [heExp]; ring
    _ ≤ _ := by
      have hp : ((k : ℝ)+4)*((k : ℝ)+1)≤((k : ℝ)+4)^2 := by nlinarith [show (0 : ℝ)≤k by positivity]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp (by positivity)) (by positivity)
lemma separatingSeries_genus_sum (I R N k : ℕ)
    (hN : 2*k≤N) (hIR : I+R≤N) (hR : 3*R≤2*N) :
    (∑ g ∈ Finset.range (k+3), separatingSeriesTerm I R N k g) ≤
      4*Real.exp (1/12 : ℝ)*(1+(I : ℝ))*((k : ℝ)+4)^3*Real.exp (-(k : ℝ)/12) := by
  have he := Finset.sum_le_sum (s := Finset.range (k+3))
    (fun g hg => separatingSeriesTerm_bound I R N k g hN hIR hR)
  simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul,Nat.cast_add,Nat.cast_ofNat] at he
  apply he.trans
  have hk : (0 : ℝ)≤k := by positivity
  have hp : ((k : ℝ)+3)*((k : ℝ)+4)^2≤((k : ℝ)+4)^3 := by nlinarith [sq_nonneg ((k : ℝ)+4)]
  have hm := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp
    (show 0≤4*Real.exp (1/12 : ℝ)*(1+(I : ℝ)) by positivity))
    (Real.exp_pos (-(k : ℝ)/12)).le
  convert hm using 1 <;> ring
lemma separatingSeries_total_bound : ∃ C : ℝ, 0<C ∧ ∀ I R N : ℕ,
    I+R≤N → 3*R≤2*N →
    (∑ k ∈ Finset.range (N/2+1), ∑ g ∈ Finset.range (k+3),
      separatingSeriesTerm I R N k g) ≤ C*(1+(I : ℝ)) := by
  obtain ⟨C,hC,hbound⟩ := separating_polynomial_sum_bound 3
  refine ⟨4*Real.exp (1/12 : ℝ)*C,by positivity,?_⟩
  intro I R N hIR hR
  calc
    _ ≤ ∑ k ∈ Finset.range (N/2+1),
        4*Real.exp (1/12 : ℝ)*(1+(I : ℝ))*((k : ℝ)+4)^3*Real.exp (-(k : ℝ)/12) := by
      apply Finset.sum_le_sum
      intro k hk
      exact separatingSeries_genus_sum I R N k
        (by have := Finset.mem_range.mp hk; omega) hIR hR
    _ = (4*Real.exp (1/12 : ℝ)*(1+(I : ℝ)))*
        (∑ k ∈ Finset.range (N/2+1), ((k : ℝ)+4)^3*Real.exp (-(k : ℝ)/12)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      ring
    _ ≤ (4*Real.exp (1/12 : ℝ)*(1+(I : ℝ)))*C :=
      mul_le_mul_of_nonneg_left (hbound (N/2)) (by positivity)
    _ = _ := by ring
end WP
