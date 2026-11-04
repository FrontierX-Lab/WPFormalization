import WPFormalization.Intersection.PrimitivePositivity
import WPFormalization.Intersection.CriticalCoefficient
/-! Exact Appendix B normalization of the classical DVV identity. The signed
normalization retains the original unstable, negative, and wrong-dimension zero
conventions; no bound or shifted recursion is assumed. -/
noncomputable section
namespace WP
/-- The actual normalization of a signed classical intersection number. -/
def primitiveScale (g n : ℕ) : ℝ :=
  (4 : ℝ)^g / (3^(complexity g n)*Real.Gamma (complexity g n))
def signedPureC (P : PsiTheory) (g : ℕ) (d : List ℤ) : ℝ :=
  primitiveScale g d.length * weighted P.psi g d
lemma pureC_signed (P : PsiTheory) (g : ℕ) (d : List ℕ) :
    pureC P g d = signedPureC P g (d.map Int.ofNat) := by
  unfold pureC signedPureC primitiveScale weighted pure doubleWeight
  simp only [List.length_map, List.map_map]
  have he : (fun x : ℕ => (oddFactorial (Int.ofNat x).toNat : ℝ)) =
      (fun x : ℕ => (oddFactorial x : ℝ)) := by funext x; simp
  simp only [Function.comp_def, Int.toNat_natCast, Int.ofNat_eq_natCast]
  ring
lemma primitiveScale_pos (g n : ℕ) (hs : Stable g n) : 0 < primitiveScale g n := by
  have hh : 0 < (complexity g n : ℝ) := by
    exact_mod_cast (show 0 < complexity g n by unfold Stable at hs; unfold complexity; omega)
  unfold primitiveScale
  exact div_pos (by positivity) (mul_pos (by positivity) (Real.Gamma_pos_of_pos hh))
lemma signedPureC_nonneg (P : PsiTheory) (g : ℕ) (d : List ℤ) :
    0 ≤ signedPureC P g d := by
  by_cases hs : Stable g d.length
  · exact mul_nonneg (primitiveScale_pos g d.length hs).le (weighted_nonneg P g d)
  · have hz := P.vanish g d (Or.inl hs)
    simp [signedPureC, weighted, hz]
lemma signedPureC_vanish (P : PsiTheory) (g : ℕ) (d : List ℤ)
    (hv : ¬ Stable g d.length ∨ (∃ k ∈ d, k < 0) ∨
      d.sum ≠ 3*(g : ℤ)-3+d.length) : signedPureC P g d = 0 := by
  simp [signedPureC, weighted, P.vanish g d hv]
lemma primitiveScale_merger (g n : ℕ) (hh : 2 ≤ complexity g (n+1)) :
    primitiveScale g (n+1) =
      (1/(3*((complexity g (n+1) : ℝ)-1))) * primitiveScale g n := by
  have hc : complexity g (n+1) = complexity g n+1 := by unfold complexity at *; omega
  have hn : 0 < (complexity g n : ℝ) := by exact_mod_cast (show 0 < complexity g n by omega)
  unfold primitiveScale
  rw [hc, pow_succ, Nat.cast_add, Nat.cast_one, Real.Gamma_add_one hn.ne']
  field_simp [hn.ne', (Real.Gamma_pos_of_pos hn).ne']
  <;> ring
lemma primitiveScale_handle (g n : ℕ) (hg : 1 ≤ g)
    (hh : 2 ≤ complexity g (n+1)) :
    primitiveScale g (n+1) * (1/2 : ℝ) =
      (2/(3*((complexity g (n+1) : ℝ)-1))) * primitiveScale (g-1) (n+2) := by
  have hc : complexity g (n+1) = complexity (g-1) (n+2)+1 := by unfold complexity at *; omega
  have hn : 0 < (complexity (g-1) (n+2) : ℝ) := by exact_mod_cast (show 0 < complexity (g-1) (n+2) by omega)
  have h4 : (4 : ℝ)^g = 4^(g-1)*4 := by
    nth_rw 1 [show g = (g-1)+1 by omega]
    rw [pow_succ]
  unfold primitiveScale
  rw [hc, pow_succ, Nat.cast_add, Nat.cast_one, Real.Gamma_add_one hn.ne',
    h4]
  field_simp [hn.ne', (Real.Gamma_pos_of_pos hn).ne']
  <;> ring
lemma primitiveScale_separating (g g₁ n n₁ n₂ : ℕ) (hg : g₁ ≤ g)
    (hn : n₁+n₂ = n+2) (hs₁ : Stable g₁ n₁) (hs₂ : Stable (g-g₁) n₂) :
    primitiveScale g (n+1) * (1/2 : ℝ) =
      (Real.Gamma (complexity g₁ n₁) * Real.Gamma (complexity (g-g₁) n₂) /
        (6*Real.Gamma (complexity g (n+1)))) *
      primitiveScale g₁ n₁ * primitiveScale (g-g₁) n₂ := by
  have hc : complexity g (n+1) = complexity g₁ n₁+complexity (g-g₁) n₂+1 := by
    unfold Stable at hs₁ hs₂
    unfold complexity
    omega
  have hp₁ : 0 < (complexity g₁ n₁ : ℝ) := by
    exact_mod_cast (show 0 < complexity g₁ n₁ by unfold Stable at hs₁; unfold complexity; omega)
  have hp₂ : 0 < (complexity (g-g₁) n₂ : ℝ) := by
    exact_mod_cast (show 0 < complexity (g-g₁) n₂ by unfold Stable at hs₂; unfold complexity; omega)
  have hp : 0 < (complexity g (n+1) : ℝ) := by rw [hc]; positivity
  have hpow : (4 : ℝ)^g = 4^g₁*4^(g-g₁) := by rw [← pow_add]; congr 1; omega
  unfold primitiveScale
  rw [hc, pow_succ, pow_add, hpow]
  field_simp [(Real.Gamma_pos_of_pos hp₁).ne', (Real.Gamma_pos_of_pos hp₂).ne',
    (Real.Gamma_pos_of_pos hp).ne']
  <;> ring
def primitiveDvvRHS (P : PsiTheory) (g pivot : ℕ) (d : List ℤ) : ℝ :=
  (∑ j ∈ Finset.range d.length,
    ((2*(d[j]! : ℝ)+1)/(3*((complexity g (d.length+1) : ℝ)-1))) *
      signedPureC P g (((pivot : ℤ)+d[j]!-1) :: d.eraseIdx j)) +
  (if g = 0 then 0 else
    (2/(3*((complexity g (d.length+1) : ℝ)-1))) *
      ∑ u ∈ Finset.range (pivot-1),
        signedPureC P (g-1) ((u : ℤ) :: ((pivot : ℤ)-2-u) :: d)) +
  ∑ u ∈ Finset.range (pivot-1), ∑ g₁ ∈ Finset.range (g+1),
    ∑ I ∈ (Finset.range d.length).powerset,
      let c₁ := (u : ℤ) :: selected d I
      let c₂ := ((pivot : ℤ)-2-u) :: selected d ((Finset.range d.length) \ I)
      (Real.Gamma (complexity g₁ c₁.length) * Real.Gamma (complexity (g-g₁) c₂.length) /
        (6*Real.Gamma (complexity g (d.length+1)))) *
      signedPureC P g₁ c₁ * signedPureC P (g-g₁) c₂
lemma signedPureC_dvv (P : PsiTheory) (g pivot : ℕ) (d : List ℤ)
    (hd : ∀ k ∈ d, 0 ≤ k) (hh : 2 ≤ complexity g (d.length+1)) :
    signedPureC P g ((pivot : ℤ) :: d) = primitiveDvvRHS P g pivot d := by
  unfold signedPureC
  simp only [List.length_cons]
  rw [P.dvv g pivot d hd hh]
  unfold dvvRHS primitiveDvvRHS signedPureC
  simp only [mul_add]
  congr 1
  · congr 1
    · rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      have hj' := Finset.mem_range.mp hj
      rw [List.length_cons, List.length_eraseIdx_of_lt hj',
        show d.length-1+1 = d.length by omega]
      rw [primitiveScale_merger g d.length hh]
      ring
    · split_ifs with hg
      · simp
      · have hg' : 1 ≤ g := by omega
        rw [← mul_assoc, primitiveScale_handle g d.length hg' hh]
        rw [Finset.mul_sum, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro u hu
        simp only [List.length_cons]
        rw [show d.length+1+1 = d.length+2 by omega]
        ring
  · simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro u hu
    apply Finset.sum_congr rfl
    intro g₁ hg₁
    apply Finset.sum_congr rfl
    intro I hI
    rw [← mul_assoc]
    let c₁ := (u : ℤ) :: selected d I
    let c₂ := ((pivot : ℤ)-2-u) :: selected d ((Finset.range d.length) \ I)
    by_cases hs₁ : Stable g₁ c₁.length
    · by_cases hs₂ : Stable (g-g₁) c₂.length
      · have hg₁' : g₁ ≤ g := by have := Finset.mem_range.mp hg₁; omega
        have hn : c₁.length+c₂.length = d.length+2 := by
          dsimp only [c₁,c₂]
          simp only [List.length_cons]
          have := selected_partition_length d I
          omega
        have he := primitiveScale_separating g g₁ d.length c₁.length c₂.length hg₁' hn hs₁ hs₂
        change primitiveScale g (d.length+1)*(1/2) *
          (weighted P.psi g₁ c₁ * weighted P.psi (g-g₁) c₂) = _
        rw [he]
        ring
      · have hz := P.vanish (g-g₁) c₂ (Or.inl hs₂)
        change primitiveScale g (d.length+1)*(1/2) *
          (weighted P.psi g₁ c₁ * weighted P.psi (g-g₁) c₂) = _
        change _ = _ * (primitiveScale (g-g₁) c₂.length * weighted P.psi (g-g₁) c₂)
        simp [weighted,hz]
    · have hz := P.vanish g₁ c₁ (Or.inl hs₁)
      change primitiveScale g (d.length+1)*(1/2) *
        (weighted P.psi g₁ c₁ * weighted P.psi (g-g₁) c₂) = _
      change _ = _ * (primitiveScale g₁ c₁.length * weighted P.psi g₁ c₁) * _
      simp [weighted,hz]
lemma pureC_nonneg (P : PsiTheory) (g : ℕ) (d : List ℕ) : 0 ≤ pureC P g d := by
  rw [pureC_signed]
  exact signedPureC_nonneg P g (d.map Int.ofNat)
end WP
