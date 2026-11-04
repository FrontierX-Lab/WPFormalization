import WPFormalization.Comparison.ZeroDrift
/-! The full finite zero-potential budget for the actual merger and handle
profiles. The genuine layer drift above 24 and the elementary fourfold cap
below 24 give one uniform additive budget 2^26, without a stochastic axiom. -/
noncomputable section
namespace WP
open Set
def zeroCountLayer (pivot:ℕ)(d:List ℕ)(l:ℕ):ℝ:=
  (∑j∈Finset.range d.length,(2*(d[j]!:ℝ)+1)*(if 1 ≤ pivot+d[j]!+l then 1 else 0))+2*(pivot+l-1:ℕ)
lemma zeroCountLayer_nonneg (pivot:ℕ)(d:List ℕ)(l:ℕ):0 ≤ zeroCountLayer pivot d l := by
  unfold zeroCountLayer
  apply add_nonneg
  · apply Finset.sum_nonneg
    intro j hj
    split_ifs <;> positivity
  · positivity
lemma zeroCountLayer_positive (pivot:ℕ)(d:List ℕ)(l:ℕ)(hp:1 ≤ pivot):
    zeroCountLayer pivot d l=(∑j∈Finset.range d.length,(2*(d[j]!:ℝ)+1))+2*(pivot+l-1:ℕ) := by
  unfold zeroCountLayer
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw[if_pos (by omega :1 ≤ pivot+d[j]!+l),mul_one]
lemma zeroCountLayer_zero (d:List ℕ)(hd:∀k∈d,k=0)(l:ℕ):
    zeroCountLayer 0 d l=(d.length:ℝ)*(if 1 ≤ l then 1 else 0)+2*(l-1:ℕ) := by
  unfold zeroCountLayer
  simp only[Nat.zero_add]
  congr 1
  calc _=∑j∈Finset.range d.length, (if 1 ≤ l then (1:ℝ) else 0):=by
            apply Finset.sum_congr rfl
            intro j hj
            have hj':=Finset.mem_range.mp hj
            have hv:d[j]! = 0:=hd _ (by simpa[hj'] using List.getElem_mem (l:=d) j hj')
            simp[hv]
       _=_:=by simp
lemma zeroPotentialLayer_large (pivot:ℕ)(d:List ℕ)(l:ℕ)
    (hp:1 ≤ pivot ∨(pivot=0 ∧∀k∈d,k=0))(hZ:24 ≤ zeros (pivot::d)):
    zeroPotentialLayer pivot d l ≤ zeroCountLayer pivot d l := by
  rcases hp with hp|⟨rfl,hd⟩
  · rw[zeroCountLayer_positive pivot d l hp]
    exact zeroPotentialLayer_positive_drift pivot d l hp hZ
  · rw[zeroCountLayer_zero d hd l]
    exact zeroPotentialLayer_zero_drift d hd l hZ
lemma zeroPotentialLayer_coarse (pivot:ℕ)(d:List ℕ)(l:ℕ):
    zeroPotentialLayer pivot d l ≤ 4*zeroCountLayer pivot d l := by
  have hmerger:∀j∈Finset.range d.length,zeroPowerRatio (pivot::d) (mergerProfile pivot d l j) ≤ 4:=by
    intro j hj
    have hj':=Finset.mem_range.mp hj
    have hp:(d[j]!::d.eraseIdx j).Perm d:=by simpa[hj'] using List.getElem_cons_eraseIdx_perm hj'
    have hEr:zeros (d.eraseIdx j) ≤ zeros d:=by
      rw[←zeros_perm hp]
      exact (zeros_cons_bounds d[j]! (d.eraseIdx j)).1
    have hCh:zeros (mergerProfile pivot d l j) ≤ zeros (d.eraseIdx j)+1:=(zeros_cons_bounds _ _).2
    have hPar:zeros d ≤ zeros (pivot::d):=(zeros_cons_bounds _ _).1
    apply zeroPowerRatio_le_four
    omega
  have hm:(∑j∈Finset.range d.length,(2*(d[j]!:ℝ)+1)*
      (if 1 ≤ pivot+d[j]!+l then zeroPowerRatio (pivot::d) (mergerProfile pivot d l j) else 0)) ≤
      4*(∑j∈Finset.range d.length,(2*(d[j]!:ℝ)+1)*(if 1 ≤ pivot+d[j]!+l then 1 else 0)):=by
    rw[Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j hj
    split_ifs
    · have hc:0 ≤ 2*(d[j]!:ℝ)+1:=by positivity
      have he:=mul_le_mul_of_nonneg_left (hmerger j hj) hc
      nlinarith
    · simp
  have hn:(∑u∈Finset.range (pivot+l-1),zeroPowerRatio (pivot::d) (contractionProfile pivot d l u)) ≤ 4*(pivot+l-1:ℕ):=by
    calc _ ≤ ∑u∈Finset.range (pivot+l-1),(4:ℝ):=by
              apply Finset.sum_le_sum
              intro u hu
              exact zeroPowerRatio_contraction_cap pivot u (pivot+l-2-u) d
         _=_:=by simp;ring
  unfold zeroPotentialLayer zeroCountLayer
  linarith
lemma finite_zero_power_budget (s:Finset ℕ)(c:ℕ→ℝ)(hc:∀l∈s,0 ≤ c l)
    (pivot:ℕ)(d:List ℕ)(hp:1 ≤ pivot ∨(pivot=0 ∧∀k∈d,k=0)):
    (2:ℝ)^(zeros (pivot::d))*(∑l∈s,c l*zeroPotentialLayer pivot d l) ≤
      (∑l∈s,c l*zeroCountLayer pivot d l)*((2:ℝ)^(zeros (pivot::d))+(2:ℝ)^26) := by
  let Z:=zeros (pivot::d)
  let mass:=∑l∈s,c l*zeroCountLayer pivot d l
  have hm:0 ≤ mass:=Finset.sum_nonneg (fun l hl=>mul_nonneg (hc l hl) (zeroCountLayer_nonneg _ _ _))
  by_cases hZ:24 ≤ Z
  · have hpot:(∑l∈s,c l*zeroPotentialLayer pivot d l) ≤ mass:=
      Finset.sum_le_sum (fun l hl=>mul_le_mul_of_nonneg_left (zeroPotentialLayer_large pivot d l hp hZ) (hc l hl))
    have he:=mul_le_mul_of_nonneg_left hpot (show 0 ≤ (2:ℝ)^Z by positivity)
    change (2:ℝ)^Z*(∑l∈s,c l*zeroPotentialLayer pivot d l) ≤ mass*((2:ℝ)^Z+(2:ℝ)^26)
    have hplus:0 ≤ mass*(2:ℝ)^26:=by positivity
    nlinarith
  · have hpot:(∑l∈s,c l*zeroPotentialLayer pivot d l) ≤ 4*mass:=by
      calc _ ≤ ∑l∈s,c l*(4*zeroCountLayer pivot d l):=Finset.sum_le_sum
                 (fun l hl=>mul_le_mul_of_nonneg_left (zeroPotentialLayer_coarse pivot d l) (hc l hl))
           _=4*mass:=by dsimp[mass];rw[Finset.mul_sum];apply Finset.sum_congr rfl;intro l hl;ring
    have hpZ:(2:ℝ)^Z ≤ (2:ℝ)^24:=pow_le_pow_right₀ (by norm_num) (by omega)
    have hn:(3:ℝ)*(2:ℝ)^24 ≤ (2:ℝ)^26:=by norm_num
    have hcmp:4*(2:ℝ)^Z ≤ (2:ℝ)^Z+(2:ℝ)^26:=by nlinarith
    have he:=mul_le_mul_of_nonneg_left hpot (show 0 ≤ (2:ℝ)^Z by positivity)
    have hf:=mul_le_mul_of_nonneg_left hcmp hm
    change (2:ℝ)^Z*(∑l∈s,c l*zeroPotentialLayer pivot d l) ≤ mass*((2:ℝ)^Z+(2:ℝ)^26)
    nlinarith
end WP
