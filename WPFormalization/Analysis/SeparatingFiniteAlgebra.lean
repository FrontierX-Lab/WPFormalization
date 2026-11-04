import Mathlib

/-! Actual finite estimates for the separating terms of Section 6. The
proofs use the original marked W functions and the already proved ratio
and growth bounds; no separating estimate is assumed. -/
noncomputable section
open Set
open scoped BigOperators
namespace WP.Analysis

lemma finite_symmetric_sum_le_twice_half (g : ℕ) (f : ℕ → ℝ)
    (hf : ∀ j : ℕ, j ≤ g → 0 ≤ f j)
    (hsym : ∀ j : ℕ, j ≤ g → f (g-j)=f j) :
    (∑ j ∈ Finset.range (g+1), f j) ≤ 2*∑ j ∈ Finset.range (g/2+1), f j := by
  classical
  let L := (Finset.range (g+1)).filter (fun j => 2*j ≤ g)
  let U := (Finset.range (g+1)).filter (fun j => ¬2*j ≤ g)
  have hpart : (∑ j ∈ Finset.range (g+1), f j) = (∑ j ∈ L, f j)+(∑ j ∈ U, f j) := by
    dsimp only [L,U]
    simp only [Finset.sum_filter]
    rw [←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    by_cases h : 2*j ≤ g <;> simp [h]
  have hL : L = Finset.range (g/2+1) := by
    ext j
    simp only [L,Finset.mem_filter,Finset.mem_range]
    omega
  have hUpper : (∑ j ∈ U, f j) ≤ ∑ j ∈ L, f j := by
    apply Finset.sum_le_sum_of_injOn (fun j => g-j)
    · intro i hi j hj he
      have hi' := (Finset.mem_filter.mp hi).1
      have hj' := (Finset.mem_filter.mp hj).1
      simp only [Finset.mem_range] at hi' hj'
      change g-i=g-j at he
      omega
    · intro i hi
      obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hi
      have hj' := Finset.mem_filter.mp hj
      have hg' := Finset.mem_range.mp hj'.1
      simp only [L,Finset.mem_filter,Finset.mem_range]
      omega
    · intro j hj
      have hgj : j ≤ g := by have := Finset.mem_range.mp (Finset.mem_filter.mp hj).1;omega
      exact (hsym j hgj).symm.le
    · intro j hj hnot
      exact hf j (by have := Finset.mem_range.mp (Finset.mem_filter.mp hj).1;omega)
  rw [hpart,←hL]
  linarith

lemma finite_half_cut_partition (g N : ℕ) (hN : 2 ≤ N) (f : ℕ → ℝ) :
    (∑ j ∈ Finset.range (g/2+1), f j) = f 0 +
      (∑ j ∈ Finset.range (g/N+1), if 1 ≤ j then f j else 0) +
      ∑ j ∈ Finset.range (g+1), if g/N < j ∧ 2*j ≤ g then f j else 0 := by
  classical
  let H := Finset.range (g/2+1)
  let S := Finset.range (g/N+1)
  have hcut : g/N ≤ g/2 := Nat.div_le_div_left hN (by norm_num)
  have hSub : S ⊆ H := Finset.range_mono (by omega)
  have hSet : (Finset.range (g+1)).filter (fun j => g/N < j ∧ 2*j ≤ g) = H\S := by
    ext j
    simp only [H,S,Finset.mem_filter,Finset.mem_range,Finset.mem_sdiff]
    omega
  have hmacro : (∑ j ∈ Finset.range (g+1), if g/N < j ∧ 2*j ≤ g then f j else 0) =
      ∑ j ∈ H\S, f j := by rw [←Finset.sum_filter,hSet]
  have hzero : (∑ j ∈ S, f j) = f 0 +
      ∑ j ∈ Finset.range (g/N+1), if 1 ≤ j then f j else 0 := by
    dsimp only [S]
    rw [Finset.sum_range_succ',Finset.sum_range_succ']
    simp [add_comm]
  have hsplit := Finset.sum_sdiff (f:=f) hSub
  change (∑ j ∈ H, f j) = _
  linarith

lemma finite_half_positive_cut_partition (g N : ℕ) (hN : 2 ≤ N) (f : ℕ → ℝ) :
    (∑ j ∈ Finset.range (g/2+1), if 1 ≤ j then f j else 0) =
      (∑ j ∈ Finset.range (g/N+1), if 1 ≤ j then f j else 0) +
      ∑ j ∈ Finset.range (g+1), if g/N < j ∧ 2*j ≤ g then f j else 0 := by
  have hzero : (∑ j ∈ Finset.range (g/2+1), f j) = f 0 +
      ∑ j ∈ Finset.range (g/2+1), if 1 ≤ j then f j else 0 := by
    rw [Finset.sum_range_succ',Finset.sum_range_succ']
    simp [add_comm]
  linarith [finite_half_cut_partition g N hN f]

lemma finite_symmetric_positive_sum_bound (g N : ℕ) (hg : 2 ≤ g) (hN : 2 ≤ N) (f : ℕ → ℝ)
    (hf : ∀ j : ℕ, j ≤ g → 0 ≤ f j)
    (hsym : ∀ j : ℕ, j ≤ g → f (g-j)=f j) :
    (∑ j ∈ Finset.range (g+1), if 1 ≤ j ∧ j < g then f j else 0) ≤
      2*((∑ j ∈ Finset.range (g/N+1), if 1 ≤ j then f j else 0) +
        ∑ j ∈ Finset.range (g+1), if g/N < j ∧ 2*j ≤ g then f j else 0) := by
  let f' (j : ℕ) := if 1 ≤ j ∧ j < g then f j else 0
  have hnon : ∀ j, j ≤ g → 0 ≤ f' j := by
    intro j hj
    dsimp only [f']
    split_ifs <;> [exact hf j hj;exact le_rfl]
  have hsym' : ∀ j, j ≤ g → f' (g-j)=f' j := by
    intro j hj
    by_cases h : 1 ≤ j ∧ j < g
    · have h' : 1 ≤ g-j ∧ g-j < g := by omega
      simp only [f',if_pos h,if_pos h',hsym j hj]
    · have h' : ¬(1 ≤ g-j ∧ g-j < g) := by omega
      simp only [f',if_neg h,if_neg h']
  have hb := finite_symmetric_sum_le_twice_half g f' hnon hsym'
  have hhalf : (∑ j ∈ Finset.range (g/2+1), f' j) =
      ∑ j ∈ Finset.range (g/2+1), if 1 ≤ j then f j else 0 := by
    apply Finset.sum_congr rfl
    intro j hj
    have hj' := Finset.mem_range.mp hj
    have hjg : j < g := by omega
    simp only [f',hjg,and_true]
  rw [hhalf,finite_half_positive_cut_partition g N hN f] at hb
  exact hb

lemma finite_sum_eq_endpoints_plus_positive (g : ℕ) (hg : 1 ≤ g) (f : ℕ → ℝ) :
    (∑ j ∈ Finset.range (g+1), f j) = f 0+f g+
      ∑ j ∈ Finset.range (g+1), if 1 ≤ j ∧ j < g then f j else 0 := by
  calc
    _ = ∑ j ∈ Finset.range (g+1),
        ((if j=0 then f 0 else 0)+(if j=g then f g else 0)+
          (if 1 ≤ j ∧ j < g then f j else 0)) := by
      apply Finset.sum_congr rfl
      intro j hj
      have hj' := Finset.mem_range.mp hj
      by_cases h0 : j=0
      · subst j
        simp [show (0:ℕ)≠g by omega]
      · by_cases hlast : j=g
        · subst j
          simp [show g≠0 by omega]
        · have hmid : 1 ≤ j ∧ j < g := by omega
          simp [h0,hlast,hmid]
    _ = _ := by simp [Finset.sum_add_distrib]

lemma two_pow_le_centralBinom (j : ℕ) : 2^j ≤ Nat.centralBinom j := by
  induction j with
  | zero => simp
  | succ j ih =>
    have he := Nat.succ_mul_centralBinom_succ j
    have hm : (j+1)*(2*Nat.centralBinom j) ≤ (j+1)*Nat.centralBinom (j+1) := by
      rw [he]
      nlinarith
    have hstep : 2*Nat.centralBinom j ≤ Nat.centralBinom (j+1) :=
      Nat.le_of_mul_le_mul_left hm (Nat.succ_pos j)
    calc
      2^(j+1) = 2*2^j := by rw [pow_succ];ring
      _ ≤ 2*Nat.centralBinom j := Nat.mul_le_mul_left _ ih
      _ ≤ _ := hstep

lemma two_pow_le_choose_add (a b j : ℕ) (ha : j ≤ a) (hb : j ≤ b) :
    2^j ≤ (a+b).choose b := by
  calc
    _ ≤ Nat.centralBinom j := two_pow_le_centralBinom j
    _ ≤ (a+j).choose j := Nat.choose_le_choose j (by omega)
    _ = (a+j).choose a := Nat.choose_symm_add.symm
    _ ≤ (a+b).choose a := Nat.choose_le_choose a (by omega)
    _ = (a+b).choose b := Nat.choose_symm_add

lemma factorial_pair_ratio_le_geometric (a b j : ℕ) (ha : j ≤ a) (hb : j ≤ b) :
    ((a.factorial:ℝ)*b.factorial)/(a+b).factorial ≤ (1/2:ℝ)^j := by
  have heN := Nat.add_choose_mul_factorial_mul_factorial a b
  have he : ((a+b).choose b:ℝ)*a.factorial*b.factorial=(a+b).factorial := by exact_mod_cast heN
  have hc : (2:ℝ)^j ≤ (Nat.choose (a+b) b:ℝ) := by exact_mod_cast two_pow_le_choose_add a b j ha hb
  rw [div_pow,one_pow]
  apply (div_le_div_iff₀ (by positivity : (0:ℝ)<(a+b).factorial) (by positivity : (0:ℝ)<2^j)).2
  have hm := mul_le_mul_of_nonneg_right hc (show 0 ≤ (a.factorial:ℝ)*b.factorial by positivity)
  nlinarith

lemma gamma_nat_eq_pred_factorial (n : ℕ) (hn : 1 ≤ n) :
    Real.Gamma (n:ℝ) = ((n-1).factorial:ℝ) := by
  have he : (n:ℝ) = ((n-1:ℕ):ℝ)+1 := by exact_mod_cast (Nat.sub_add_cancel hn).symm
  rw [he,Real.Gamma_nat_eq_factorial]

lemma gamma_pair_ratio_le_geometric (h₁ h₂ h j : ℕ) (h₁p : 1 ≤ h₁) (h₂p : 1 ≤ h₂)
    (hs : h₁+h₂ ≤ h) (hj₁ : j+1 ≤ h₁) (hj₂ : j+1 ≤ h₂) :
    Real.Gamma (h₁:ℝ)*Real.Gamma (h₂:ℝ)/Real.Gamma (h:ℝ) ≤ (1/2:ℝ)^j := by
  have hp : 1 ≤ h := by omega
  rw [gamma_nat_eq_pred_factorial h₁ h₁p,gamma_nat_eq_pred_factorial h₂ h₂p,gamma_nat_eq_pred_factorial h hp]
  have hd : (((h₁-1)+(h₂-1)).factorial:ℝ) ≤ ((h-1).factorial:ℝ) := by
    exact_mod_cast Nat.factorial_le (show (h₁-1)+(h₂-1) ≤ h-1 by omega)
  calc
    _ ≤ (((h₁-1).factorial:ℝ)*(h₂-1).factorial)/((h₁-1)+(h₂-1)).factorial :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hd
    _ ≤ _ := factorial_pair_ratio_le_geometric (h₁-1) (h₂-1) j (by omega) (by omega)

lemma linear_times_exp_decay_bound (α : ℝ) (hα : 0 < α) (g : ℕ) (hg : 1 ≤ g) :
    ((g:ℝ)+1)*Real.exp (-α*(g:ℝ)) ≤ 12/(α^3*(g:ℝ)^2) := by
  have hgR : (1:ℝ) ≤ g := by exact_mod_cast hg
  have hgpos : 0 < (g:ℝ) := by linarith
  have he := Real.pow_div_factorial_le_exp (α*(g:ℝ)) (by positivity) 3
  norm_num only [Nat.factorial_succ,Nat.factorial_zero,Nat.cast_ofNat,mul_one] at he
  have hm := mul_le_mul_of_nonneg_right (show (g:ℝ)+1 ≤ 2*g by linarith)
    (show 0 ≤ α^3*(g:ℝ)^2 by positivity)
  rw [show -α*(g:ℝ)=-(α*(g:ℝ)) by ring,Real.exp_neg,←div_eq_mul_inv]
  apply (div_le_div_iff₀ (Real.exp_pos _) (by positivity : 0 < α^3*(g:ℝ)^2)).2
  nlinarith

end WP.Analysis
