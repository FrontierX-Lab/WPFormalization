import WPFormalization.Analysis.FiniteWatson
/-! Factorial convolution and the unused amplitude tail in finite Gaussian
Gevrey-two expansions. All constants precede the truncation order and the
finite amplitude range. These are scalar inequalities with standard axioms. -/
noncomputable section
open Set
namespace WP.Analysis
lemma gaussian_factorial_convolution (s N:ℕ) :
    (s.factorial:ℝ)^2*(N.factorial:ℝ)≤((s+N).factorial:ℝ)^2 := by
  have hp:(s.factorial:ℝ)*(N.factorial:ℝ)≤((s+N).factorial:ℝ) := by
    exact_mod_cast Nat.le_of_dvd (Nat.factorial_pos (s+N)) (Nat.factorial_mul_factorial_dvd_factorial_add s N)
  have hN:1≤(N.factorial:ℝ) := by exact_mod_cast Nat.factorial_pos N
  calc _ ≤ (s.factorial:ℝ)^2*(N.factorial:ℝ)^2 :=
          mul_le_mul_of_nonneg_left (le_self_pow₀ hN (by norm_num)) (sq_nonneg _)
       _ = ((s.factorial:ℝ)*(N.factorial:ℝ))^2 := by ring
       _ ≤ _ := pow_le_pow_left₀ (by positivity) hp 2

lemma gaussian_gevrey_two_convolution (B D:ℝ) (hB:0≤B) (hD:0≤D) (K:ℕ) :
    (∑s∈Finset.range (K+1),B^s*(s.factorial:ℝ)^2*D^(K+1-s)*((K+1-s).factorial:ℝ))≤
      (2*max B D)^(K+1)*((K+1).factorial:ℝ)^2 := by
  let E:ℝ := max B D
  have hE:0≤E := hB.trans (le_max_left _ _)
  have hterm (s:ℕ) (hs:s∈Finset.range (K+1)) :
      B^s*(s.factorial:ℝ)^2*D^(K+1-s)*((K+1-s).factorial:ℝ)≤
        E^(K+1)*((K+1).factorial:ℝ)^2 := by
    have hsK:s≤K+1 := (Finset.mem_range.mp hs).le
    have hplus:s+(K+1-s)=K+1 := Nat.add_sub_of_le hsK
    have hp:B^s*D^(K+1-s)≤E^(K+1) := by
      calc _ ≤ E^s*E^(K+1-s) := mul_le_mul
                (pow_le_pow_left₀ hB (le_max_left B D) s)
                (pow_le_pow_left₀ hD (le_max_right B D) _) (by positivity) (by positivity)
           _ = E^(K+1) := by rw [←pow_add,hplus]
    have hf:=gaussian_factorial_convolution s (K+1-s)
    rw [hplus] at hf
    calc _ = (B^s*D^(K+1-s))*((s.factorial:ℝ)^2*((K+1-s).factorial:ℝ)) := by ring
         _ ≤ _ := mul_le_mul hp hf (by positivity) (by positivity)
  calc _ ≤ ∑_s∈Finset.range (K+1),E^(K+1)*((K+1).factorial:ℝ)^2 := Finset.sum_le_sum hterm
       _ = (K+1:ℕ)*(E^(K+1)*((K+1).factorial:ℝ)^2) := by simp
       _ ≤ (2:ℝ)^(K+1)*(E^(K+1)*((K+1).factorial:ℝ)^2) := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            exact_mod_cast (Nat.le_of_lt (Nat.lt_two_pow_self (n:=K+1)))
       _ = _ := by rw [mul_pow];dsimp only [E];ring
end WP.Analysis

namespace WP.Analysis
lemma gaussian_half_geometric_sum (N:ℕ) :
    (∑n∈Finset.range N,(1/2:ℝ)^n)≤2 := by
  have he:(∑n∈Finset.range N,(1/2:ℝ)^n)=2*(1-(1/2:ℝ)^N) := by
    induction N with
    | zero => simp
    | succ N ih => rw [Finset.sum_range_succ,ih,pow_succ];ring
  rw [he]
  nlinarith [pow_nonneg (by norm_num : (0:ℝ)≤1/2) N]

lemma gaussian_unused_amplitude_tail (B h:ℝ) (hB:0≤B) (hh:0<h) (J K:ℕ)
    (hwindow:B*((J:ℝ)+1)^2/h≤1/2) :
    (∑n∈Finset.range (J-K),B^(K+1+n)*((K+1+n).factorial:ℝ)^2/h^(K+1+n))≤
      2*B^(K+1)*((K+1).factorial:ℝ)^2/h^(K+1) := by
  let t:ℕ→ℝ := fun n=>B^n*(n.factorial:ℝ)^2/h^n
  have ht0(n:ℕ):0≤t n := by dsimp only [t];positivity
  have hstep (n:ℕ) (hn:n≤J) : t (n+1)≤t n*(1/2) := by
    have hnr:(n:ℝ)+1≤(J:ℝ)+1 := by exact_mod_cast Nat.add_le_add_right hn 1
    have hrat:B*((n:ℝ)+1)^2/h≤1/2 := by
      apply le_trans _ hwindow
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity) hnr 2) hB) hh.le
    have he:t (n+1)=t n*(B*((n:ℝ)+1)^2/h) := by
      dsimp only [t]
      rw [Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one,pow_succ,pow_succ]
      field_simp
      <;> ring
    rw [he]
    exact mul_le_mul_of_nonneg_left hrat (ht0 n)
  have hterm(n:ℕ)(hn:K+1+n≤J):t (K+1+n)≤t (K+1)*(1/2:ℝ)^n := by
    induction n with
    | zero => simp
    | succ n ih =>
      have hparent:K+1+n≤J := by omega
      calc _ ≤ t (K+1+n)*(1/2) := by
                  convert hstep (K+1+n) hparent using 1 <;> congr 1 <;> omega
           _ ≤ (t (K+1)*(1/2:ℝ)^n)*(1/2) :=
                mul_le_mul_of_nonneg_right (ih hparent) (by norm_num)
           _ = _ := by rw [pow_succ];ring
  calc _ ≤ ∑n∈Finset.range (J-K),t (K+1)*(1/2:ℝ)^n := by
            apply Finset.sum_le_sum
            intro n hn
            apply hterm
            have ht:=Finset.mem_range.mp hn
            omega
       _ = t (K+1)*(∑n∈Finset.range (J-K),(1/2:ℝ)^n) := (Finset.mul_sum _ _ _).symm
       _ ≤ t (K+1)*2 := mul_le_mul_of_nonneg_left (gaussian_half_geometric_sum (J-K)) (ht0 _)
       _ = _ := by dsimp only [t];ring
end WP.Analysis
