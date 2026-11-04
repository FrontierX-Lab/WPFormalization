import WPFormalization.HigherOrder.ComplexDescentMajorant
import WPFormalization.HigherOrder.ComplexRatioMajorant
import WPFormalization.HigherOrder.SmallComponentCounts
import WPFormalization.HigherOrder.PositiveSeriesBounds
/-! Actual finite KdV scalar coefficient estimates, with uniform marking and
loss control. Profile coefficients at the current order and scalar coefficients
at strictly earlier orders are the displayed local induction data. -/
set_option maxHeartbeats 800000
noncomputable section
namespace WP.HigherOrder.ComplexCanonical
open PowerSeries

def genusSeparatingMajorant (K : ℕ) (B : ℝ) (g a : WP.HigherOrder.Series) : WP.HigherOrder.Series :=
  ∑j∈Finset.range (K+1),∑s∈Finset.range (K+1),
    if 1≤2*j+s ∧ 2*j+s≤K then
      PowerSeries.C (B^(2*j+s))*(PowerSeries.X^(2*j+s)*
        ((((PowerSeries.exp ℝ)^2)*g)^(2*j+s)*a^j)) else 0

lemma genusSeparatingMajorant_coeff (K : ℕ) (B : ℝ) (g a : WP.HigherOrder.Series) :
    PowerSeries.coeff K (genusSeparatingMajorant K B g a)=
      ∑j∈Finset.range (K+1),∑s∈Finset.range (K+1),if 1≤2*j+s ∧ 2*j+s≤K then
        B^(2*j+s)*PowerSeries.coeff (K-(2*j+s)) ((((PowerSeries.exp ℝ)^2)*g)^(2*j+s)*a^j) else 0 := by
  simp only [genusSeparatingMajorant,map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro s hs
  split_ifs with h
  · rw [PowerSeries.coeff_C_mul,PowerSeries.coeff_X_pow_mul',ite_eq_left h.2]
  · simp

lemma genus_configuration_norm_bound (P : PsiTheory) (R : ℂ → ℂ) (z : ℂ) (F : HierarchyJet)
    (M : ℝ) (hM : 1≤M) (K p j s : ℕ) (hp : 2≤p) (hs : s<p-1)
    (hstable : Stable j (s+2)) (hr : 1≤2*j+s) (hrK : 2*j+s≤K)
    (A₀ T : ℝ) (hA₀ : 0≤A₀) (hA : ‖kernelA R z‖≤A₀) (hT : 1≤T)
    (hsmall : ∀g:ℕ,∀d:List ℕ,Stable g d.length →
      ‖smallW P R z g d‖≤Real.Gamma (complexity g d.length:ℝ)*T^(complexity g d.length))
    (g a : WP.HigherOrder.Series) (hg : ∀n,0≤PowerSeries.coeff n g) (ha : ∀n,0≤PowerSeries.coeff n a)
    (hcusp : ∀i:ℕ,i≤K-1 → ∀q:ℕ,1≤q → ‖PowerSeries.coeff i (F.cusp q)‖≤
      (scalarOrderWeight M i q)^(2*i)*PowerSeries.coeff i g)
    (hgenus : ∀i:ℕ,i≤K-1 → ∀q:ℕ,1≤q → ‖PowerSeries.coeff i (F.genus q)‖≤
      (scalarOrderWeight M i q)^(2*i)*PowerSeries.coeff i a) :
    ‖PowerSeries.coeff K (PowerSeries.C ((Nat.choose (p-2) s:ℂ)*smallW P R z j (List.replicate (s+2) 0))*
      ratioSeries R z F p j s)‖≤
      (scalarOrderWeight M K p)^(2*K)*(T*A₀)^(2*j+s)*
        PowerSeries.coeff (K-(2*j+s)) ((((PowerSeries.exp ℝ)^2)*g)^(2*j+s)*a^j) := by
  let r := 2*j+s
  let S := scalarOrderWeight M K p
  have hM0 : 0≤M := by linarith
  have hS1 : 1≤S := by
    have hpR : (1:ℝ)≤p := by exact_mod_cast (show 1≤p by omega)
    dsimp only [S,scalarOrderWeight]
    linarith [mul_nonneg hM0 (Nat.cast_nonneg (α:=ℝ) K)]
  have hS0 : 0≤S := by linarith
  have hsmallj : ‖smallW P R z j (List.replicate (s+2) 0)‖≤Real.Gamma (r:ℝ)*T^r := by
    have hh := hsmall j (List.replicate (s+2) 0) (by simpa only [List.length_replicate] using hstable)
    have hcomp : complexity j (List.replicate (s+2) 0).length=r := by
      simp only [List.length_replicate]
      dsimp only [complexity,r]
      omega
    simpa only [hcomp] using hh
  have hcount : (Nat.choose (p-2) s:ℝ)*‖smallW P R z j (List.replicate (s+2) 0)‖≤S^r*T^r := by
    calc
      _ ≤ (Nat.choose (p-2) s:ℝ)*(Real.Gamma (r:ℝ)*T^r) :=
        mul_le_mul_of_nonneg_left hsmallj (Nat.cast_nonneg _)
      _ = ((Nat.choose (p-2) s:ℝ)*Real.Gamma (r:ℝ))*T^r := by ring
      _ ≤ (((p-2+r:ℕ):ℝ)^r)*T^r :=
        mul_le_mul_of_nonneg_right (choose_gamma_le_add_pow (p-2) r s hr (by dsimp only [r];omega)) (by positivity)
      _ ≤ S^r*T^r := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        apply pow_le_pow_left₀ (Nat.cast_nonneg _)
        have hnat : p-2+r≤p+K := by dsimp only [r] at hrK ⊢;omega
        have hnatR : ((p-2+r:ℕ):ℝ)≤((p+K:ℕ):ℝ) := by exact_mod_cast hnat
        have hm := mul_le_mul_of_nonneg_right hM (Nat.cast_nonneg (α:=ℝ) K)
        dsimp only [S,scalarOrderWeight]
        norm_num only [Nat.cast_add] at hnatR ⊢
        linarith
  have hratio := ratioSeries_scalar_order_norm_bound R z F M hM p j s (K-r) K (by omega) (by omega)
    hr (by dsimp only [r];omega) S le_rfl g a hg ha hcusp hgenus
  have hrK' : r≤K := hrK
  rw [Nat.sub_add_cancel hrK'] at hratio
  have hQ : 0≤PowerSeries.coeff (K-r) ((((PowerSeries.exp ℝ)^2)*g)^r*a^j) :=
    coeff_mul_nonneg (coeff_pow_nonneg (coeff_mul_nonneg (coeff_pow_nonneg exp_coeff_nonneg 2) hg) r)
      (coeff_pow_nonneg ha j) _
  have hratio' : ‖PowerSeries.coeff K (ratioSeries R z F p j s)‖≤
      A₀^r*S^(2*(K-r))*PowerSeries.coeff (K-r) ((((PowerSeries.exp ℝ)^2)*g)^r*a^j) := by
    apply hratio.trans
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (norm_nonneg _) hA r) (pow_nonneg hS0 _)) hQ
  rw [PowerSeries.coeff_C_mul,norm_mul,norm_mul,Complex.norm_natCast]
  apply (mul_le_mul hcount hratio' (norm_nonneg _) (mul_nonneg (pow_nonneg hS0 _) (by positivity))).trans
  have hpow : S^(r+2*(K-r))≤S^(2*K) := pow_le_pow_right₀ hS1 (by omega)
  have hh := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hpow
    (pow_nonneg (mul_nonneg (by linarith : 0≤T) hA₀) r)) hQ
  convert! hh using 1 <;>dsimp only [r] <;>rw [mul_pow] <;>ring


lemma sum_range_le_of_zero_above (K N : ℕ) (f : ℕ → ℝ)
    (hf : ∀s,0≤f s) (hz : ∀s,K<s → f s=0) :
    ∑s∈Finset.range N,f s≤∑s∈Finset.range (K+1),f s := by
  have he : ∑s∈Finset.range N,f s=∑s∈Finset.range N∩Finset.range (K+1),f s := by
    symm
    apply Finset.sum_subset Finset.inter_subset_left
    intro s hs hn
    have hn' : ¬s<K+1 := by
      simpa only [Finset.mem_inter,hs,true_and,Finset.mem_range] using hn
    exact hz s (by omega)
  rw [he]
  exact Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right (fun s _ _=>hf s)

lemma genusSeries_uniform_norm_majorant (P : PsiTheory) (R : ℂ → ℂ) (z : ℂ) (F : HierarchyJet)
    (profiles : List ℕ → Series) (M : ℝ) (hM : 1≤M) (K p : ℕ) (hp : 2≤p)
    (A₀ T : ℝ) (hA₀ : 0≤A₀) (hA : ‖kernelA R z‖≤A₀) (hT : 1≤T)
    (hsmall : ∀g:ℕ,∀d:List ℕ,Stable g d.length →
      ‖smallW P R z g d‖≤Real.Gamma (complexity g d.length:ℝ)*T^(complexity g d.length))
    (e g a : WP.HigherOrder.Series) (he : ∀n,0≤PowerSeries.coeff n e)
    (hg : ∀n,0≤PowerSeries.coeff n g) (ha : ∀n,0≤PowerSeries.coeff n a)
    (hprofile : ∀d:List ℕ,1≤d.length → ‖PowerSeries.coeff K (profiles d)‖≤
      (profileOrderWeight M K d)^(2*K)*PowerSeries.coeff K e)
    (hcusp : ∀i:ℕ,i≤K-1 → ∀q:ℕ,1≤q → ‖PowerSeries.coeff i (F.cusp q)‖≤
      (scalarOrderWeight M i q)^(2*i)*PowerSeries.coeff i g)
    (hgenus : ∀i:ℕ,i≤K-1 → ∀q:ℕ,1≤q → ‖PowerSeries.coeff i (F.genus q)‖≤
      (scalarOrderWeight M i q)^(2*i)*PowerSeries.coeff i a) :
    ‖PowerSeries.coeff K (genusSeries P R z F profiles K p)‖≤
      (scalarOrderWeight M K p)^(2*K)*PowerSeries.coeff K
        (PowerSeries.C (Real.exp 6)*e+PowerSeries.C 3*genusSeparatingMajorant K (T*A₀) g a) := by
  let S := scalarOrderWeight M K p
  let B := T*A₀
  let Q := fun j s=>((((PowerSeries.exp ℝ)^2)*g)^(2*j+s)*a^j)
  let f := fun j s=>if 1≤2*j+s ∧ 2*j+s≤K then B^(2*j+s)*PowerSeries.coeff (K-(2*j+s)) (Q j s) else 0
  let H : Series := ∑j∈Finset.range (K+1),∑s∈Finset.range (p-1),
    if Stable j (s+2) ∧ 1≤2*j+s ∧ 2*j+s≤K then
      PowerSeries.C ((Nat.choose (p-2) s:ℂ)*smallW P R z j (List.replicate (s+2) 0))*
        ratioSeries R z F p j s else 0
  have hM0 : 0≤M := by linarith
  have hS0 : 0≤S := by dsimp only [S,scalarOrderWeight];positivity
  have hB : 0≤B := mul_nonneg (by linarith) hA₀
  have hQ (j s : ℕ) : ∀n,0≤PowerSeries.coeff n (Q j s) :=
    coeff_mul_nonneg (coeff_pow_nonneg (coeff_mul_nonneg (coeff_pow_nonneg exp_coeff_nonneg 2) hg) (2*j+s))
      (coeff_pow_nonneg ha j)
  have hf (j s : ℕ) : 0≤f j s := by
    dsimp only [f]
    split_ifs
    · exact mul_nonneg (pow_nonneg hB _) (hQ j s _)
    · exact le_rfl
  have hterm (j s : ℕ) (hs : s<p-1) :
      ‖PowerSeries.coeff K (if Stable j (s+2) ∧ 1≤2*j+s ∧ 2*j+s≤K then
        PowerSeries.C ((Nat.choose (p-2) s:ℂ)*smallW P R z j (List.replicate (s+2) 0))*
          ratioSeries R z F p j s else 0)‖≤S^(2*K)*f j s := by
    by_cases ht : Stable j (s+2) ∧ 1≤2*j+s ∧ 2*j+s≤K
    · rw [ite_eq_left ht]
      dsimp only [f]
      rw [ite_eq_left ht.2]
      simpa only [S,B,Q,mul_assoc] using
        genus_configuration_norm_bound P R z F M hM K p j s hp hs ht.1 ht.2.1 ht.2.2
          A₀ T hA₀ hA hT hsmall g a hg ha hcusp hgenus
    · rw [ite_eq_right ht,map_zero,norm_zero]
      exact mul_nonneg (pow_nonneg hS0 _) (hf j s)
  have hH : ‖PowerSeries.coeff K H‖≤S^(2*K)*PowerSeries.coeff K (genusSeparatingMajorant K B g a) := by
    simp only [H,map_sum]
    calc
      _ ≤ ∑j∈Finset.range (K+1),‖∑s∈Finset.range (p-1),PowerSeries.coeff K
          (if Stable j (s+2) ∧ 1≤2*j+s ∧ 2*j+s≤K then
            PowerSeries.C ((Nat.choose (p-2) s:ℂ)*smallW P R z j (List.replicate (s+2) 0))*
              ratioSeries R z F p j s else 0)‖ := norm_sum_le _ _
      _ ≤ ∑j∈Finset.range (K+1),∑s∈Finset.range (p-1),‖PowerSeries.coeff K
          (if Stable j (s+2) ∧ 1≤2*j+s ∧ 2*j+s≤K then
            PowerSeries.C ((Nat.choose (p-2) s:ℂ)*smallW P R z j (List.replicate (s+2) 0))*
              ratioSeries R z F p j s else 0)‖ := Finset.sum_le_sum (fun j hj=>norm_sum_le _ _)
      _ ≤ ∑j∈Finset.range (K+1),∑s∈Finset.range (p-1),S^(2*K)*f j s :=
        Finset.sum_le_sum (fun j hj=>Finset.sum_le_sum (fun s hs=>hterm j s (Finset.mem_range.mp hs)))
      _ = S^(2*K)*(∑j∈Finset.range (K+1),∑s∈Finset.range (p-1),f j s) := by simp only [Finset.mul_sum]
      _ ≤ S^(2*K)*(∑j∈Finset.range (K+1),∑s∈Finset.range (K+1),f j s) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun j hj=>
          sum_range_le_of_zero_above K (p-1) (f j) (hf j) (by
            intro s hs
            dsimp only [f]
            rw [ite_eq_right (by omega)]))) (pow_nonneg hS0 _)
      _ = _ := by rw [genusSeparatingMajorant_coeff]
  have hlen : (1::List.replicate (p-1) 0).length=p := by
    simp only [List.length_cons,List.length_replicate]
    omega
  have hweight : profileOrderWeight M K (1::List.replicate (p-1) 0)=S+1 := by
    unfold profileOrderWeight
    rw [hlen]
    simp only [List.sum_cons,List.sum_replicate,nsmul_zero,add_zero,Nat.cast_one]
    dsimp only [S,scalarOrderWeight]
    ring
  have hSp : S+1≤(p:ℝ)+M*(K+1)+2 := by dsimp only [S,scalarOrderWeight];nlinarith
  have hpow : (S+1)^(2*K)≤Real.exp 6*S^(2*K) :=
    (pow_le_pow_left₀ (by positivity : 0≤S+1) hSp _).trans (scalar_weight_succ_offset_pow M hM K p (by omega))
  have hprof : ‖PowerSeries.coeff K (profiles (1::List.replicate (p-1) 0))‖≤
      Real.exp 6*S^(2*K)*PowerSeries.coeff K e := by
    have hh := hprofile (1::List.replicate (p-1) 0) (by simp)
    rw [hweight] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right hpow (he K))
  change ‖PowerSeries.coeff K (profiles (1::List.replicate (p-1) 0)-PowerSeries.C 3*H)‖≤_
  rw [map_sub,PowerSeries.coeff_C_mul]
  calc
    _ ≤ ‖PowerSeries.coeff K (profiles (1::List.replicate (p-1) 0))‖+3*‖PowerSeries.coeff K H‖ := by
      simpa only [norm_mul,Complex.norm_ofNat] using norm_sub_le
        (PowerSeries.coeff K (profiles (1::List.replicate (p-1) 0))) ((3:ℂ)*PowerSeries.coeff K H)
    _ ≤ Real.exp 6*S^(2*K)*PowerSeries.coeff K e+3*(S^(2*K)*PowerSeries.coeff K (genusSeparatingMajorant K B g a)) :=
      add_le_add hprof (mul_le_mul_of_nonneg_left hH (by norm_num))
    _ = _ := by
      rw [map_add,PowerSeries.coeff_C_mul,PowerSeries.coeff_C_mul]
      dsimp only [S,B]
      ring

end WP.HigherOrder.ComplexCanonical
