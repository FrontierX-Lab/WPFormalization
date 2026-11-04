import Mathlib
noncomputable section
namespace WP.Analysis
lemma sum_triangle_reindex {R:Type*} [AddCommMonoid R] (A:ℕ → ℕ → R) (K:ℕ):
    (∑s∈Finset.range (K+1),∑i∈Finset.range (K-s+1),A s i)=
      ∑n∈Finset.range (K+1),∑s∈Finset.range (n+1),A s (n-s):=by
  rw[Finset.sum_sigma',Finset.sum_sigma']
  apply Finset.sum_bij (fun p hp=>(⟨p.1+p.2,p.1⟩:Sigma (fun _:ℕ=>ℕ)))
  · intro p hp
    simp only[Finset.mem_sigma,Finset.mem_range] at hp ⊢
    omega
  · intro p hp q hq he
    have h1:=congrArg Sigma.fst he
    have h2:=congrArg Sigma.snd he
    apply Sigma.ext h2
    simpa only[heq_eq_eq] using (show p.2=q.2 by dsimp at h1 h2;omega)
  · intro q hq
    simp only[Finset.mem_sigma,Finset.mem_range] at hq
    refine ⟨⟨q.2,q.1-q.2⟩,?_,?_⟩
    · simp only[Finset.mem_sigma,Finset.mem_range]
      omega
    · apply Sigma.ext (by dsimp;omega)
      rfl
  · intro p hp
    simp
lemma factorial_mixed_le_square (s i:ℕ):
    (s.factorial:ℝ)^2*(i.factorial:ℝ)≤((s+i).factorial:ℝ)^2:=by
  have hf:s.factorial*i.factorial≤(s+i).factorial:=
    Nat.le_of_dvd (Nat.factorial_pos _) (Nat.factorial_mul_factorial_dvd_factorial_add s i)
  have hfr:(s.factorial:ℝ)*(i.factorial:ℝ)≤((s+i).factorial:ℝ):=by exact_mod_cast hf
  have hi1:(1:ℝ) ≤ (i.factorial:ℝ):=by exact_mod_cast (Nat.succ_le_of_lt (Nat.factorial_pos i))
  have hpow:=pow_le_pow_left₀ (by positivity) hfr 2
  have hii:(i.factorial:ℝ)≤(i.factorial:ℝ)^2:=by nlinarith
  have hh:=mul_le_mul_of_nonneg_left hii (sq_nonneg (s.factorial:ℝ))
  nlinarith
end WP.Analysis
namespace WP.Analysis
lemma poisson_diagonal_convolution_bound (a:ℕ→ℕ→ℂ) (C B D:ℝ)
    (hC:0<C) (hB:0<B) (hD:0<D)
    (ha:∀s i,‖a s i‖≤C*B^s*(s.factorial:ℝ)^2*D^(i+1)*(i.factorial:ℝ)) (n:ℕ):
    ‖∑s∈Finset.range (n+1),a s (n-s)‖≤
      (2*C*D)*(2*max B D)^n*(n.factorial:ℝ)^2:=by
  let E:ℝ:=max B D
  have hE:0<E:=hB.trans_le (le_max_left _ _)
  have hterm(s:ℕ) (hs:s∈Finset.range (n+1)):
      ‖a s (n-s)‖≤C*D*E^n*(n.factorial:ℝ)^2:=by
    have hsle:s≤n:=Nat.le_of_lt_succ (Finset.mem_range.mp hs)
    have hp:B^s*D^(n-s)≤E^n:=by
      calc
        _≤E^s*E^(n-s):=mul_le_mul
          (pow_le_pow_left₀ hB.le (le_max_left _ _) _) (pow_le_pow_left₀ hD.le (le_max_right _ _) _)
          (by positivity) (by positivity)
        _=E^n:=by rw[←pow_add, Nat.add_sub_of_le hsle]
    have hf:(s.factorial:ℝ)^2*((n-s).factorial:ℝ)≤(n.factorial:ℝ)^2:=by
      simpa only[Nat.add_sub_of_le hsle] using factorial_mixed_le_square s (n-s)
    calc
      _≤C*B^s*(s.factorial:ℝ)^2*D^(n-s+1)*((n-s).factorial:ℝ):=ha s (n-s)
      _=C*D*(B^s*D^(n-s))*((s.factorial:ℝ)^2*((n-s).factorial:ℝ)):=by rw[pow_succ];ring
      _≤C*D*E^n*(n.factorial:ℝ)^2:=by
        exact mul_le_mul (mul_le_mul_of_nonneg_left hp (by positivity)) hf (by positivity) (by positivity)
  have hcard:((n+1:ℕ):ℝ)≤(2:ℝ)^(n+1):=by exact_mod_cast (Nat.le_of_lt (n+1).lt_two_pow_self)
  calc
    _≤∑s∈Finset.range (n+1),‖a s (n-s)‖:=norm_sum_le _ _
    _≤∑s∈Finset.range (n+1),C*D*E^n*(n.factorial:ℝ)^2:=Finset.sum_le_sum hterm
    _=((n+1:ℕ):ℝ)*(C*D*E^n*(n.factorial:ℝ)^2):=by simp
    _≤(2:ℝ)^(n+1)*(C*D*E^n*(n.factorial:ℝ)^2):=mul_le_mul_of_nonneg_right hcard (by positivity)
    _=_:=by rw[pow_succ,mul_pow];dsimp[E];ring
end WP.Analysis
