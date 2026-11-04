import WPFormalization.HigherOrder.SmallComponentBounds

/-! Label-subset binomials times the genuine bounded-component Gamma scale obey the loss-r polynomial count. The generic norm estimate also applies to complex amplitudes once their actual Gamma bound is instantiated. -/
noncomputable section
namespace WP.HigherOrder
lemma choose_mul_factorial_le_add_pow (p r s:ℕ) (hr:1≤r) (hs:s≤r) :
    Nat.choose p s*(r-1).factorial≤(p+r)^r := by
  have hchoose:Nat.choose p s*s.factorial≤p^s := by
    rw[Nat.mul_comm,←Nat.descFactorial_eq_factorial_mul_choose]
    exact Nat.descFactorial_le_pow p s
  by_cases hsr:s≤r-1
  · have heq:(r-1).factorial=s.factorial*(s+1).ascFactorial (r-1-s):=by
      rw[Nat.factorial_mul_ascFactorial]
      congr 1
      omega
    have hasc:(s+1).ascFactorial (r-1-s)≤r^(r-1-s):=by
      exact (Nat.ascFactorial_le_pow_add s (r-1-s)).trans
        (Nat.pow_le_pow_left (by omega) _)
    calc Nat.choose p s*(r-1).factorial
        = (Nat.choose p s*s.factorial)*(s+1).ascFactorial (r-1-s):=by rw[heq];ring
      _≤p^s*r^(r-1-s):=Nat.mul_le_mul hchoose hasc
      _≤(p+r)^s*(p+r)^(r-1-s):=Nat.mul_le_mul
        (Nat.pow_le_pow_left (by omega) _) (Nat.pow_le_pow_left (by omega) _)
      _=(p+r)^(r-1):=by rw[←pow_add];congr 1;omega
      _≤(p+r)^r:=Nat.pow_le_pow_right (by omega) (by omega)
  · have hsr':s=r:=by omega
    subst s
    exact ((Nat.mul_le_mul_left _ (Nat.factorial_le (by omega : r-1≤r))).trans hchoose).trans
      (Nat.pow_le_pow_left (by omega) _)
lemma choose_gamma_le_add_pow (p r s:ℕ) (hr:1≤r) (hs:s≤r) :
    (Nat.choose p s:ℝ)*Real.Gamma (r:ℝ)≤((p+r:ℕ):ℝ)^r := by
  have he:r=(r-1)+1:=by omega
  rw[he,Nat.cast_add,Nat.cast_one,Real.Gamma_nat_eq_factorial]
  norm_cast
  simpa only[←he] using choose_mul_factorial_le_add_pow p r s hr hs
lemma Gamma_nat_sub_one_le (r:ℕ) (hr:2≤r) :
    Real.Gamma ((r-1:ℕ):ℝ)≤Real.Gamma (r:ℝ) := by
  have hG (n:ℕ) (hn:1≤n) : Real.Gamma (n:ℝ)=((n-1).factorial:ℝ):=by
    have he:n=n-1+1:=by omega
    conv_lhs=>rw[he,Nat.cast_add,Nat.cast_one,Real.Gamma_nat_eq_factorial]
  rw[hG r (by omega),hG (r-1) (by omega)]
  exact_mod_cast Nat.factorial_le (by omega : r-1-1≤r-1)
lemma small_component_label_norm_bound {𝕜:Type*} [SeminormedAddCommGroup 𝕜]
    (p r s:ℕ) (hr:2≤r) (hs:s≤r) (T S:ℝ) (hT:1≤T) (hS:((p+r:ℕ):ℝ)≤S)
    (W:𝕜) (hW:‖W‖≤Real.Gamma ((r-1:ℕ):ℝ)*T^(r-1)) :
    (Nat.choose p s:ℝ)*‖W‖≤(T*S)^r := by
  have hS0:0≤S:=(Nat.cast_nonneg (p+r)).trans hS
  have hT0:0≤T:=by linarith
  have hG:0≤Real.Gamma ((r-1:ℕ):ℝ):=(Real.Gamma_pos_of_pos (by exact_mod_cast (show 0<r-1 by omega))).le
  have hchoose:=choose_gamma_le_add_pow p r s (by omega) hs
  have hgamma:=Gamma_nat_sub_one_le r hr
  have hpow:T^(r-1)≤T^r:=pow_le_pow_right₀ hT (by omega)
  calc
    _≤(Nat.choose p s:ℝ)*(Real.Gamma ((r-1:ℕ):ℝ)*T^(r-1)):=
      mul_le_mul_of_nonneg_left hW (Nat.cast_nonneg _)
    _≤(Nat.choose p s:ℝ)*(Real.Gamma (r:ℝ)*T^r):=
      mul_le_mul_of_nonneg_left (mul_le_mul hgamma hpow (pow_nonneg hT0 _) ((hG.trans hgamma))) (Nat.cast_nonneg _)
    _=((Nat.choose p s:ℝ)*Real.Gamma (r:ℝ))*T^r:=by ring
    _≤((p+r:ℕ):ℝ)^r*T^r:=mul_le_mul_of_nonneg_right hchoose (pow_nonneg hT0 _)
    _≤S^r*T^r:=mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (Nat.cast_nonneg _) hS _) (pow_nonneg hT0 _)
    _=(T*S)^r:=by rw[mul_pow];ring
lemma smallW_profile_label_count_bound (P:PsiTheory) : ∃T:ℝ,1≤T ∧
    ∀p j s:ℕ,∀d:List ℕ,d.length=s+1→Stable j (s+1)→2≤2*j+s→
      ∀Y∈Set.Icc (0:ℝ) y₀,
        (Nat.choose p s:ℝ)*|smallW P Y j d|≤(T*((p+2*j+s:ℕ):ℝ))^(2*j+s) := by
  obtain ⟨T,hT,hdata⟩:=smallW_real_uniform_complexity_bound P
  refine ⟨T,hT,?_⟩
  intro p j s d hd hst hr Y hY
  have hw:=hdata j d (by simpa only[hd] using hst) (by omega) Y hY
  have hc:complexity j d.length=2*j+s-1:=by rw[hd];unfold complexity;omega
  rw[hc] at hw
  have hb:=small_component_label_norm_bound p (2*j+s) s hr (by omega) T ((p+2*j+s:ℕ):ℝ)
    hT (by push_cast;ring_nf;exact le_rfl) (smallW P Y j d) (by simpa only[Real.norm_eq_abs] using hw)
  simpa only[Real.norm_eq_abs] using hb
end WP.HigherOrder
