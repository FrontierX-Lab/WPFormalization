import WPFormalization.Analysis.KernelSineReference

/-! A finite exact catalog of the sine-reference zeros in half-integer pi
disks. The positive/negative pairing is injective; integer bounds prove
exhaustion. Simplicity comes from the actual sine-reference derivative. -/
noncomputable section
namespace WP.Analysis

def pairedRealRoots {n:ℕ} (r:Fin n→ℝ) : Fin n⊕Fin n→ℂ
  | Sum.inl i => (r i:ℂ)
  | Sum.inr i => -(r i:ℂ)
lemma pairedRealRoots_injective {n:ℕ} (r:Fin n→ℝ)
    (hpos:∀i,0<r i) (hinj:Function.Injective r) : Function.Injective (pairedRealRoots r) := by
  intro x y h
  cases x with
  | inl i =>
    cases y with
    | inl j =>
      change (r i:ℂ)=(r j:ℂ) at h
      exact congrArg Sum.inl (hinj (Complex.ofReal_inj.mp h))
    | inr j =>
      have he := congrArg Complex.re h
      change r i= -r j at he
      linarith [hpos i,hpos j]
  | inr i =>
    cases y with
    | inl j =>
      have he := congrArg Complex.re h
      change -r i=r j at he
      linarith [hpos i,hpos j]
    | inr j =>
      change -(r i:ℂ)= -(r j:ℂ) at h
      exact congrArg Sum.inr (hinj (Complex.ofReal_inj.mp (neg_inj.mp h)))
def positiveSineRoots (N:ℕ) (i:Fin N) : ℝ := ((i:ℕ)+1:ℝ)*Real.pi
lemma positiveSineRoots_pos (N:ℕ) (i:Fin N) : 0<positiveSineRoots N i := by
  unfold positiveSineRoots
  positivity
lemma positiveSineRoots_injective (N:ℕ) : Function.Injective (positiveSineRoots N) := by
  intro i j hij
  unfold positiveSineRoots at hij
  have hh := (mul_left_inj' Real.pi_ne_zero).mp hij
  have he : (i:ℝ)=(j:ℝ) := by linarith
  apply Fin.ext
  exact_mod_cast he
lemma positiveSineRoots_bound (N:ℕ)(i:Fin N) :
    positiveSineRoots N i<((N:ℝ)+1/2)*Real.pi := by
  have hi : ((i:ℕ):ℝ)+1≤(N:ℝ) := by exact_mod_cast (show (i:ℕ)+1≤N by omega)
  unfold positiveSineRoots
  exact mul_lt_mul_of_pos_right (by linarith) Real.pi_pos
lemma integer_pi_zero_in_pairedRoots (N:ℕ) (k:ℤ) (hk:k≠0)
    (hbound:‖(k:ℂ)*Real.pi‖<((N:ℝ)+1/2)*Real.pi) :
    ∃i:Fin N⊕Fin N,(k:ℂ)*Real.pi=pairedRealRoots (positiveSineRoots N) i := by
  have hn : ‖(k:ℂ)*Real.pi‖=|(k:ℝ)| *Real.pi := by
    rw [norm_mul,show (k:ℂ)=((k:ℝ):ℂ) by simp,Complex.norm_real,Real.norm_eq_abs,
      Complex.norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos]
  rw [hn] at hbound
  have hb : |(k:ℝ)|<(N:ℝ)+1/2 := (mul_lt_mul_iff_left₀ Real.pi_pos).mp hbound
  by_cases hp:0<k
  · have hc: (k.toNat:ℤ)=k := Int.toNat_of_nonneg hp.le
    have hcR: (k.toNat:ℝ)=(k:ℝ) := by exact_mod_cast hc
    have hkN: k≤(N:ℤ) := by
      have hr : (k:ℝ)<(N:ℝ)+1 := lt_of_le_of_lt (le_abs_self _) (by linarith)
      have hi : k<(N:ℤ)+1 := by exact_mod_cast hr
      omega
    let j:Fin N:=⟨k.toNat-1,by omega⟩
    refine ⟨Sum.inl j,?_⟩
    change (k:ℂ)*Real.pi=((((k.toNat-1:ℕ):ℝ)+1)*Real.pi:ℝ)
    have he : ((k.toNat-1:ℕ):ℝ)+1=(k:ℝ) := by
      rw [Nat.cast_sub (by omega),Nat.cast_one,hcR]
      ring
    rw [he]
    push_cast
    rfl
  · have hp':0< -k := by omega
    have hc: ((-k).toNat:ℤ)= -k := Int.toNat_of_nonneg hp'.le
    have hcR: ((-k).toNat:ℝ)= -(k:ℝ) := by exact_mod_cast hc
    have hkN: -k≤(N:ℤ) := by
      have hr : -(k:ℝ)<(N:ℝ)+1 := lt_of_le_of_lt (neg_le_abs _) (by linarith)
      have hi : -k<(N:ℤ)+1 := by exact_mod_cast hr
      omega
    let j:Fin N:=⟨(-k).toNat-1,by omega⟩
    refine ⟨Sum.inr j,?_⟩
    change (k:ℂ)*Real.pi= -(((((-k).toNat-1:ℕ):ℝ)+1)*Real.pi:ℝ)
    have he : (((-k).toNat-1:ℕ):ℝ)+1= -(k:ℝ) := by
      rw [Nat.cast_sub (by omega),Nat.cast_one,hcR]
      ring
    rw [he]
    push_cast
    ring
lemma pairedSineRoots_catalog (N:ℕ) :
    Function.Injective (pairedRealRoots (positiveSineRoots N)) ∧
    (∀ i : Fin N⊕Fin N,
      ‖pairedRealRoots (positiveSineRoots N) i‖<((N:ℝ)+1/2)*Real.pi ∧
      sineReference (pairedRealRoots (positiveSineRoots N) i)=0 ∧
      deriv sineReference (pairedRealRoots (positiveSineRoots N) i)≠0) ∧
    (∀ z : ℂ, ‖z‖<((N:ℝ)+1/2)*Real.pi → sineReference z=0 →
      ∃ i : Fin N⊕Fin N,z=pairedRealRoots (positiveSineRoots N) i) := by
  refine ⟨pairedRealRoots_injective _ (positiveSineRoots_pos N) (positiveSineRoots_injective N),?_,?_⟩
  · intro i
    have hroot : sineReference (pairedRealRoots (positiveSineRoots N) i)=0 := by
      apply (sineReference_zero_iff _).2
      cases i with
      | inl j =>
        refine ⟨(j.val:ℤ)+1,by omega,?_⟩
        dsimp [pairedRealRoots,positiveSineRoots]
        push_cast
        ring
      | inr j =>
        refine ⟨-((j.val:ℤ)+1),by omega,?_⟩
        dsimp [pairedRealRoots,positiveSineRoots]
        push_cast
        ring
    refine ⟨?_,hroot,sineReference_simple _ hroot⟩
    cases i with
    | inl j =>
      change ‖(positiveSineRoots N j:ℂ)‖<_
      rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos (positiveSineRoots_pos N j)]
      exact positiveSineRoots_bound N j
    | inr j =>
      change ‖-(positiveSineRoots N j:ℂ)‖<_
      rw [norm_neg,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (positiveSineRoots_pos N j)]
      exact positiveSineRoots_bound N j
  · intro z hz hzero
    obtain ⟨k,hk,rfl⟩ := (sineReference_zero_iff z).mp hzero
    exact integer_pi_zero_in_pairedRoots N k hk hz
end WP.Analysis
