import WPFormalization.Analysis.KernelMomentBounds
import WPFormalization.HigherOrder.BMoments
import Mathlib.Data.Nat.Choose.Central

/-! One common geometric Cauchy bound controls every actual kernel and signed dilaton absolute moment by C B^q q!, with even moments bounded by C B^j (j!)^2. Constants precede all orders and parameters. -/
noncomputable section
namespace WP.Analysis
lemma geometric_factorial_moment_bound (R M : ℝ) (hR : 1<R) (hM : 0<M) :
    ∃ C B : ℝ,0<C ∧ 0<B ∧ ∀f:ℕ→ℝ,(∀n,|f n|≤M/R^n)→∀q:ℕ,
      Summable (fun n:ℕ=>((n:ℝ)+1)^q*|f n|) ∧
      (∑'n:ℕ,((n:ℝ)+1)^q*|f n|)≤C*B^q*(q.factorial:ℝ) := by
  let α:=Real.log R/2
  let ρ:=Real.exp α/R
  have hRp : 0<R := by linarith
  have hα : 0<α := by dsimp [α];exact div_pos (Real.log_pos hR) (by norm_num)
  have hρp : 0<ρ := div_pos (Real.exp_pos _) hRp
  have hexp : Real.exp α<R := by
    calc Real.exp α<Real.exp (Real.log R) := Real.exp_lt_exp.mpr (by dsimp [α];linarith [Real.log_pos hR])
         _=R := Real.exp_log hRp
  have hρ1 : ρ<1 := (div_lt_one hRp).2 hexp
  have hden : 0<1-ρ := by linarith
  have hsρ : HasSum (fun n:ℕ=>ρ^n) (1-ρ)⁻¹ :=
    hasSum_geometric_of_abs_lt_one (by rw [abs_of_pos hρp];exact hρ1)
  refine ⟨M*Real.exp α/(1-ρ),α⁻¹,by positivity,by positivity,?_⟩
  intro f hf q
  have hfact : 0<(q.factorial:ℝ) := by exact_mod_cast q.factorial_pos
  have hp (n:ℕ) : ((n:ℝ)+1)^q≤(q.factorial:ℝ)*(α⁻¹)^q*Real.exp (α*((n:ℝ)+1)) := by
    apply (mul_le_mul_iff_right₀ (pow_pos hα q)).mp
    calc α^q*((n:ℝ)+1)^q=(α*((n:ℝ)+1))^q := by rw [mul_pow]
         _≤Real.exp (α*((n:ℝ)+1))*(q.factorial:ℝ) :=
           (div_le_iff₀ hfact).mp (Real.pow_div_factorial_le_exp (α*((n:ℝ)+1)) (by positivity) q)
         _=α^q*((q.factorial:ℝ)*α⁻¹^q*Real.exp (α*((n:ℝ)+1))) := by
           rw [inv_pow]
           field_simp
  let K:=M*Real.exp α*α⁻¹^q*(q.factorial:ℝ)
  have hK : 0≤K := by dsimp [K];positivity
  have hmajor : Summable (fun n:ℕ=>K*ρ^n) := hsρ.summable.mul_left K
  have hpoint (n:ℕ) : ((n:ℝ)+1)^q*|f n|≤K*ρ^n := by
    apply (mul_le_mul (hp n) (hf n) (abs_nonneg _) (by positivity)).trans_eq
    have he : Real.exp (α*((n:ℝ)+1))=Real.exp α*(Real.exp α)^n := by
      rw [show α*((n:ℝ)+1)=(n:ℝ)*α+α by ring,Real.exp_add,Real.exp_nat_mul]
      ring
    rw [he]
    dsimp [K,ρ]
    rw [div_pow]
    ring
  have hs : Summable (fun n:ℕ=>((n:ℝ)+1)^q*|f n|) :=
    Summable.of_nonneg_of_le (fun n=>by positivity) hpoint hmajor
  refine ⟨hs,?_⟩
  calc _≤∑'n:ℕ,K*ρ^n := hs.tsum_le_tsum hpoint hmajor
       _=K*(1-ρ)⁻¹ := (hsρ.mul_left K).tsum_eq
       _=(M*Real.exp α/(1-ρ))*α⁻¹^q*(q.factorial:ℝ) := by dsimp [K];ring

lemma weight_factorial_moments : ∃ C B : ℝ,0<C ∧ 0<B ∧ ∀q:ℕ,
    ∀Y∈Set.Icc (0:ℝ) y₀,
      Summable (fun l:ℕ=>((l:ℝ)+1)^q*|weight Y l|) ∧
      (∑'l:ℕ,((l:ℝ)+1)^q*|weight Y l|)≤C*B^q*(q.factorial:ℝ) := by
  obtain ⟨R,M,hR,hM,hpoint⟩:=weight_norm_geometric_bound
  obtain ⟨C,B,hC,hB,hbound⟩:=geometric_factorial_moment_bound R M hR hM
  exact ⟨C,B,hC,hB,fun q Y hY=>hbound (weight Y) (hpoint Y hY) q⟩

lemma dilaton_factorial_moments : ∃ C B : ℝ,0<C ∧ 0<B ∧ ∀q:ℕ,
    ∀Y∈Set.Icc (0:ℝ) y₀,
      Summable (fun d:ℕ=>((d:ℝ)+1)^q*|canonicalDilatonCoefficient Y d|) ∧
      (∑'d:ℕ,((d:ℝ)+1)^q*|canonicalDilatonCoefficient Y d|)≤C*B^q*(q.factorial:ℝ) := by
  obtain ⟨M,hM,hpoint⟩:=barH_radius_two_coefficient_bound
  obtain ⟨C,B,hC,hB,hbound⟩:=geometric_factorial_moment_bound 2 (2*M/3) (by norm_num) (by positivity)
  refine ⟨C,B,hC,hB,?_⟩
  intro q Y hY
  apply hbound
  intro d
  cases d with
  | zero => simp [canonicalDilatonCoefficient];positivity
  | succ d =>
    simp only [canonicalDilatonCoefficient,show 1≤d+1 by omega,ite_true,Nat.add_sub_cancel,
      abs_div,abs_of_pos (by norm_num:(0:ℝ)<3)]
    apply (div_le_div_of_nonneg_right (hpoint Y hY d) (by norm_num:(0:ℝ)≤3)).trans_eq
    rw [pow_succ]
    ring

lemma factorial_double_le_four_pow (j:ℕ) : ((2*j).factorial:ℝ)≤(4:ℝ)^j*(j.factorial:ℝ)^2 := by
  have h:=Nat.centralBinom_le_four_pow j
  rw [Nat.centralBinom_eq_two_mul_choose] at h
  have he:=Nat.choose_mul_factorial_mul_factorial (show j≤2*j by omega)
  have he' : (Nat.choose (2*j) j:ℝ)*(j.factorial:ℝ)^2=((2*j).factorial:ℝ) := by
    have hh : 2*j-j=j := by omega
    rw [hh] at he
    rw [pow_two,←mul_assoc]
    exact_mod_cast he
  rw [←he']
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast h) (sq_nonneg _)
lemma weight_even_factorial_moments : ∃ C B : ℝ,0<C ∧ 0<B ∧ ∀j:ℕ,
    ∀Y∈Set.Icc (0:ℝ) y₀,
      Summable (fun l:ℕ=>((l:ℝ)+1)^(2*j)*|weight Y l|) ∧
      (∑'l:ℕ,((l:ℝ)+1)^(2*j)*|weight Y l|)≤C*B^j*(j.factorial:ℝ)^2 := by
  obtain ⟨C,B,hC,hB,hbound⟩:=weight_factorial_moments
  refine ⟨C,4*B^2,hC,by positivity,?_⟩
  intro j Y hY
  refine ⟨(hbound (2*j) Y hY).1,?_⟩
  calc _≤C*B^(2*j)*((2*j).factorial:ℝ) := (hbound (2*j) Y hY).2
       _≤C*B^(2*j)*((4:ℝ)^j*(j.factorial:ℝ)^2) :=
         mul_le_mul_of_nonneg_left (factorial_double_le_four_pow j) (by positivity)
       _=C*(4*B^2)^j*(j.factorial:ℝ)^2 := by rw [mul_pow,pow_mul];ring

lemma dilaton_even_factorial_moments : ∃ C B : ℝ,0<C ∧ 0<B ∧ ∀j:ℕ,
    ∀Y∈Set.Icc (0:ℝ) y₀,
      Summable (fun d:ℕ=>((d:ℝ)+1)^(2*j)*|canonicalDilatonCoefficient Y d|) ∧
      (∑'d:ℕ,((d:ℝ)+1)^(2*j)*|canonicalDilatonCoefficient Y d|)≤C*B^j*(j.factorial:ℝ)^2 := by
  obtain ⟨C,B,hC,hB,hbound⟩:=dilaton_factorial_moments
  refine ⟨C,4*B^2,hC,by positivity,?_⟩
  intro j Y hY
  refine ⟨(hbound (2*j) Y hY).1,?_⟩
  calc _≤C*B^(2*j)*((2*j).factorial:ℝ) := (hbound (2*j) Y hY).2
       _≤C*B^(2*j)*((4:ℝ)^j*(j.factorial:ℝ)^2) :=
         mul_le_mul_of_nonneg_left (factorial_double_le_four_pow j) (by positivity)
       _=C*(4*B^2)^j*(j.factorial:ℝ)^2 := by rw [mul_pow,pow_mul];ring
end WP.Analysis
