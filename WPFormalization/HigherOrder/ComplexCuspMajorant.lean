import WPFormalization.HigherOrder.ComplexOperatorAnalytic
import WPFormalization.HigherOrder.NormCoefficientSum
/-! Actual complex dilaton/cusp scalar norm bound. Constants are uniform in the
order, markings, and parameter, assuming exactly the displayed lower profile
majorant. A harmless uniform exp(6) absorbs the extra index shift. -/
set_option maxHeartbeats 800000
noncomputable section
namespace WP.HigherOrder.ComplexCanonical
open PowerSeries

lemma scalar_weight_succ_offset_pow (M : ℝ) (hM : 1≤M) (j p : ℕ) (hp : 1≤p) :
    ((p:ℝ)+M*(j+1)+2)^(2*j)≤Real.exp 6*(scalarOrderWeight M j p)^(2*j) := by
  let S : ℝ := scalarOrderWeight M j p
  have hM0 : 0≤M := by linarith
  have hp0 : (1:ℝ)≤p := by exact_mod_cast hp
  have hj0 : (0:ℝ)≤j := Nat.cast_nonneg j
  have hS : 0<S := by dsimp only [S,scalarOrderWeight];nlinarith [mul_nonneg hM0 hj0]
  have hoff : 0≤(M+2)/S := div_nonneg (by linarith) hS.le
  have hbase : (p:ℝ)+M*(j+1)+2=S*(1+(M+2)/S) := by
    dsimp only [S,scalarOrderWeight]
    field_simp
    ring
  have hexp : (1+(M+2)/S)^(2*j)≤(Real.exp ((M+2)/S))^(2*j) :=
    pow_le_pow_left₀ (by positivity) (by simpa only [add_comm] using Real.add_one_le_exp ((M+2)/S)) _
  have hpower : (Real.exp ((M+2)/S))^(2*j)=Real.exp (((2*j:ℕ):ℝ)*(M+2)/S) := by
    rw [←Real.exp_nat_mul]
    congr 1
    ring
  have h6 : (((2*j:ℕ):ℝ)*(M+2)/S)≤6 := by
    apply (div_le_iff₀ hS).mpr
    have hm2 : M+2≤3*M := by linarith
    have hb := mul_le_mul_of_nonneg_left hm2 (show (0:ℝ)≤2*j by positivity)
    dsimp only [S,scalarOrderWeight]
    push_cast
    nlinarith
  calc
    _ = S^(2*j)*(1+(M+2)/S)^(2*j) := by rw [hbase,mul_pow]
    _ ≤ S^(2*j)*(Real.exp ((M+2)/S))^(2*j) := mul_le_mul_of_nonneg_left hexp (pow_nonneg hS.le _)
    _ = S^(2*j)*Real.exp (((2*j:ℕ):ℝ)*(M+2)/S) := by rw [hpower]
    _ ≤ S^(2*j)*Real.exp 6 := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr h6) (pow_nonneg hS.le _)
    _ = _ := mul_comm _ _

lemma cuspSeries_uniform_norm_majorant (ρ K A₀ : ℝ) (hρ : 1<ρ) (hK : 0<K) (hA₀ : 0<A₀) :
    ∃ B M₀ : ℝ,0<B ∧ 0<M₀ ∧ ∀R:ℂ→ℂ,∀z:ℂ,
      (∀d:ℕ,‖WP.Analysis.complexDilatonCoefficient R d z‖≤K/ρ^d) → ‖(kernelA R z)⁻¹‖≤A₀ →
      ∀M:ℝ,M₀≤M → ∀j:ℕ,∀F:HierarchyJet,∀e:WP.HigherOrder.Series,
      (∀n:ℕ,0≤PowerSeries.coeff n e) →
      (∀i:ℕ,i≤j → ∀d:List ℕ,1≤d.length → ‖PowerSeries.coeff i (F.profile d)‖≤
        (profileOrderWeight M i d)^(2*i)*PowerSeries.coeff i e) → ∀p:ℕ,1≤p →
      ‖PowerSeries.coeff j (cuspSeries R z F.profile p)‖≤
        B*(scalarOrderWeight M j p)^(2*j)*PowerSeries.coeff j ((PowerSeries.exp ℝ)*e) := by
  obtain ⟨C,M₁,hC,hM₁,hkernel⟩ := geometric_coefficient_tsum_order_bounds (𝕜:=ℂ) ρ K hρ hK
  refine ⟨A₀*C*Real.exp 6,max M₁ 1,by positivity,lt_of_lt_of_le hM₁ (le_max_left _ _),?_⟩
  intro R z hgeom hA M hM j F e he hprofile p hp
  have hMop : M₁≤M := (le_max_left _ _).trans hM
  have hM1 : 1≤M := (le_max_right _ _).trans hM
  have hM0 : 0≤M := by linarith
  let L : ℕ → Series := fun l=>complexityShift (-1) (F.profile ((l+1)::List.replicate p 0))
  have hL (l : ℕ) : ‖PowerSeries.coeff j (L l)‖≤
      PowerSeries.coeff j ((PowerSeries.exp ℝ)*e)*((2:ℝ)+p+M*(j+1)+l+1)^(2*j) := by
    convert! cusp_shifted_profile_norm_polynomial M hM1 j F e he hprofile p j le_rfl l using 1 <;>ring
  have ha : ∀l:ℕ,‖bCoeff R z (l+1)‖≤K/ρ^l := by
    intro l
    calc
      _ ≤ K/ρ^(l+1) := hgeom (l+1)
      _ = (K/ρ^l)/ρ := by rw [pow_succ,div_mul_eq_div_div]
      _ ≤ K/ρ^l := div_le_self (by positivity) hρ.le
  have hEN := coeff_mul_nonneg exp_coeff_nonneg he
  have hop := hkernel M hMop (fun l=>bCoeff R z (l+1)) ha (j+1) 2 p (2*j) j hp (by omega)
    _ (hEN j) L (by
      intro l
      simpa only [Nat.cast_ofNat,Nat.cast_add,Nat.cast_one] using hL l)
  norm_num only [Nat.cast_ofNat,Nat.cast_add,Nat.cast_one] at hop
  have hsum : ‖∑' l:ℕ,bCoeff R z (l+1)*PowerSeries.coeff j (L l)‖≤
      C*(((p:ℝ)+M*(j+1)+2)^(2*j))*PowerSeries.coeff j ((PowerSeries.exp ℝ)*e) := by
    convert! hop.2 using 1 <;>ring
  simp only [cuspSeries,PowerSeries.coeff_C_mul,coefficientSum,PowerSeries.coeff_mk,norm_mul]
  calc
    _ ≤ A₀*(C*((p:ℝ)+M*(j+1)+2)^(2*j)*PowerSeries.coeff j ((PowerSeries.exp ℝ)*e)) :=
      mul_le_mul hA hsum (norm_nonneg _) hA₀.le
    _ ≤ A₀*(C*(Real.exp 6*(scalarOrderWeight M j p)^(2*j))*PowerSeries.coeff j ((PowerSeries.exp ℝ)*e)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (scalar_weight_succ_offset_pow M hM1 j p hp) hC.le) (hEN j)) hA₀.le
    _ = _ := by ring

end WP.HigherOrder.ComplexCanonical
