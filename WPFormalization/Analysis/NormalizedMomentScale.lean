import WPFormalization.Analysis.KernelMomentBounds
import WPFormalization.Marked.DilatonMoments

/-! The actual growing-order moment estimate of Appendix C.5(b), with k <= 2j and the full Sj + l + 1 shift. A common constant works for all orders, states and closed-interval parameters, and every sufficiently large scale M. -/
noncomputable section
namespace WP.Analysis
lemma geometric_normalized_scale_bound (R M α : ℝ) (hR : 0<R) (hM : 0<M) (hα : 0<α)
    (hExp : Real.exp α<R) :
    ∃ C : ℝ,0<C ∧ ∀f:ℕ→ℝ,(∀n,|f n|≤M/R^n)→∀q:ℕ,∀S:ℝ,0<S→(q:ℝ)≤α*S→
      Summable (fun n:ℕ=>(S+n+1)^q*|f n|) ∧
      (∑'n:ℕ,(S+n+1)^q*|f n|)≤C*S^q := by
  let ρ:=Real.exp α/R
  have hρp : 0<ρ:=div_pos (Real.exp_pos _) hR
  have hρ1 : ρ<1:=(div_lt_one hR).2 hExp
  have hden : 0<1-ρ:=by linarith
  have hsρ : HasSum (fun n:ℕ=>ρ^n) (1-ρ)⁻¹:=
    hasSum_geometric_of_abs_lt_one (by rw [abs_of_pos hρp];exact hρ1)
  refine ⟨M*Real.exp α/(1-ρ),by positivity,?_⟩
  intro f hf q S hS hq
  have hp (n:ℕ) : (S+n+1)^q≤S^q*(Real.exp α*(Real.exp α)^n) := by
    have hbase : (S+(n:ℝ)+1)=S*(((n:ℝ)+1)/S+1) := by field_simp;ring
    rw [hbase,mul_pow]
    apply mul_le_mul_of_nonneg_left _ (pow_nonneg hS.le q)
    calc ((((n:ℝ)+1)/S)+1)^q≤(Real.exp (((n:ℝ)+1)/S))^q :=
           pow_le_pow_left₀ (by positivity) (Real.add_one_le_exp _) q
         _=Real.exp ((q:ℝ)*(((n:ℝ)+1)/S)) := (Real.exp_nat_mul _ _).symm
         _≤Real.exp (((n:ℝ)+1)*α) := by
           apply Real.exp_le_exp.mpr
           have hi : (q:ℝ)/S≤α := (div_le_iff₀ hS).2 (by nlinarith)
           have hn:=mul_le_mul_of_nonneg_right hi (show (0:ℝ)≤(n:ℝ)+1 by positivity)
           nlinarith
         _=Real.exp α*(Real.exp α)^n := by
           rw [show ((n:ℝ)+1)*α=(n:ℝ)*α+α by ring,Real.exp_add,Real.exp_nat_mul]
           ring
  let K:=M*S^q*Real.exp α
  have hmajor : Summable (fun n:ℕ=>K*ρ^n):=hsρ.summable.mul_left K
  have hpoint (n:ℕ) : (S+n+1)^q*|f n|≤K*ρ^n := by
    apply (mul_le_mul (hp n) (hf n) (abs_nonneg _) (by positivity)).trans_eq
    dsimp [K,ρ]
    rw [div_pow]
    ring
  have hs : Summable (fun n:ℕ=>(S+n+1)^q*|f n|):=
    Summable.of_nonneg_of_le (fun n=>by positivity) hpoint hmajor
  refine ⟨hs,?_⟩
  calc _≤∑'n:ℕ,K*ρ^n:=hs.tsum_le_tsum hpoint hmajor
       _=K*(1-ρ)⁻¹:=(hsρ.mul_left K).tsum_eq
       _=M*Real.exp α/(1-ρ)*S^q:=by dsimp [K];ring

lemma geometric_growing_order_scale_bound (R B : ℝ) (hR : 1<R) (hB : 0<B) :
    ∃ C M₀ : ℝ,0<C ∧ 0<M₀ ∧ ∀M:ℝ,M₀≤M→∀f:ℕ→ℝ,(∀n,|f n|≤B/R^n)→
      ∀j D p k:ℕ,1≤p→k≤2*j→Summable (fun l:ℕ=>((D:ℝ)+p+M*j+l+1)^k*|f l|) ∧
      (∑'l:ℕ,((D:ℝ)+p+M*j+l+1)^k*|f l|)≤C*((D:ℝ)+p+M*j)^k := by
  let α:=Real.log R/2
  have hRp : 0<R:=by linarith
  have hα : 0<α:=by dsimp [α];exact div_pos (Real.log_pos hR) (by norm_num)
  have hExp : Real.exp α<R:=by
    calc Real.exp α<Real.exp (Real.log R):=Real.exp_lt_exp.mpr (by dsimp [α];linarith [Real.log_pos hR])
         _=R:=Real.exp_log hRp
  obtain ⟨C,hC,hdata⟩:=geometric_normalized_scale_bound R B α hRp hB hα hExp
  refine ⟨C,2/α,hC,by positivity,?_⟩
  intro M hM f hf j D p k hp hk
  have hMpos : 0<M:=lt_of_lt_of_le (by positivity) hM
  have hS : 0<(D:ℝ)+p+M*j:=by
    have hpR : (1:ℝ)≤p:=by exact_mod_cast hp
    have hMj : 0≤M*(j:ℝ):=by positivity
    linarith [show (0:ℝ)≤D from Nat.cast_nonneg D]
  apply hdata f hf k _ hS
  have hMα : 2≤α*M := by
    have hi:=(div_le_iff₀ hα).mp hM
    nlinarith
  have hj:=mul_le_mul_of_nonneg_right hMα (Nat.cast_nonneg j : (0:ℝ)≤j)
  have hkR : (k:ℝ)≤2*j := by exact_mod_cast hk
  nlinarith [mul_nonneg hα.le (show (0:ℝ)≤(D:ℝ)+p by positivity)]

lemma weight_growing_order_scale_bound_of_large_scale : ∃ C M₀ : ℝ,0<C ∧ 0<M₀ ∧
    ∀M:ℝ,M₀≤M→∀j D p k:ℕ,1≤p→k≤2*j→∀Y∈Set.Icc (0:ℝ) y₀,
      Summable (fun l:ℕ=>((D:ℝ)+p+M*j+l+1)^k*|weight Y l|) ∧
      (∑'l:ℕ,((D:ℝ)+p+M*j+l+1)^k*|weight Y l|)≤C*((D:ℝ)+p+M*j)^k := by
  obtain ⟨R,B,hR,hB,hbound⟩:=weight_norm_geometric_bound
  obtain ⟨C,M,hC,hM,hdata⟩:=geometric_growing_order_scale_bound R B hR hB
  exact ⟨C,M,hC,hM,fun M' hM' j D p k hp hk Y hY=>hdata M' hM' (weight Y) (hbound Y hY) j D p k hp hk⟩

lemma dilaton_growing_order_scale_bound_of_large_scale : ∃ C M₀ : ℝ,0<C ∧ 0<M₀ ∧
    ∀M:ℝ,M₀≤M→∀j D p k:ℕ,1≤p→k≤2*j→∀Y∈Set.Icc (0:ℝ) y₀,
      Summable (fun l:ℕ=>((D:ℝ)+p+M*j+l+1)^k*|canonicalDilatonCoefficient Y l|) ∧
      (∑'l:ℕ,((D:ℝ)+p+M*j+l+1)^k*|canonicalDilatonCoefficient Y l|)≤C*((D:ℝ)+p+M*j)^k := by
  obtain ⟨B,hB,hbound⟩:=barH_radius_two_coefficient_bound
  obtain ⟨C,M,hC,hM,hdata⟩:=geometric_growing_order_scale_bound 2 (2*B/3) (by norm_num) (by positivity)
  refine ⟨C,M,hC,hM,?_⟩
  intro M' hM' j D p k hp hk Y hY
  apply hdata M' hM' (canonicalDilatonCoefficient Y) _ j D p k hp hk
  intro d
  cases d with
  | zero => simp [canonicalDilatonCoefficient];positivity
  | succ d =>
    simp only [canonicalDilatonCoefficient,show 1≤d+1 by omega,ite_true,Nat.add_sub_cancel,
      abs_div,abs_of_pos (by norm_num:(0:ℝ)<3)]
    apply (div_le_div_of_nonneg_right (hbound Y hY d) (by norm_num:(0:ℝ)≤3)).trans_eq
    rw [pow_succ]
    ring
lemma canonical_growing_order_scale_bounds : ∃ C M₀ : ℝ,0<C ∧ 0<M₀ ∧
    ∀M:ℝ,M₀≤M→∀j D p k:ℕ,1≤p→k≤2*j→∀Y∈Set.Icc (0:ℝ) y₀,
      Summable (fun l:ℕ=>((D:ℝ)+p+M*j+l+1)^k*|weight Y l|) ∧
      Summable (fun l:ℕ=>((D:ℝ)+p+M*j+l+1)^k*|canonicalDilatonCoefficient Y l|) ∧
      (∑'l:ℕ,((D:ℝ)+p+M*j+l+1)^k*|weight Y l|)≤C*((D:ℝ)+p+M*j)^k ∧
      (∑'l:ℕ,((D:ℝ)+p+M*j+l+1)^k*|canonicalDilatonCoefficient Y l|)≤C*((D:ℝ)+p+M*j)^k := by
  obtain ⟨Cw,Mw,hCw,hMw,hw⟩:=weight_growing_order_scale_bound_of_large_scale
  obtain ⟨Cb,Mb,hCb,hMb,hb⟩:=dilaton_growing_order_scale_bound_of_large_scale
  refine ⟨Cw+Cb,max Mw Mb,by positivity,lt_of_lt_of_le hMw (le_max_left _ _),?_⟩
  intro M hM j D p k hp hk Y hY
  have hwm:=hw M ((le_max_left _ _).trans hM) j D p k hp hk Y hY
  have hbm:=hb M ((le_max_right _ _).trans hM) j D p k hp hk Y hY
  have hMp : 0<M:=lt_of_lt_of_le hMw ((le_max_left _ _).trans hM)
  have hpow : 0≤((D:ℝ)+p+M*j)^k:=by positivity
  exact ⟨hwm.1,hbm.1,hwm.2.trans (mul_le_mul_of_nonneg_right (by linarith) hpow),
    hbm.2.trans (mul_le_mul_of_nonneg_right (by linarith) hpow)⟩
end WP.Analysis
