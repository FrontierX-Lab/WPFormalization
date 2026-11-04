import Mathlib
/-! Fully proved record and exponential-rate arguments for the comparison
upper bound. The actual recursion remains a separate client obligation. -/
noncomputable section
namespace WP.Analysis
open Set
lemma sequence_bounded_of_record_bounds (f:ℕ→ℝ)(N:ℕ)(K:ℝ)
    (hrecord:∀n:ℕ,N ≤ n→(∀j:ℕ,j<n→f j ≤ f n)→f n ≤ K):
    ∃B:ℝ,0<B ∧∀n:ℕ,f n ≤ B:=by
  let B:=max K 0+1+∑j∈Finset.range N,|f j|
  have hsum:0 ≤ ∑j∈Finset.range N,|f j|:=Finset.sum_nonneg (fun _ _=>abs_nonneg _)
  have hB:0<B:=by dsimp[B];nlinarith[le_max_right K 0]
  refine ⟨B,hB,?_⟩
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn:n<N
    · have hsingle:|f n| ≤ ∑j∈Finset.range N,|f j|:=
        Finset.single_le_sum (f:=fun j=>|f j|) (fun _ _=>abs_nonneg _) (Finset.mem_range.mpr hn)
      dsimp[B]
      linarith[le_abs_self (f n),le_max_right K 0]
    · by_cases hr:∀j:ℕ,j<n→f j ≤ f n
      · have hk:=hrecord n (by omega) hr
        dsimp[B]
        linarith[le_max_left K 0]
      · push_neg at hr
        obtain ⟨j,hj,hlt⟩:=hr
        exact hlt.le.trans (ih j hj)

def exponentialRates (f:ℕ→ℝ):Set ℝ:={a |0 ≤ a ∧∃C:ℝ,0<C ∧∀n:ℕ,f n ≤ C*Real.exp (a*n)}

lemma subexponential_of_rate_reduction (f:ℕ→ℝ)(η:ℝ)(hη:0<η)
    (hglobal:(exponentialRates f).Nonempty)
    (hreduce:∀a b:ℝ,0<b→b<a→a-b<η→a∈exponentialRates f→b∈exponentialRates f):
    ∀ε:ℝ,0<ε→∃C:ℝ,0<C ∧∀n:ℕ,f n ≤ C*Real.exp (ε*n):=by
  let γ:=sInf (exponentialRates f)
  have hbdd:BddBelow (exponentialRates f):=⟨0,fun _ ha=>ha.1⟩
  have hγ:0 ≤ γ:=le_csInf hglobal (fun a ha=>ha.1)
  have hγzero:γ=0:=by
    by_contra hz
    have hγpos:0<γ:=lt_of_le_of_ne hγ (Ne.symm hz)
    let δ:=min (γ/4) (η/4)
    have hδ:0<δ:=lt_min (by positivity) (by positivity)
    have hδγ:δ ≤ γ/4:=min_le_left _ _
    have hδη:δ ≤ η/4:=min_le_right _ _
    obtain ⟨a,ha,haNear⟩:=exists_lt_of_csInf_lt hglobal (show γ<γ+δ by linarith)
    have hγa:γ ≤ a:=csInf_le hbdd ha
    have hb:γ-δ∈exponentialRates f:=hreduce a (γ-δ) (by linarith) (by linarith) (by linarith) ha
    have hle:γ ≤ γ-δ:=csInf_le hbdd hb
    linarith
  intro ε hε
  obtain ⟨a,ha,haε⟩:=exists_lt_of_csInf_lt hglobal (show sInf (exponentialRates f)<ε by change γ<ε;rw[hγzero];exact hε)
  obtain ⟨C,hC,hbound⟩:=ha.2
  refine ⟨C,hC,?_⟩
  intro n
  exact (hbound n).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
    (mul_le_mul_of_nonneg_right haε.le (Nat.cast_nonneg _))) hC.le)
end WP.Analysis
namespace WP.Analysis
open Filter Set
open scoped Topology
lemma bounded_of_record_excess (f e:ℕ→ℝ)(K r t:ℝ)(N₀:ℕ)(hr:r<t)
    (he:Tendsto e atTop (𝓝 0))
    (hrec:∀n:ℕ,N₀ ≤ n→(∀j:ℕ,j<n→f j ≤ f n)→f n ≤ K ∨ t ≤ r+e n):
    ∃B:ℝ,0<B ∧∀n:ℕ,f n ≤ B:=by
  have hev:∀ᶠn:ℕ in atTop,e n<t-r:=he.eventually (gt_mem_nhds (by linarith:0<t-r))
  obtain ⟨N,hN⟩:=eventually_atTop.mp hev
  apply sequence_bounded_of_record_bounds f (max N N₀) K
  intro n hn hrecn
  have hnN:N ≤ n:=(le_max_left _ _).trans hn
  have hn₀:N₀ ≤ n:=(le_max_right _ _).trans hn
  rcases hrec n hn₀ hrecn with hk|hbad
  · exact hk
  · exfalso
    linarith [hN n hnN]

lemma exponential_barrier_of_record_excess (f q e:ℕ→ℝ)(K r t:ℝ)(N₀:ℕ)(hr:r<t)
    (he:Tendsto e atTop (𝓝 0))
    (hrec:∀n:ℕ,N₀ ≤ n→(∀j:ℕ,j<n→f j*Real.exp (-q j) ≤ f n*Real.exp (-q n))→
      f n*Real.exp (-q n) ≤ K ∨ t ≤ r+e n):
    ∃B:ℝ,0<B ∧∀n:ℕ,f n ≤ B*Real.exp (q n):=by
  obtain ⟨B,hB,hbound⟩:=bounded_of_record_excess (fun n=>f n*Real.exp (-q n)) e K r t N₀ hr he hrec
  refine ⟨B,hB,?_⟩
  intro n
  have hmul:=mul_le_mul_of_nonneg_right (hbound n) (Real.exp_pos (q n)).le
  simpa only [mul_assoc,←Real.exp_add,neg_add_cancel,Real.exp_zero,mul_one] using hmul
end WP.Analysis
namespace WP.Analysis
lemma value_le_record_exponential (f:ℕ→ℝ)(q:ℕ→ℝ)(n:ℕ)
    (hrec:∀j:ℕ,j<n→f j*Real.exp (-q j) ≤ f n*Real.exp (-q n))
    (j:ℕ)(hj:j<n):f j ≤ f n*Real.exp (q j-q n):=by
  have hmul:=mul_le_mul_of_nonneg_right (hrec j hj) (Real.exp_pos (q j)).le
  have he:Real.exp (-q j)*Real.exp (q j)=1:=by rw[←Real.exp_add,neg_add_cancel,Real.exp_zero]
  rw [mul_assoc,he,mul_one,mul_assoc,←Real.exp_add] at hmul
  convert hmul using 1
  congr 2
  ring

lemma record_split_exponential_bound (f:ℕ→ℝ)(hpos:∀n,0 ≤ f n)
    (a b η C:ℝ)(hb:0<b)(hab:a-b ≤ η)(hC:0 ≤ C)
    (hglobal:∀j:ℕ,f j ≤ C*Real.exp (a*j))
    (n:ℕ)(hrec:∀j:ℕ,j<n→f j*Real.exp (-b*j) ≤ f n*Real.exp (-b*n))
    (j k:ℕ)(hrank:j+k+1=n):f j*f k ≤ f n*C*Real.exp (η*j):=by
  have hk:k<n:=by omega
  have hr:=value_le_record_exponential f (fun i=>b*i) n (by
    intro i hi
    simpa only[neg_mul] using hrec i hi) k hk
  have hprod:=mul_le_mul (hglobal j) hr (hpos k) (mul_nonneg hC (Real.exp_pos _).le)
  have hrankR:(j:ℝ)+k+1=n:=by exact_mod_cast hrank
  have harg:a*(j:ℝ)+(b*k-b*n) ≤ η*j:=by
    have hz:=mul_nonneg (sub_nonneg.mpr hab) (show 0 ≤ (j:ℝ) from Nat.cast_nonneg _)
    nlinarith
  calc
    _ ≤ (C*Real.exp (a*j))*(f n*Real.exp (b*k-b*n)):=hprod
    _ = f n*C*Real.exp (a*j+(b*k-b*n)):=by rw[Real.exp_add];ring
    _ ≤ _:=mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr harg) (mul_nonneg (hpos n) hC)

lemma record_split_monotone_bound (f:ℕ→ℝ)(hpos:∀n,0 ≤ f n)
    (q:ℕ→ℝ)(hq:Monotone q)(a η C:ℝ)(ha:a ≤ η)(hC:0 ≤ C)
    (hglobal:∀j:ℕ,f j ≤ C*Real.exp (a*j))
    (n:ℕ)(hrec:∀j:ℕ,j<n→f j*Real.exp (-q j) ≤ f n*Real.exp (-q n))
    (j k:ℕ)(hrank:j+k+1=n):f j*f k ≤ f n*C*Real.exp (η*j):=by
  have hk:k<n:=by omega
  have hr:=value_le_record_exponential f q n hrec k hk
  have hkn:f k ≤ f n:=hr.trans (by
    have he:Real.exp (q k-q n) ≤ 1:=Real.exp_le_one_iff.mpr (sub_nonpos.mpr (hq hk.le))
    nlinarith[hpos n])
  calc
    _ ≤ (C*Real.exp (a*j))*f n:=mul_le_mul (hglobal j) hkn (hpos k) (mul_nonneg hC (Real.exp_pos _).le)
    _ = f n*C*Real.exp (a*j):=by ring
    _ ≤ _:=mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right ha (Nat.cast_nonneg _)))
      (mul_nonneg (hpos n) hC)
end WP.Analysis
namespace WP.Analysis
lemma exp_neg_le_one_sub_half (x:ℝ)(hx:0 ≤ x)(hx1:x ≤ 1):
    Real.exp (-x) ≤ 1-x/2:=by
  have hden:0<1+x:=by linarith
  have he:Real.exp (-x) ≤ (1+x)⁻¹:=by
    rw [Real.exp_neg]
    exact inv_anti₀ hden (by linarith [Real.add_one_le_exp x])
  have hf:(1+x)⁻¹ ≤ 1-x/2:=by
    rw [←one_div,div_le_iff₀ hden]
    nlinarith [mul_nonneg hx (sub_nonneg.mpr hx1)]
  exact he.trans hf

lemma sqrt_record_factor_lt_one (L B A:ℝ)(hL:0 ≤ L)(hB:0 ≤ B)
    (hA:4*(L+B)<A)(n:ℕ)(hn:1 ≤ n)(hAn:A ≤ 2*Real.sqrt (n:ℝ)):
    (1+L/Real.sqrt (n:ℝ))*Real.exp (A*(Real.sqrt (n-1:ℕ)-Real.sqrt (n:ℝ)))+
      B/Real.sqrt (n:ℝ)<1:=by
  let r:=Real.sqrt (n:ℝ)
  let s:=Real.sqrt (n-1:ℕ)
  have hr:0<r:=Real.sqrt_pos.mpr (by exact_mod_cast (show 0<n by omega))
  have hs:0 ≤ s:=Real.sqrt_nonneg _
  have hsr:s ≤ r:=Real.sqrt_le_sqrt (by exact_mod_cast (show n-1 ≤ n by omega))
  have hr2:r^2=n:=Real.sq_sqrt (Nat.cast_nonneg _)
  have hs2:s^2=(n:ℝ)-1:=by
    have he:((n-1:ℕ):ℝ)=(n:ℝ)-1:=by rw [Nat.cast_sub hn,Nat.cast_one]
    dsimp[s]
    rw [Real.sq_sqrt (Nat.cast_nonneg _),he]
  have hgap:1/(2*r) ≤ r-s:=by
    apply (div_le_iff₀ (by positivity:0<2*r)).2
    nlinarith [mul_nonneg (sub_nonneg.mpr hsr) (sub_nonneg.mpr hsr)]
  have hAp:0<A:=by linarith
  have hx:A/(2*r) ≤ 1:=(div_le_one (by positivity:0<2*r)).2 hAn
  have hExp:Real.exp (A*(s-r)) ≤ 1-A/(4*r):=by
    calc
      _ ≤ Real.exp (-(A/(2*r))):=Real.exp_le_exp.mpr (by
        have hm:=mul_le_mul_of_nonneg_left hgap hAp.le
        have hm':A/(2*r) ≤ A*(r-s):=by simpa only[div_eq_mul_inv,one_mul] using hm
        nlinarith only[hm'])
      _ ≤ 1-(A/(2*r))/2:=exp_neg_le_one_sub_half _ (by positivity) hx
      _ = _:=by ring
  have hscale:L/r+B/r < A/(4*r):=by
    rw [←add_div]
    apply (div_lt_div_iff₀ hr (by positivity:0<4*r)).2
    nlinarith
  have hprod:0 ≤ (L/r)*(A/(4*r)):=mul_nonneg (div_nonneg hL hr.le) (by positivity)
  calc
    _ ≤ (1+L/r)*(1-A/(4*r))+B/r:=
      add_le_add (mul_le_mul_of_nonneg_left hExp (by positivity:0 ≤ 1+L/r)) le_rfl
    _ < 1:=by nlinarith
end WP.Analysis
namespace WP.Analysis
open Filter Set
open scoped Topology
lemma exponential_bound_of_record_recursion (f:ℕ→ℝ)(b L B K:ℝ)(hb:0<b)
    (hrec:∀n:ℕ,2 ≤ n→(∀j:ℕ,j<n→f j*Real.exp (-b*j) ≤ f n*Real.exp (-b*n))→
      f n*Real.exp (-b*n) ≤ K ∨
        1 ≤ (1+L/Real.sqrt (n:ℝ))*Real.exp (-b)+B/Real.sqrt (n:ℝ)):
    ∃C:ℝ,0<C ∧∀n:ℕ,f n ≤ C*Real.exp (b*n):=by
  have hroot:Tendsto (fun n:ℕ=>Real.sqrt (n:ℝ)) atTop atTop:=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hinv:Tendsto (fun n:ℕ=>(Real.sqrt (n:ℝ))⁻¹) atTop (𝓝 0):=
    tendsto_inv_atTop_zero.comp hroot
  have he:Tendsto (fun n:ℕ=>(L*Real.exp (-b)+B)/Real.sqrt (n:ℝ)) atTop (𝓝 0):=by
    simpa only[div_eq_mul_inv,mul_zero] using tendsto_const_nhds.mul hinv
  apply exponential_barrier_of_record_excess f (fun n=>b*n)
    (fun n=>(L*Real.exp (-b)+B)/Real.sqrt (n:ℝ)) K (Real.exp (-b)) 1 2
    (Real.exp_lt_one_iff.mpr (by linarith)) he
  intro n hn hr
  have hr':∀j:ℕ,j<n→f j*Real.exp (-b*j) ≤ f n*Real.exp (-b*n):=by
    simpa only[neg_mul] using hr
  rcases hrec n hn hr' with hk|hbad
  · left;simpa only[neg_mul] using hk
  · right
    convert hbad using 1 <;> ring

lemma sqrt_bound_of_record_recursion (f:ℕ→ℝ)(L B K:ℝ)(hL:0 ≤ L)(hB:0 ≤ B)
    (hrec:∀A:ℝ,0<A→∀n:ℕ,2 ≤ n→
      (∀j:ℕ,j<n→f j*Real.exp (-A*Real.sqrt (j:ℝ)) ≤ f n*Real.exp (-A*Real.sqrt (n:ℝ)))→
      f n*Real.exp (-A*Real.sqrt (n:ℝ)) ≤ K ∨
        1 ≤ (1+L/Real.sqrt (n:ℝ))*Real.exp (A*(Real.sqrt (n-1:ℕ)-Real.sqrt (n:ℝ)))+
          B/Real.sqrt (n:ℝ)):
    ∃C:ℝ,0<C ∧∀n:ℕ,f n ≤ C*Real.exp (C*Real.sqrt (n:ℝ)):=by
  let A:=4*(L+B+1)
  have hA:0<A:=by dsimp[A];linarith
  have hAstr:4*(L+B)<A:=by dsimp[A];linarith
  obtain ⟨N,hN⟩:=exists_nat_gt (A^2)
  have hbarrier:∃D:ℝ,0<D ∧∀n:ℕ,f n*Real.exp (-A*Real.sqrt (n:ℝ)) ≤ D:=by
    apply sequence_bounded_of_record_bounds _ (max N 2) K
    intro n hn hr
    have hn2:2 ≤ n:=(le_max_right _ _).trans hn
    have hNn:N ≤ n:=(le_max_left _ _).trans hn
    have hnsq:A^2 < (n:ℝ):=hN.trans_le (by exact_mod_cast hNn)
    have hAn:A ≤ 2*Real.sqrt (n:ℝ):=by
      nlinarith[Real.sq_sqrt (Nat.cast_nonneg n:0 ≤ (n:ℝ)),Real.sqrt_nonneg (n:ℝ)]
    rcases hrec A hA n hn2 hr with hk|hbad
    · exact hk
    · exfalso
      exact (not_le_of_gt (sqrt_record_factor_lt_one L B A hL hB hAstr n (by omega) hAn)) hbad
  obtain ⟨D,hD,hbound⟩:=hbarrier
  let C:=max D A
  have hC:0<C:=lt_of_lt_of_le hD (le_max_left _ _)
  refine ⟨C,hC,?_⟩
  intro n
  have hnorm:f n ≤ D*Real.exp (A*Real.sqrt (n:ℝ)):=by
    have hm:=mul_le_mul_of_nonneg_right (hbound n) (Real.exp_pos (A*Real.sqrt (n:ℝ))).le
    simpa only[mul_assoc,←Real.exp_add,neg_mul,neg_add_cancel,Real.exp_zero,mul_one] using hm
  exact hnorm.trans (mul_le_mul (le_max_left _ _)
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.sqrt_nonneg _)))
    (Real.exp_pos _).le hC.le)
end WP.Analysis
