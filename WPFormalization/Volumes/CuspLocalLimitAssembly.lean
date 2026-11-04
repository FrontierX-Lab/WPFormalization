import WPFormalization.Statements.QuantitativeCuspLocal
import WPFormalization.Marked.LogGrowth
/-! Exact sequential local-limit assembly from the original quantitative
local limit proposition. The quantitative proposition now has its own genuine proof; both public
statements retain their original types and classical trust boundary. -/
noncomputable section
namespace WP
open Filter Set
open scoped Topology
set_option autoImplicit false
lemma cusp_local_limit_of_quantitative_proof (P : PsiTheory) (p : ℕ) (hp : 1 ≤ p)
    (gs : ℕ → ℕ) (xs : ℕ → ℝ) (ks : ℕ → ℕ) (u : ℝ)
    (hg : Tendsto gs atTop atTop) (hx : ∀ j, xs j ∈ Set.Ioo 0 xCritical)
    (hmu : Tendsto (fun j => complexity (gs j) p*Psi (xs j)) atTop atTop)
    (hu : Tendsto (fun j => ((ks j : ℝ)-complexity (gs j) p*Psi (xs j)) /
      Real.sqrt (complexity (gs j) p*euler Psi (xs j))) atTop (𝓝 u)) :
    Tendsto (fun j => Real.sqrt (complexity (gs j) p*euler Psi (xs j))*
      cuspMass P (gs j) p (ks j) (xs j)) atTop
      (𝓝 (Real.exp (-u^2/2)/Real.sqrt (2*Real.pi))) := by
  obtain ⟨C,κ,M₀,hC,hκ,hM₀,hbound⟩:=quantitative_cusp_local P p hp
  let m:ℕ→ℝ:=fun j=>min (complexity (gs j) p:ℝ) ((complexity (gs j) p:ℝ)*Psi (xs j))
  let q:ℕ→ℝ:=fun j=>((ks j:ℝ)-(complexity (gs j) p:ℝ)*Psi (xs j))/
    Real.sqrt ((complexity (gs j) p:ℝ)*euler Psi (xs j))
  let a:ℕ→ℝ:=fun j=>Real.sqrt ((complexity (gs j) p:ℝ)*euler Psi (xs j))*
    cuspMass P (gs j) p (ks j) (xs j)
  let G:ℝ→ℝ:=fun z=>Real.exp (-z^2/2)/Real.sqrt (2*Real.pi)
  have hhm:Tendsto (fun j=>(complexity (gs j) p:ℝ)) atTop atTop:=
    (Analysis.complexity_real_tendsto_atTop p).comp hg
  have hm:Tendsto m atTop atTop:=tendsto_inf_atTop atTop hhm hmu
  have herrlim:Tendsto (fun j=>C*(m j)^(-κ)) atTop (𝓝 0):=by
    simpa only[Function.comp_def,mul_zero] using ((tendsto_rpow_neg_atTop hκ).comp hm).const_mul C
  have herr:∀ᶠj:ℕ in atTop,|a j-G (q j)|≤C*(m j)^(-κ):=by
    filter_upwards[hm.eventually_ge_atTop M₀] with j hj
    have ht:=hbound (gs j) (xs j) (hx j) hj (ks j:ℤ)
    have hG:Real.exp (-((ks j:ℝ)-(complexity (gs j) p:ℝ)*Psi (xs j))^2/
      (2*(Real.sqrt ((complexity (gs j) p:ℝ)*euler Psi (xs j)))^2))/Real.sqrt (2*Real.pi)=G (q j):=by
      dsimp[G,q]
      congr 2
      ring
    simpa only[Int.natCast_nonneg,if_pos,Int.toNat_natCast,Int.cast_natCast,Real.rpow_eq_pow,hG] using ht
  have hzero:Tendsto (fun j=>a j-G (q j)) atTop (𝓝 0):=by
    apply squeeze_zero_norm' _ herrlim
    simpa only[Real.norm_eq_abs] using herr
  have hGcont:Continuous G:=by dsimp[G];fun_prop
  have hGl:Tendsto (fun j=>G (q j)) atTop (𝓝 (G u)):=hGcont.continuousAt.tendsto.comp hu
  have hsum:=hzero.add hGl
  simpa only[sub_add_cancel,zero_add] using hsum
end WP
