import WPFormalization.Analysis.Taylor
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
/-! Nonnegative real complex Taylor jets are closed under analytic sums,
products, powers, zero-preserving composition and finite positive
multivariate polynomial evaluation. Composition uses Mathlib's actual
Faà di Bruno formula; no coefficient-positivity theorem is assumed. -/
noncomputable section
namespace WP.PositiveConvolution
open Filter
open scoped Topology
abbrev nnComplexHom:NNReal→+*ℂ:=Complex.ofRealHom.comp NNReal.toRealHom
def PositiveJets (f:ℂ→ℂ):Prop:=∀n:ℕ,∃a:NNReal,iteratedDeriv n f 0=nnComplexHom a
lemma PositiveJets.const (a:NNReal):PositiveJets (fun _:ℂ=>nnComplexHom a):=by
  intro n
  by_cases hn:n=0
  · subst n
    exact ⟨a,by simp⟩
  · exact ⟨0,by simp[iteratedDeriv_const,hn]⟩
lemma PositiveJets.add {f g:ℂ→ℂ} (hf:AnalyticAt ℂ f 0) (hg:AnalyticAt ℂ g 0)
    (hF:PositiveJets f) (hG:PositiveJets g):PositiveJets (fun z=>f z+g z):=by
  intro n
  obtain ⟨a,ha⟩:=hF n
  obtain ⟨b,hb⟩:=hG n
  refine ⟨a+b,?_⟩
  rw[iteratedDeriv_fun_add hf.contDiffAt hg.contDiffAt,ha,hb,map_add]
lemma PositiveJets.mul {f g:ℂ→ℂ} (hf:AnalyticAt ℂ f 0) (hg:AnalyticAt ℂ g 0)
    (hF:PositiveJets f) (hG:PositiveJets g):PositiveJets (fun z=>f z*g z):=by
  choose a ha using hF
  choose b hb using hG
  intro n
  refine ⟨∑i∈Finset.range (n+1),(Nat.choose n i:NNReal)*a i*b (n-i),?_⟩
  rw[iteratedDeriv_fun_mul hf.contDiffAt hg.contDiffAt]
  simp only[ha,hb,map_sum,map_mul,map_natCast]
lemma PositiveJets.comp {f g:ℂ→ℂ} (hf:AnalyticAt ℂ f 0) (hg:AnalyticAt ℂ g 0)
    (hg0:g 0=0) (hF:PositiveJets f) (hG:PositiveJets g):PositiveJets (fun z=>f (g z)):=by
  choose a ha using hF
  choose b hb using hG
  intro n
  refine ⟨∑c:OrderedFinpartition n,(∏j,b (c.partSize j))*a c.length,?_⟩
  have hf':ContDiffAt ℂ ⊤ f (g 0):=by simpa only[hg0] using hf.contDiffAt
  have hg':ContDiffAt ℂ ⊤ g 0:=hg.contDiffAt
  change iteratedDeriv n (f∘g) 0=_
  rw[iteratedDeriv_scomp_eq_sum_orderedFinpartition hf' hg' (by simp)]
  simp only[hg0,ha,hb,smul_eq_mul,map_sum,map_mul,map_prod]
lemma PositiveJets.coefficient_nonneg {f:ℂ→ℂ} (hf:PositiveJets f) (n:ℕ):
    0 ≤ realCoeff f n ∧ (WP.coeff f n).im=0:=by
  obtain ⟨a,ha⟩:=hf n
  have hc:WP.coeff f n=Complex.ofReal ((a:ℝ)/(n.factorial:ℝ)):=by
    unfold WP.coeff
    rw[ha]
    change ((a:ℝ):ℂ)/(n.factorial:ℂ)=Complex.ofReal ((a:ℝ)/(n.factorial:ℝ))
    simpa only[Complex.ofReal_natCast] using (Complex.ofReal_div (a:ℝ) (n.factorial:ℝ)).symm
  rw[show realCoeff f n=(WP.coeff f n).re from rfl,hc]
  simp only[Complex.ofReal_re,Complex.ofReal_im]
  exact ⟨div_nonneg a.coe_nonneg (Nat.cast_nonneg _),True.intro⟩
end WP.PositiveConvolution

namespace WP.PositiveConvolution
lemma PositiveJets.of_coefficients {f:ℂ→ℂ} (hn:∀n,0 ≤ realCoeff f n)
    (him:∀n,(WP.coeff f n).im=0):PositiveJets f:=by
  intro n
  let a:NNReal:=⟨realCoeff f n*(n.factorial:ℝ),mul_nonneg (hn n) (Nat.cast_nonneg _)⟩
  refine ⟨a,?_⟩
  have hc:WP.coeff f n=Complex.ofReal (realCoeff f n):=by
    apply Complex.ext
    · rfl
    · simpa only[Complex.ofReal_im] using him n
  have he:iteratedDeriv n f 0=WP.coeff f n*(n.factorial:ℂ):=by
    unfold WP.coeff
    rw[div_mul_cancel₀ _ (show (n.factorial:ℂ)≠0 by exact_mod_cast n.factorial_ne_zero)]
  rw[he,hc]
  change Complex.ofReal (realCoeff f n)*(n.factorial:ℂ)=Complex.ofReal (realCoeff f n*(n.factorial:ℝ))
  simp only[Complex.ofReal_mul,Complex.ofReal_natCast]
lemma PositiveJets.pow {f:ℂ→ℂ} (hf:AnalyticAt ℂ f 0) (hF:PositiveJets f) (n:ℕ):
    PositiveJets (fun z=>f z^n):=by
  induction n with
  | zero=>simpa only[pow_zero,map_one] using PositiveJets.const (1:NNReal)
  | succ n ih=>
    simpa only[pow_succ,Pi.pow_apply] using PositiveJets.mul (hf.pow n) hf ih hF
lemma PositiveJets.sum {ι:Type*} (s:Finset ι) (f:ι→ℂ→ℂ)
    (hf:∀i∈s,AnalyticAt ℂ (f i) 0) (hF:∀i∈s,PositiveJets (f i)):
    PositiveJets (fun z=>∑i∈s,f i z):=by
  classical
  induction s using Finset.induction_on with
  | empty=>simpa only[Finset.sum_empty,map_zero] using PositiveJets.const (0:NNReal)
  | @insert i s hi ih=>
    have htail:∀j∈s,AnalyticAt ℂ (f j) 0:=fun j hj=>hf j (Finset.mem_insert_of_mem hj)
    have hJ:∀j∈s,PositiveJets (f j):=fun j hj=>hF j (Finset.mem_insert_of_mem hj)
    simpa only[Finset.sum_insert hi] using PositiveJets.add
      (hf i (Finset.mem_insert_self _ _)) (Finset.analyticAt_fun_sum _ htail)
      (hF i (Finset.mem_insert_self _ _)) (ih htail hJ)
lemma PositiveJets.prod {ι:Type*} (s:Finset ι) (f:ι→ℂ→ℂ)
    (hf:∀i∈s,AnalyticAt ℂ (f i) 0) (hF:∀i∈s,PositiveJets (f i)):
    PositiveJets (fun z=>∏i∈s,f i z):=by
  classical
  induction s using Finset.induction_on with
  | empty=>simpa only[Finset.prod_empty,map_one] using PositiveJets.const (1:NNReal)
  | @insert i s hi ih=>
    have htail:∀j∈s,AnalyticAt ℂ (f j) 0:=fun j hj=>hf j (Finset.mem_insert_of_mem hj)
    have hJ:∀j∈s,PositiveJets (f j):=fun j hj=>hF j (Finset.mem_insert_of_mem hj)
    simpa only[Finset.prod_insert hi] using PositiveJets.mul
      (hf i (Finset.mem_insert_self _ _)) (Finset.analyticAt_fun_prod _ htail)
      (hF i (Finset.mem_insert_self _ _)) (ih htail hJ)
lemma polynomial_analyticAt (F:MvPolynomial ℕ NNReal) (v:ℕ→ℂ→ℂ)
    (hf:∀l,AnalyticAt ℂ (v l) 0):
    AnalyticAt ℂ (fun z=>MvPolynomial.eval₂ nnComplexHom (fun l=>v l z) F) 0:=by
  classical
  change AnalyticAt ℂ (fun z=>∑d∈F.support,nnComplexHom (F.coeff d)*∏l∈d.support,(v l z)^(d l)) 0
  apply Finset.analyticAt_fun_sum
  intro d hd
  apply AnalyticAt.mul analyticAt_const
  apply Finset.analyticAt_fun_prod
  intro l hl
  exact (hf l).pow _
lemma polynomial_positiveJets (F:MvPolynomial ℕ NNReal) (v:ℕ→ℂ→ℂ)
    (hf:∀l,AnalyticAt ℂ (v l) 0) (hF:∀l,PositiveJets (v l)):
    PositiveJets (fun z=>MvPolynomial.eval₂ nnComplexHom (fun l=>v l z) F):=by
  classical
  change PositiveJets (fun z=>∑d∈F.support,nnComplexHom (F.coeff d)*∏l∈d.support,(v l z)^(d l))
  apply PositiveJets.sum
  · intro d hd
    apply AnalyticAt.mul analyticAt_const
    apply Finset.analyticAt_fun_prod
    intro l hl
    exact (hf l).pow _
  · intro d hd
    apply PositiveJets.mul analyticAt_const
    · apply Finset.analyticAt_fun_prod
      intro l hl
      exact (hf l).pow _
    · exact PositiveJets.const _
    · apply PositiveJets.prod
      · intro l hl
        exact (hf l).pow _
      · intro l hl
        exact PositiveJets.pow (hf l) (hF l) _
end WP.PositiveConvolution
