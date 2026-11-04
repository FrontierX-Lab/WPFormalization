import WPFormalization.HigherOrder.ComplexTriangular
import WPFormalization.HigherOrder.MergerMajorant
import WPFormalization.HigherOrder.ComplexShiftBounds
/-! The actual loss-r finite ratio core: normalized bounds for its cusp shifts, inverse-linear factors and genus factors, and its product with a child series. These are finite norm estimates under explicit lower-order data. The wider analytic factor exp(2t)^r is retained. -/
set_option maxHeartbeats 800000
noncomputable section
namespace WP.HigherOrder.ComplexCanonical
open PowerSeries

def ratioCoreSeries (F:HierarchyJet) (p j s:ℕ) : Series :=
  let r:=2*j+s
  (∏a∈Finset.range r,complexityShift (r-a) (F.cusp (p-s+a))*
    (1-C ((r-a:ℕ):ℂ)*PowerSeries.X)⁻¹)*
    ∏b∈Finset.range j,F.genus (p+2*b)

lemma ratioCoreSeries_norm_coeff_bound (F:HierarchyJet) (p j s n K:ℕ) (S:ℝ)
    (hr:1 ≤ 2*j+s) (hn:n+(2*j+s) ≤ K) (hS:(K:ℝ) ≤ S)
    (g a:WP.HigherOrder.Series)
    (hg:∀k,0 ≤ PowerSeries.coeff k g) (ha:∀k,0 ≤ PowerSeries.coeff k a)
    (hcusp:∀b∈Finset.range (2*j+s),∀i:ℕ,i ≤ n→
      ‖PowerSeries.coeff i (F.cusp (p-s+b))‖ ≤ S^(2*i)*PowerSeries.coeff i g)
    (hgenus:∀b∈Finset.range j,∀i:ℕ,i ≤ n→
      ‖PowerSeries.coeff i (F.genus (p+2*b))‖ ≤ S^(2*i)*PowerSeries.coeff i a) :
    ‖PowerSeries.coeff n (ratioCoreSeries F p j s)‖ ≤
      S^(2*n)*PowerSeries.coeff n ((((PowerSeries.exp ℝ)^2)*g)^(2*j+s)*a^j) := by
  let r:=2*j+s
  have hS0:0 ≤ S:=(Nat.cast_nonneg K).trans hS
  have hG:=coeff_mul_nonneg exp_coeff_nonneg hg
  let U:WP.HigherOrder.Series:=((PowerSeries.exp ℝ)^2)*g
  have hU:∀k,0 ≤ PowerSeries.coeff k U:=by
    dsimp[U]
    exact coeff_mul_nonneg (by simpa only[pow_two] using coeff_mul_nonneg exp_coeff_nonneg exp_coeff_nonneg) hg
  have hfactor (b:ℕ) (hb:b∈Finset.range r) (q:ℕ) (hq:q ≤ n) :
      ‖PowerSeries.coeff q (complexityShift (r-b) (F.cusp (p-s+b))*
        (1-C ((r-b:ℕ):ℂ)*PowerSeries.X)⁻¹)‖ ≤ S^(2*q)*PowerSeries.coeff q U := by
    have hrK:r ≤ K:=by dsimp only[r];omega
    have hbK:r-b ≤ K:=(Nat.sub_le _ _).trans hrK
    have hcast:((r:ℂ)-(b:ℂ))=((r-b:ℕ):ℂ):=(Nat.cast_sub (Finset.mem_range.mp hb).le).symm
    have hnorm:‖((r-b:ℕ):ℂ)‖ ≤ (K:ℝ):=by
      rw[Complex.norm_natCast]
      exact_mod_cast hbK
    have hshift:∀i:ℕ,i ≤ q→‖PowerSeries.coeff i (complexityShift (r-b) (F.cusp (p-s+b)))‖ ≤
        S^(2*i)*PowerSeries.coeff i ((PowerSeries.exp ℝ)*g):=by
      rw[hcast]
      intro i hi
      have hsh:=complex_shift_coeff_exponential_majorant ((r-b:ℕ):ℂ) S
        (F.cusp (p-s+b)) (fun k=>PowerSeries.coeff k g) i K (by omega) hnorm hS hg (by
          intro k hk
          simpa only[mul_comm] using hcusp b hb k (hk.trans (hi.trans hq)))
      have hmk:PowerSeries.mk (fun k=>PowerSeries.coeff k g)=g:=by ext k;simp
      rw[hmk] at hsh
      simpa only[complexityShift,shiftVariable] using hsh
    have hinv:∀i:ℕ,i ≤ q→‖PowerSeries.coeff i ((1-C ((r-b:ℕ):ℂ)*PowerSeries.X:Series)⁻¹)‖ ≤
        S^(2*i)*PowerSeries.coeff i (PowerSeries.exp ℝ):=by
      intro i hi
      have hh:=complex_inverse_linear_pow_coeff_normalized ((r-b:ℕ):ℂ) S 1 i K (by omega) hnorm hS
      have heq:PowerSeries.coeff i (PowerSeries.exp ℝ)=1/(i.factorial:ℝ):=by norm_num[PowerSeries.coeff_exp]
      simpa only[pow_one,heq,div_eq_mul_inv,one_mul] using hh
    have hm:=scaled_coeff_mul_bound _ _ ((PowerSeries.exp ℝ)*g) (PowerSeries.exp ℝ) S hS0 q
      hG exp_coeff_nonneg hshift hinv
    have hu:((PowerSeries.exp ℝ)*g)*(PowerSeries.exp ℝ)=U:=by dsimp[U];ring
    simpa only[hu] using hm
  have hprod:∀q:ℕ,q ≤ n→‖PowerSeries.coeff q
      (∏b∈Finset.range r,complexityShift (r-b) (F.cusp (p-s+b))*
        (1-C ((r-b:ℕ):ℂ)*PowerSeries.X)⁻¹)‖ ≤ S^(2*q)*PowerSeries.coeff q (U^r):=by
    intro q hq
    have hp:=scaled_coeff_prod_bound (Finset.range r)
      (fun b=>complexityShift (r-b) (F.cusp (p-s+b))*(1-C ((r-b:ℕ):ℂ)*PowerSeries.X)⁻¹)
      (fun _=>U) S hS0 (fun b hb=>hU) q (fun b hb i hi=>hfactor b hb i (hi.trans hq))
    simpa only[Finset.prod_const,Finset.card_range] using hp
  have hgp:∀q:ℕ,q ≤ n→‖PowerSeries.coeff q (∏b∈Finset.range j,F.genus (p+2*b))‖ ≤
      S^(2*q)*PowerSeries.coeff q (a^j):=by
    intro q hq
    have hp:=scaled_coeff_prod_bound (Finset.range j) (fun b=>F.genus (p+2*b)) (fun _=>a)
      S hS0 (fun b hb=>ha) q (fun b hb i hi=>hgenus b hb i (hi.trans hq))
    simpa only[Finset.prod_const,Finset.card_range] using hp
  have hUN:∀k,0 ≤ PowerSeries.coeff k (U^r):=by
    simpa only[Finset.prod_const,Finset.card_range] using
      coeff_prod_nonneg (Finset.range r) (fun _=>U) (fun b hb=>hU)
  have hAN:∀k,0 ≤ PowerSeries.coeff k (a^j):=by
    simpa only[Finset.prod_const,Finset.card_range] using
      coeff_prod_nonneg (Finset.range j) (fun _=>a) (fun b hb=>ha)
  exact scaled_coeff_mul_bound _ _ (U^r) (a^j) S hS0 n hUN hAN hprod hgp

lemma ratioSeries_norm_coeff_bound (R:ℂ→ℂ) (z:ℂ) (F:HierarchyJet) (p j s n K:ℕ) (S:ℝ)
    (hr:1 ≤ 2*j+s) (hn:n+(2*j+s) ≤ K) (hS:(K:ℝ) ≤ S)
    (g a:WP.HigherOrder.Series)
    (hg:∀k,0 ≤ PowerSeries.coeff k g) (ha:∀k,0 ≤ PowerSeries.coeff k a)
    (hcusp:∀b∈Finset.range (2*j+s),∀i:ℕ,i ≤ n→
      ‖PowerSeries.coeff i (F.cusp (p-s+b))‖ ≤ S^(2*i)*PowerSeries.coeff i g)
    (hgenus:∀b∈Finset.range j,∀i:ℕ,i ≤ n→
      ‖PowerSeries.coeff i (F.genus (p+2*b))‖ ≤ S^(2*i)*PowerSeries.coeff i a) :
    ‖PowerSeries.coeff (n+(2*j+s)) (ratioSeries R z F p j s)‖ ≤
      ‖kernelA R z‖^(2*j+s)*S^(2*n)*
        PowerSeries.coeff n ((((PowerSeries.exp ℝ)^2)*g)^(2*j+s)*a^j) := by
  have hser:ratioSeries R z F p j s=PowerSeries.C ((kernelA R z)^(2*j+s))*
      (PowerSeries.X^(2*j+s)*ratioCoreSeries F p j s):=by
    dsimp[ratioSeries,ratioCoreSeries]
    rw[mul_pow,←map_pow]
    ring
  rw[hser,PowerSeries.coeff_C_mul,PowerSeries.coeff_X_pow_mul,norm_mul,norm_pow]
  exact (mul_le_mul_of_nonneg_left
    (ratioCoreSeries_norm_coeff_bound F p j s n K S hr hn hS g a hg ha hcusp hgenus)
    (pow_nonneg (norm_nonneg _) _)).trans_eq (by ring)
lemma ratioSeries_scalar_order_norm_bound (R:ℂ→ℂ) (z:ℂ) (F:HierarchyJet)
    (M:ℝ) (hM:1 ≤ M) (p j s n K:ℕ) (hp:1 ≤ p) (hs:s<p)
    (hr:1 ≤ 2*j+s) (hn:n+(2*j+s) ≤ K) (S:ℝ) (hS:scalarOrderWeight M K p ≤ S)
    (g a:WP.HigherOrder.Series)
    (hg:∀k,0 ≤ PowerSeries.coeff k g) (ha:∀k,0 ≤ PowerSeries.coeff k a)
    (hcusp:∀i:ℕ,i ≤ K-1→∀q:ℕ,1 ≤ q→‖PowerSeries.coeff i (F.cusp q)‖ ≤
      (scalarOrderWeight M i q)^(2*i)*PowerSeries.coeff i g)
    (hgenus:∀i:ℕ,i ≤ K-1→∀q:ℕ,1 ≤ q→‖PowerSeries.coeff i (F.genus q)‖ ≤
      (scalarOrderWeight M i q)^(2*i)*PowerSeries.coeff i a) :
    ‖PowerSeries.coeff (n+(2*j+s)) (ratioSeries R z F p j s)‖ ≤
      ‖kernelA R z‖^(2*j+s)*S^(2*n)*
        PowerSeries.coeff n ((((PowerSeries.exp ℝ)^2)*g)^(2*j+s)*a^j) := by
  have hM0:0 ≤ M:=by linarith
  have hKS:(K:ℝ) ≤ S:=by
    have hm:=mul_le_mul_of_nonneg_right hM (Nat.cast_nonneg K : (0:ℝ) ≤ K)
    dsimp only[scalarOrderWeight] at hS
    linarith [Nat.cast_nonneg (α:=ℝ) p]
  apply ratioSeries_norm_coeff_bound R z F p j s n K S hr hn hKS g a hg ha
  · intro b hb i hi
    have hb':b<2*j+s:=Finset.mem_range.mp hb
    have hq:1 ≤ p-s+b:=by omega
    have hscale:scalarOrderWeight M i (p-s+b) ≤ S:=
      (scalar_order_weight_shift M hM i K p (p-s+b) (2*j+s) (by omega) (by omega)).trans hS
    have hscale0:0 ≤ scalarOrderWeight M i (p-s+b):=by unfold scalarOrderWeight;positivity
    exact (hcusp i (by omega) (p-s+b) hq).trans
      (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hscale0 hscale _) (hg i))
  · intro b hb i hi
    have hb':b<j:=Finset.mem_range.mp hb
    have hq:1 ≤ p+2*b:=by omega
    have hscale:scalarOrderWeight M i (p+2*b) ≤ S:=
      (scalar_order_weight_shift M hM i K p (p+2*b) (2*j+s) (by omega) (by omega)).trans hS
    have hscale0:0 ≤ scalarOrderWeight M i (p+2*b):=by unfold scalarOrderWeight;positivity
    exact (hgenus i (by omega) (p+2*b) hq).trans
      (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hscale0 hscale _) (ha i))

lemma ratioSeries_mul_norm_coeff_bound (R:ℂ→ℂ) (z:ℂ) (F:HierarchyJet) (p j s n K:ℕ) (S:ℝ)
    (hr:1 ≤ 2*j+s) (hn:n+(2*j+s) ≤ K) (hS:(K:ℝ) ≤ S)
    (g a E:WP.HigherOrder.Series) (f:Series)
    (hg:∀k,0 ≤ PowerSeries.coeff k g) (ha:∀k,0 ≤ PowerSeries.coeff k a)
    (hE:∀k,0 ≤ PowerSeries.coeff k E)
    (hcusp:∀b∈Finset.range (2*j+s),∀i:ℕ,i ≤ n→
      ‖PowerSeries.coeff i (F.cusp (p-s+b))‖ ≤ S^(2*i)*PowerSeries.coeff i g)
    (hgenus:∀b∈Finset.range j,∀i:ℕ,i ≤ n→
      ‖PowerSeries.coeff i (F.genus (p+2*b))‖ ≤ S^(2*i)*PowerSeries.coeff i a)
    (hf:∀i:ℕ,i ≤ n→‖PowerSeries.coeff i f‖ ≤ S^(2*i)*PowerSeries.coeff i E) :
    ‖PowerSeries.coeff (n+(2*j+s)) (ratioSeries R z F p j s*f)‖ ≤
      ‖kernelA R z‖^(2*j+s)*S^(2*n)*
        PowerSeries.coeff n (((((PowerSeries.exp ℝ)^2)*g)^(2*j+s)*a^j)*E) := by
  have hS0:0 ≤ S:=(Nat.cast_nonneg K).trans hS
  let U:WP.HigherOrder.Series:=(((PowerSeries.exp ℝ)^2)*g)^(2*j+s)*a^j
  have hU:∀k,0 ≤ PowerSeries.coeff k U:=by
    have hExp2:∀k,0 ≤ PowerSeries.coeff k ((PowerSeries.exp ℝ)^2):=by
      simpa only[pow_two] using coeff_mul_nonneg exp_coeff_nonneg exp_coeff_nonneg
    have hUg:∀k,0 ≤ PowerSeries.coeff k (((PowerSeries.exp ℝ)^2*g)^(2*j+s)):=by
      simpa only[Finset.prod_const,Finset.card_range] using
        (coeff_prod_nonneg (Finset.range (2*j+s)) (fun _=>(PowerSeries.exp ℝ)^2*g)
          (fun b hb=>coeff_mul_nonneg hExp2 hg))
    have hAj:∀k,0 ≤ PowerSeries.coeff k (a^j):=by
      simpa only[Finset.prod_const,Finset.card_range] using
        (coeff_prod_nonneg (Finset.range j) (fun _=>a) (fun b hb=>ha))
    exact coeff_mul_nonneg hUg hAj
  have hprod:=scaled_coeff_mul_bound (ratioCoreSeries F p j s) f U E S hS0 n hU hE
    (fun i hi=>ratioCoreSeries_norm_coeff_bound F p j s i K S hr (by omega) hS g a hg ha
      (fun b hb k hk=>hcusp b hb k (hk.trans hi)) (fun b hb k hk=>hgenus b hb k (hk.trans hi))) hf
  have hser:ratioSeries R z F p j s*f=PowerSeries.C ((kernelA R z)^(2*j+s))*
      (PowerSeries.X^(2*j+s)*(ratioCoreSeries F p j s*f)):=by
    dsimp[ratioSeries,ratioCoreSeries]
    rw[mul_pow,←map_pow]
    ring
  rw[hser,PowerSeries.coeff_C_mul,PowerSeries.coeff_X_pow_mul,norm_mul,norm_pow]
  exact (mul_le_mul_of_nonneg_left hprod (pow_nonneg (norm_nonneg _) _)).trans_eq (by ring)
end WP.HigherOrder.ComplexCanonical
