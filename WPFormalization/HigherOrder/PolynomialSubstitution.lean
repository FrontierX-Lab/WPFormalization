import WPFormalization.HigherOrder.MajorantProof
/-! Exact evaluation of polynomial inputs for the finite substitutionCoeff operation in Lemma C.2. The monomial proof includes all degrees outside the finite box, using actual zero-constant product vanishing. This is an algebraic bridge, not an assumed interpretation of formalFixedPoint. -/
noncomputable section
namespace WP.Majorant
open PowerSeries
variable {R:Type*} [CommSemiring R]

lemma listprod_coeff_zero_of_lt_length {σ:Type*} (l:List σ) (f:σ→PowerSeries R)
    (hf:∀s,PowerSeries.coeff 0 (f s)=0) (n:ℕ) (hn:n < l.length) :
    PowerSeries.coeff n (l.map f).prod=0 := by
  induction l generalizing n with
  | nil=>simp at hn
  | cons s l ih=>
    simp only[List.length_cons] at hn
    simp only[List.map_cons,List.prod_cons]
    rw[PowerSeries.coeff_mul]
    apply Finset.sum_eq_zero
    intro ij hij
    have hs:=Finset.HasAntidiagonal.mem_antidiagonal.mp hij
    by_cases hz:ij.1=0
    · rw[hz,hf s,zero_mul]
    · rw[ih ij.2 (by omega),mul_zero]

lemma multiDegree_eq_sum {m:ℕ} (α:Option (Fin m)→₀ℕ) :
    multiDegree α=∑s:Option (Fin m),α s := by
  unfold multiDegree
  apply Finsupp.sum_fintype
  intro s
  rfl

lemma monomial_argument_coeff_zero {m:ℕ} (α:Option (Fin m)→₀ℕ) (E:Fin m→PowerSeries R)
    (hE:∀i,PowerSeries.coeff 0 (E i)=0) (n:ℕ) (hn:n < multiDegree α) :
    PowerSeries.coeff n (PowerSeries.X^(α none)*∏i,E i^(α (some i)))=0 := by
  rw[←factor_argumentSeries_prod]
  apply listprod_coeff_zero_of_lt_length
  · exact argumentSeries_zero E hE
  · simpa only[factors_length,multiDegree] using hn

lemma substitutionCoeff_monomial {m:ℕ} (α:Option (Fin m)→₀ℕ) (c:R) (E:Fin m→PowerSeries R)
    (hE:∀i,PowerSeries.coeff 0 (E i)=0) (n:ℕ) :
    substitutionCoeff (MvPowerSeries.monomial α c) E n=
      c*PowerSeries.coeff n (PowerSeries.X^(α none)*∏i,E i^(α (some i))) := by
  classical
  by_cases hd:multiDegree α  ≤  n
  · have hc (s:Option (Fin m)) : α s  ≤  n:=by
      have hs:α s  ≤  ∑t:Option (Fin m),α t:=
        Finset.single_le_sum (fun t ht=>Nat.zero_le _) (Finset.mem_univ s)
      rw[←multiDegree_eq_sum] at hs
      exact hs.trans hd
    let β:Option (Fin m)→Fin (n+1):=fun s=>⟨α s,by have hs:=hc s;omega⟩
    have henc:Finsupp.equivFunOnFinite.symm (fun s=>(β s).val)=α:=by ext s;rfl
    have hdegree:(∑s:Option (Fin m),(β s).val)  ≤  n:=by
      simpa only[β,←multiDegree_eq_sum] using hd
    unfold substitutionCoeff
    rw[Finset.sum_eq_single β]
    · rw[if_pos hdegree,henc,MvPowerSeries.coeff_monomial_same]
    · intro γ hγ hne
      by_cases hsum:(∑s:Option (Fin m),(γ s).val)  ≤  n
      · rw[if_pos hsum,MvPowerSeries.coeff_monomial_ne]
        · exact zero_mul _
        · intro heq
          apply hne
          funext s
          apply Fin.ext
          have hh:=congrArg (fun f:Option (Fin m)→₀ℕ=>f s) heq
          exact hh
      · rw[if_neg hsum]
    · simp
  · have hz:=monomial_argument_coeff_zero α E hE n (by omega)
    rw[hz,mul_zero]
    unfold substitutionCoeff
    apply Finset.sum_eq_zero
    intro β hβ
    by_cases hsum:(∑s:Option (Fin m),(β s).val)  ≤  n
    · rw[if_pos hsum,MvPowerSeries.coeff_monomial_ne]
      · exact zero_mul _
      · intro heq
        have hh:multiDegree α  ≤  n:=by
          rw[←heq,multiDegree_eq_sum]
          exact hsum
        exact hd hh
    · rw[if_neg hsum]
lemma substitutionCoeff_add {m:ℕ} (Φ Ψ:MvPowerSeries (Option (Fin m)) R)
    (E:Fin m→PowerSeries R) (n:ℕ) :
    substitutionCoeff (Φ+Ψ) E n=substitutionCoeff Φ E n+substitutionCoeff Ψ E n := by
  unfold substitutionCoeff
  rw[←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro α hα
  simp only[map_add]
  split_ifs <;>ring

lemma eval₂_monomial_argument {m:ℕ} (α:Option (Fin m)→₀ℕ) (c:R) (E:Fin m→PowerSeries R) :
    MvPolynomial.eval₂ PowerSeries.C (argumentSeries E) (MvPolynomial.monomial α c)=
      PowerSeries.C c*(PowerSeries.X^(α none)*∏i,E i^(α (some i))) := by
  rw[MvPolynomial.eval₂_monomial,←factors_prod,factor_argumentSeries_prod]

lemma substitutionCoeff_polynomial {m:ℕ} (p:MvPolynomial (Option (Fin m)) R)
    (E:Fin m→PowerSeries R) (hE:∀i,PowerSeries.coeff 0 (E i)=0) (n:ℕ) :
    substitutionCoeff (p:MvPowerSeries (Option (Fin m)) R) E n=
      PowerSeries.coeff n (MvPolynomial.eval₂ PowerSeries.C (argumentSeries E) p) := by
  induction p using MvPolynomial.induction_on' with
  | add p q hp hq=>
      rw[MvPolynomial.coe_add,substitutionCoeff_add,MvPolynomial.eval₂_add,map_add,hp,hq]
  | monomial α c=>
      rw[MvPolynomial.coe_monomial,substitutionCoeff_monomial α c E hE n,
        eval₂_monomial_argument,PowerSeries.coeff_C_mul]
end WP.Majorant
