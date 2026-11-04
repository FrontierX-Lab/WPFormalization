import WPFormalization.HigherOrder.RecursiveSeparating
/-! Absolute summability of every genuine separating kernel coefficient.
C.4 controls the actual shifted canonical profiles, positivity bounds each bounded component,
and the genuine kernel moments control the full finite node-degree sum. -/

noncomputable section
namespace WP.HigherOrder
open Set
lemma separating_selected_length (d:List ℕ) (I:Finset ℕ) (hI:I⊆Finset.range d.length) :
    (selectedNat d I).length=I.card:=by
  rw[←selectedNat_toNat,List.length_map]
  exact selected_length_card (d.map Int.ofNat) I (by simpa only[List.length_map] using hI)

lemma separating_smallW_bound (P:PsiTheory) (d:List ℕ) (j:ℕ) (I:Finset ℕ)
    (hI:I⊆Finset.range d.length) (hst:Stable j (I.card+1))
    (Y:ℝ) (hY:Y∈Icc (0:ℝ) y₀) (u:ℕ) :
    |smallW P Y j (u::selectedNat d I)| ≤ W P j (I.card+1) Y:=by
  have hl:(u::selectedNat d I).length=I.card+1:=by simp[separating_selected_length d I hI]
  have hb:=normalized_le_all_zero P j (u::selectedNat d I) (by rw[hl];exact hst) Y hY
  have h0:=normalized_nonneg_nonempty P j (u::selectedNat d I) (by simp) Y hY
  rw[smallW,abs_of_nonneg (mul_nonneg (by positivity) h0)]
  exact (mul_le_mul_of_nonneg_left hb (by positivity:(0:ℝ) ≤ (4:ℝ)^j)).trans_eq
    (by rw[hl];rfl)

lemma separating_inner_coefficient_summable (P:PsiTheory) (t j n:ℕ) (d:List ℕ)
    (I:Finset ℕ) (hI:I⊆Finset.range d.length) (hst:Stable j (I.card+1))
    (Y:ℝ) (hY:Y∈Icc (0:ℝ) y₀) :
    Summable (fun l:ℕ=>weight Y l*PowerSeries.coeff n
      (∑u∈Finset.range (t+l-1),PowerSeries.C (smallW P Y j (u::selectedNat d I))*
        complexityShift ((2*j+I.card:ℕ):ℝ)
          (formalProfile P Y ((t+l-2-u)::selectedNat d ((Finset.range d.length)\I))))) :=by
  obtain ⟨C,B,Mb,hC,hB,hMb,hcoeff⟩:=canonical_coefficients_on_common_scale P
  obtain ⟨Cm,Mm,hCm,hMm,hops⟩:=canonical_coefficientSum_order_bounds
  let M:ℕ:=max Mb ⌈Mm⌉₊
  have hMbM:Mb ≤ M:=le_max_left _ _
  have hMmM:Mm ≤ (M:ℝ):=(Nat.le_ceil _).trans (by exact_mod_cast (le_max_right Mb ⌈Mm⌉₊))
  have hMtwo:(2:ℝ) ≤ M:=by exact_mod_cast (hMb.trans hMbM)
  have hM0:(0:ℝ) ≤ M:=by positivity
  let r:=2*j+I.card
  let K:=n+r+1
  let S:=profileOrderWeight (M:ℝ) K (t::d)
  let e:ℕ→ℝ:=fun i=>C*B^i
  have he:∀i:ℕ,0 ≤ e i:=fun i=>by dsimp[e];positivity
  let J:=PowerSeries.coeff n ((PowerSeries.exp ℝ)*PowerSeries.mk e)
  have hJ:0 ≤ J:=coeff_mul_nonneg exp_coeff_nonneg (fun i=>by simpa only[PowerSeries.coeff_mk] using he i) n
  let B₀:=W P j (I.card+1) Y
  have hB₀:0 ≤ B₀:=W_nonneg P j (I.card+1) (by omega) Y hY
  let F:ℕ→Series:=fun l=>∑u∈Finset.range (t+l-1),PowerSeries.C (smallW P Y j (u::selectedNat d I))*
    complexityShift (r:ℝ) (formalProfile P Y ((t+l-2-u)::selectedNat d ((Finset.range d.length)\I)))
  have hpoint (l:ℕ):|PowerSeries.coeff n (F l)| ≤ (B₀*J)*(S+l+1)^(2*n+1):=by
    have hKS:(K:ℝ) ≤ S:=by
      have hm:=mul_le_mul_of_nonneg_right (show (1:ℝ) ≤ M by linarith) (Nat.cast_nonneg K : (0:ℝ) ≤ K)
      dsimp[S,profileOrderWeight]
      linarith[Nat.cast_nonneg (α:=ℝ) (t::d).sum,Nat.cast_nonneg (α:=ℝ) (t::d).length]
    have hSl:(K:ℝ) ≤ S+l+1:=by linarith[Nat.cast_nonneg (α:=ℝ) l]
    have hSl0:0 ≤ S+l+1:=(Nat.cast_nonneg K).trans hSl
    have hterm (u:ℕ) (hu:u∈Finset.range (t+l-1)) :
        |PowerSeries.coeff n (PowerSeries.C (smallW P Y j (u::selectedNat d I))*
          complexityShift (r:ℝ) (formalProfile P Y ((t+l-2-u)::selectedNat d ((Finset.range d.length)\I))))| ≤
          B₀*((S+l+1)^(2*n)*J):=by
      have hb:=complexityShift_coeff_exponential_majorant (r:ℝ) (S+l+1)
        (formalProfile P Y ((t+l-2-u)::selectedNat d ((Finset.range d.length)\I))) e n K
        (by dsimp[K];omega) (by rw[abs_of_nonneg (Nat.cast_nonneg _)];exact_mod_cast (by dsimp[K];omega : r ≤ K)) hSl he (by
          intro i hi
          have hscalar:scalarOrderWeight (M:ℝ) K 1 ≤ S+l+1:=by
            dsimp[S,scalarOrderWeight,profileOrderWeight]
            simp only[Nat.cast_one]
            linarith[Nat.cast_nonneg (α:=ℝ) (t::d).sum,
              show (1:ℝ) ≤ (t::d).length by exact_mod_cast (by simp : 1 ≤ (t::d).length),
              Nat.cast_nonneg (α:=ℝ) l]
          have hlarge:profileOrderWeight (M:ℝ) K ((t+l-2-u)::selectedNat d ((Finset.range d.length)\I)) ≤ S+l+1:=by
            have hw:=separating_order_weight (M:ℝ) hM0 K K t l u d ((Finset.range d.length)\I)
              le_rfl (Finset.mem_range.mp hu)
            dsimp[S]
            linarith
          exact (hcoeff M hMbM 1 (by omega) _ (by simp) K (S+l+1) hscalar hlarge i
            (by dsimp[K];omega) Y hY).2.2)
      rw[PowerSeries.coeff_C_mul,abs_mul]
      exact mul_le_mul (separating_smallW_bound P d j I hI hst Y hY u) hb (abs_nonneg _) hB₀
    simp only[F,map_sum]
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    calc
      _ ≤ ∑u∈Finset.range (t+l-1),B₀*((S+l+1)^(2*n)*J):=Finset.sum_le_sum hterm
      _=(((t+l-1:ℕ):ℝ))*(B₀*((S+l+1)^(2*n)*J)):=by
        simp only[Finset.sum_const,Finset.card_range,nsmul_eq_mul]
      _ ≤ (S+l+1)*(B₀*((S+l+1)^(2*n)*J)):=by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact (pair_count_le_order_weight (M:ℝ) hM0 K t l d).trans (by dsimp[S];linarith)
      _=_:=by rw[pow_succ];ring
  exact (hops (M:ℝ) hMmM K (t::d).sum (t::d).length (2*n+1) n (by simp)
    (by dsimp[K];omega) (B₀*J) (by positivity) F Y hY hpoint).1
end WP.HigherOrder
