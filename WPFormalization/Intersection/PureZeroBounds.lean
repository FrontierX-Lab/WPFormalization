import WPFormalization.Statements.PrimitiveBounds
noncomputable section
namespace WP
lemma zero_string_weight_bounds (g:ℕ)(d:List ℤ)(hd:∀k∈d,0≤k)
    (hh:2≤complexity g (d.length+1))
    (hdim:(0::d).sum=3*(g:ℤ)-3+(d.length+1)):
    (2/3:ℝ)≤(∑j∈Finset.range d.length,if 0<d[j]! then 2*(d[j]!:ℝ)+1 else 0)/
      (3*((complexity g (d.length+1):ℝ)-1)) ∧
    (∑j∈Finset.range d.length,if 0<d[j]! then 2*(d[j]!:ℝ)+1 else 0)/
      (3*((complexity g (d.length+1):ℝ)-1))≤2 := by
  have hhh:(2:ℝ)≤complexity g (d.length+1):=by exact_mod_cast hh
  have hden:0<3*((complexity g (d.length+1):ℝ)-1):=by linarith
  have hsum:=sum_positive_string_weights d hd
  have hdimR:(d.sum:ℝ)=3*(g:ℝ)-3+(d.length+1):=by
    simp only [List.sum_cons,zero_add] at hdim
    exact_mod_cast hdim
  have hc:(complexity g (d.length+1):ℝ)=2*g+d.length-1:=by
    unfold complexity at hh ⊢
    rw [Nat.cast_sub (by omega)]
    push_cast
    ring
  have hz:(d.count 0:ℝ)≤d.length:=by exact_mod_cast List.count_le_length (a:=(0:ℤ)) (l:=d)
  have hz0:0≤(d.count 0:ℝ):=Nat.cast_nonneg _
  have hlen:0≤(d.length:ℝ):=Nat.cast_nonneg _
  have hg:0≤(g:ℝ):=Nat.cast_nonneg _
  constructor
  · apply (le_div_iff₀ hden).2
    rw [hsum,hc]
    linarith
  · apply (div_le_iff₀ hden).2
    rw [hsum,hc]
    linarith
end WP
namespace WP
lemma signedPureC_zero_two_sided (P:PsiTheory)(g:ℕ)(d:List ℤ)
    (hd:∀k∈d,0≤k)(hh:2≤complexity g (d.length+1))
    (hdim:(0::d).sum=3*(g:ℤ)-3+(d.length+1))
    (L U:ℝ)(hL:0≤L)(hU:0≤U)
    (hb:∀j∈Finset.range d.length,0<d[j]!→
      L≤ signedPureC P g ((d[j]!-1)::d.eraseIdx j) ∧
      signedPureC P g ((d[j]!-1)::d.eraseIdx j)≤U):
    (2/3:ℝ)*L≤ signedPureC P g (0::d) ∧ signedPureC P g (0::d)≤2*U := by
  have hw:=zero_string_weight_bounds g d hd hh hdim
  have hhh:(2:ℝ)≤complexity g (d.length+1):=by exact_mod_cast hh
  have hden:0<3*((complexity g (d.length+1):ℝ)-1):=by linarith
  have he:signedPureC P g (0::d)=∑j∈Finset.range d.length,
      (if 0<d[j]! then (2*(d[j]!:ℝ)+1)/(3*((complexity g (d.length+1):ℝ)-1))*
        signedPureC P g ((d[j]!-1)::d.eraseIdx j) else 0):=by
    rw [show (0:ℤ)=((0:ℕ):ℤ) from rfl,signedPureC_dvv P g 0 d hd hh]
    simp only [primitiveDvvRHS,Nat.zero_sub,Finset.range_zero,Finset.sum_empty,
      mul_zero,ite_self,add_zero,Int.natCast_zero,zero_add]
    apply Finset.sum_congr rfl
    intro j hj
    by_cases hp:0<d[j]!
    · simp only [hp,ite_true]
    · have hj':=Finset.mem_range.mp hj
      have hv:=hd (d[j]!) (by simpa [hj'] using (List.getElem_mem (l:=d) (n:=j) hj'))
      have hz:d[j]! = 0:=by omega
      have hvan:signedPureC P g ((d[j]!-1)::d.eraseIdx j)=0:=by
        apply signedPureC_vanish
        refine Or.inr (Or.inl ⟨-1,?_,by norm_num⟩)
        simp [hz]
      simp only [hp,ite_false,hvan,mul_zero]
  have hweights:(∑j∈Finset.range d.length,if 0<d[j]! then
      (2*(d[j]!:ℝ)+1)/(3*((complexity g (d.length+1):ℝ)-1)) else 0)=
      (∑j∈Finset.range d.length,if 0<d[j]! then 2*(d[j]!:ℝ)+1 else 0)/
        (3*((complexity g (d.length+1):ℝ)-1)):=by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j hj
    split_ifs <;> simp
  constructor
  · calc
      _ ≤ ((∑j∈Finset.range d.length,if 0<d[j]! then
          (2*(d[j]!:ℝ)+1)/(3*((complexity g (d.length+1):ℝ)-1)) else 0))*L:=by
        rw [hweights];exact mul_le_mul_of_nonneg_right hw.1 hL
      _ ≤ signedPureC P g (0::d):=by
        rw [he,Finset.sum_mul]
        apply Finset.sum_le_sum
        intro j hj
        by_cases hp:0<d[j]!
        · simp only [hp,ite_true]
          exact mul_le_mul_of_nonneg_left (hb j hj hp).1 (div_nonneg (by positivity) hden.le)
        · simp only [hp,ite_false,zero_mul,le_refl]
  · calc
      signedPureC P g (0::d) ≤ (∑j∈Finset.range d.length,if 0<d[j]! then
          (2*(d[j]!:ℝ)+1)/(3*((complexity g (d.length+1):ℝ)-1)) else 0)*U:=by
        rw [he,Finset.sum_mul]
        apply Finset.sum_le_sum
        intro j hj
        by_cases hp:0<d[j]!
        · simp only [hp,ite_true]
          exact mul_le_mul_of_nonneg_left (hb j hj hp).2 (div_nonneg (by positivity) hden.le)
        · simp only [hp,ite_false,zero_mul,le_refl]
      _ ≤ 2*U:=by rw [hweights];exact mul_le_mul_of_nonneg_right hw.2 hU
end WP
namespace WP
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma signedPureC_all_zero_bounds_aux (P:PsiTheory)(N:ℕ):
    ∀g:ℕ,∀d:List ℤ,Stable g d.length→(∀k∈d,0≤k)→
      d.sum=3*(g:ℤ)-3+d.length→d.length=N→
      (1/6:ℝ)*(2/3:ℝ)^(d.count 0)≤ signedPureC P g d ∧
      signedPureC P g d≤(2:ℝ)^(d.count 0) := by
  induction N using Nat.strong_induction_on with
  | h N ih =>
    intro g d hst hd hdim hN
    by_cases hsmall:complexity g d.length≤1
    · have hcases:(g=0 ∧d.length=3)∨(g=1 ∧d.length=1):=by
        unfold Stable at hst
        unfold complexity at hsmall
        omega
      rcases hcases with ⟨rfl,hlen⟩|⟨rfl,hlen⟩
      · have hsum:d.sum=0:=by rw [hlen] at hdim;norm_num at hdim ⊢;exact hdim
        have hd0:=eq_replicate_zero_of_nonneg_sum d hd hsum
        rw [hlen] at hd0
        subst d
        norm_num [signedPureC,primitiveScale,weighted,doubleWeight,complexity,
          oddFactorial,Finset.prod_range_succ,P.base₀]
      · obtain ⟨p,rfl⟩:=List.length_eq_one_iff.mp hlen
        have hp:p=1:=by simpa using hdim
        subst p
        norm_num [signedPureC,primitiveScale,weighted,doubleWeight,complexity,
          oddFactorial,Finset.prod_range_succ,P.base₁]
    · have hh:2≤complexity g d.length:=by omega
      by_cases hone:(1:ℤ)∈d
      · let t:=d.erase 1
        have hp:d.Perm (1::t):=List.perm_cons_erase hone
        have hl:d.length=t.length+1:=by simpa using hp.length_eq
        have ht:∀k∈t,0≤k:=fun k hk=>hd k (List.mem_of_mem_erase hk)
        have hdim':t.sum=3*(g:ℤ)-3+t.length:=by
          have hs:=hp.sum_eq
          simp only [List.sum_cons] at hs
          rw [hl] at hdim
          push_cast at hdim
          omega
        have hst':Stable g t.length:=by
          unfold Stable
          unfold complexity at hh
          rw [hl] at hh
          omega
        have hi:=ih t.length (by omega) g t hst' ht hdim' rfl
        have hc:d.count 0=t.count 0:=by
          have hc:=hp.count_eq 0
          simpa using hc
        rw [signedPureC_perm P g hp,signedPureC_dilaton P g t hst',hc]
        exact hi
      · by_cases hzero:(0:ℤ)∈d
        · let t:=d.erase 0
          have hp:d.Perm (0::t):=List.perm_cons_erase hzero
          have hl:d.length=t.length+1:=by simpa using hp.length_eq
          have ht:∀k∈t,0≤k:=fun k hk=>hd k (List.mem_of_mem_erase hk)
          have ht1:(1:ℤ)∉t:=fun hk=>hone (List.mem_of_mem_erase hk)
          have hdim':(0::t).sum=3*(g:ℤ)-3+(t.length+1):=by
            rw [←hp.sum_eq]
            simpa only [hl,Nat.cast_add,Nat.cast_one] using hdim
          have hh':2≤complexity g (t.length+1):=by rw [←hl];exact hh
          have hcnt:d.count 0=t.count 0+1:=by
            have hc:=hp.count_eq 0
            simpa [add_comm] using hc
          have hb:∀j∈Finset.range t.length,0<t[j]!→
              (1/6:ℝ)*(2/3:ℝ)^(t.count 0)≤ signedPureC P g ((t[j]!-1)::t.eraseIdx j) ∧
              signedPureC P g ((t[j]!-1)::t.eraseIdx j)≤(2:ℝ)^(t.count 0):=by
            intro j hj hjp
            have hj':=Finset.mem_range.mp hj
            have hjmem:t[j]!∈t:=by simpa [hj'] using (List.getElem_mem (l:=t) (n:=j) hj')
            have hv1:t[j]!≠1:=fun h=>ht1 (h▸hjmem)
            have hv:2≤t[j]!:=by omega
            let c:=(t[j]!-1)::t.eraseIdx j
            have hlen:c.length=t.length:=by
              dsimp[c]
              simp only [List.length_cons,List.length_eraseIdx_of_lt hj']
              omega
            have hcd:∀k∈c,0≤k:=by
              intro k hk
              rcases List.mem_cons.mp hk with hk|hk
              · subst k;omega
              · exact ht k (List.mem_of_mem_eraseIdx hk)
            have hcs:Stable g c.length:=by
              rw [hlen]
              unfold Stable
              unfold complexity at hh'
              omega
            have hcdim:c.sum=3*(g:ℤ)-3+c.length:=by
              simpa only [c,zero_add,List.length_cons,Nat.cast_add,Nat.cast_one] using
                merger_dimension g 0 t hdim' j hj'
            have hcc:c.count 0=t.count 0:=by
              have hpj:=List.getElem_cons_eraseIdx_perm hj'
              have hc:=hpj.count_eq 0
              have hj0:t[j]≠(0:ℤ):=by simpa [hj'] using (show t[j]!≠0 by omega)
              simp only [List.count_cons,beq_iff_eq,hj0,ite_false,add_zero] at hc
              dsimp[c]
              simp only [List.count_cons,beq_iff_eq,show t[j]!-1≠0 by omega,ite_false,add_zero]
              exact hc
            have hi:=ih c.length (by omega) g c hcs hcd hcdim rfl
            rwa [hcc] at hi
          have hstep:=signedPureC_zero_two_sided P g t ht hh' hdim'
            ((1/6:ℝ)*(2/3:ℝ)^(t.count 0)) ((2:ℝ)^(t.count 0)) (by positivity) (by positivity) hb
          rw [signedPureC_perm P g hp,hcnt,pow_succ,pow_succ]
          constructor <;> nlinarith [hstep.1,hstep.2]
        · have hdpos:∀k∈d,0<k:=by
            intro k hk
            have hk0:=hd k hk
            have hkz:k≠0:=fun h=>hzero (h▸hk)
            omega
          have hg:1≤g:=by
            have hsum:=length_le_sum_of_positive (d.map Int.toNat) (by
              intro k hk
              obtain ⟨j,hj,rfl⟩:=List.mem_map.mp hk
              have :=hdpos j hj
              omega)
            have hmap:((d.map Int.toNat).sum:ℤ)=d.sum:=by
              rw [←sum_map_int,map_ofNat_toNat d hd]
            simp only [List.length_map] at hsum
            have hsum':(d.length:ℤ)≤d.sum:=by
              have hcast:(d.length:ℤ)≤((d.map Int.toNat).sum:ℤ):=by exact_mod_cast hsum
              rwa [hmap] at hcast
            omega
          have hcnt:d.count 0=0:=List.count_eq_zero.mpr hzero
          rw [hcnt,pow_zero,pow_zero,mul_one]
          refine ⟨signedPrimitive_lower_aux P _ g d hg hst hd (by omega) hdim rfl,?_⟩
          exact (signedPrimitive_upper_aux P _ g d hg hst hdpos hdim rfl).trans (primitiveMajorant_le_one _)
end WP
namespace WP
/- Lemma5.2(i), Eq5.1: exact zero-count bounds for every stable pure tuple.
The explicit PsiTheory interface and classic primitive bounds remain visible. -/
@[blueprint "lem:terminal"]
lemma pureC_zero_bounds (P:PsiTheory)(g:ℕ)(d:List ℕ)(hs:Stable g d.length)
    (hdim:d.sum=dimension g d.length):
    (1/6:ℝ)*(2/3:ℝ)^(d.count 0)≤ pureC P g d ∧
      pureC P g d≤(2:ℝ)^(d.count 0) := by
  have hd:∀k∈d.map Int.ofNat,0≤k:=by
    intro k hk
    obtain ⟨j,hj,rfl⟩:=List.mem_map.mp hk
    exact Int.natCast_nonneg _
  have hdim':(d.map Int.ofNat).sum=3*(g:ℤ)-3+(d.map Int.ofNat).length:=by
    rw [sum_map_int,List.length_map,hdim,dimension_cast_of_stable g d.length hs]
  have hb:=signedPureC_all_zero_bounds_aux P d.length g (d.map Int.ofNat)
    (by simpa using hs) hd hdim' (by simp)
  have hc:(d.map Int.ofNat).count 0=d.count 0:=by
    exact List.count_map_of_injective d Int.ofNat Int.ofNat_injective 0
  simpa only [hc,←pureC_signed] using hb
end WP
