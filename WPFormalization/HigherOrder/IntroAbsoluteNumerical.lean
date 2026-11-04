import WPFormalization.HigherOrder.CanonicalExtractionStatement
import WPFormalization.HigherOrder.UnmarkedVolumeProof
import WPFormalization.Volumes.LeadingNormalization
/-! Assembly of Theorem 1.1 in the numerical model. This proof explicitly
uses the proved original canonical expansion, with its registered classical
phase-one inputs. The independent unmarked branch is also proved.
The geometric realization remains an explicit input of the public theorem. -/
noncomputable section
namespace WP.HigherOrder
open Filter
open scoped Topology
lemma complexity_one_cast (g:ℕ)(hg:1≤g):(complexity g 1:ℝ)=2*(g:ℝ)-1:=by
  unfold complexity
  rw[Nat.cast_sub (by omega)]
  push_cast
  ring

lemma intro_absolute_numerical_assembly (P:PsiTheory):
    ∃C B c:ℝ,0<C ∧ 0<B ∧ 0<c ∧ ∃G:ℕ,0<G ∧
      (∀g:ℕ,G≤g→∀K:ℕ,(K:ℝ)≤c*Real.sqrt (2*(g:ℝ)-1)→∀n:ℕ,
        |volumeModel P g n/leadingVolume g n-
          ∑j∈Finset.range (K+1),absoluteCoefficient P j g n/(2*(g:ℝ)-1)^j|≤
            C*B^(K+1)*((K+1).factorial:ℝ)^2/(2*(g:ℝ)-1)^(K+1)) ∧
      (∀g:ℕ,G≤g→∀j n:ℕ,|absoluteCoefficient P j g n|≤C*B^j*(j.factorial:ℝ)^2) ∧
      (∃C':ℝ,0<C' ∧ ∀g:ℕ,G≤g→∀n:ℕ,
        |volumeModel P g n/leadingVolume g n-1|≤C'/(g:ℝ)) ∧
      (∃c' a C':ℝ,0<c' ∧ c'≤c ∧ 0<a ∧ 0<C' ∧ ∀g:ℕ,G≤g→∀n:ℕ,
        |volumeModel P g n/leadingVolume g n-
          ∑j∈Finset.range (⌊c'*Real.sqrt (2*(g:ℝ)-1)⌋₊+1),
            absoluteCoefficient P j g n/(2*(g:ℝ)-1)^j|≤
              C'*Real.exp (-a*Real.sqrt (2*(g:ℝ)-1))):=by
  obtain ⟨Cc,Bc,cc,Hc,hCc,hBc,hcc,hHc,hext,_,_,hcerr,_⟩:=canonical_expansion P 1 (by norm_num)
  obtain ⟨Cu,Bu,cu,hCu,hBu,hcu,Nu,hNu,hunorm,huerr,_⟩:=unmarked_absolute_expansion_proof P
  obtain ⟨Ω,AC,hΩ,hcover,ha,hrest,hbound⟩:=hext
  let C:ℝ:=Cu+Cc
  let B:ℝ:=Bu+Bc
  let c:ℝ:=min cu cc
  have hC:0<C:=by dsimp[C];positivity
  have hB:0<B:=by dsimp[B];positivity
  have hc:0<c:=lt_min hcu hcc
  have hCuC:Cu≤C:=by dsimp[C];linarith
  have hCcC:Cc≤C:=by dsimp[C];linarith
  have hBuB:Bu≤B:=by dsimp[B];linarith
  have hBcB:Bc≤B:=by dsimp[B];linarith
  obtain ⟨c',a,H,hc',hc'c,ha0,hH,hopt⟩:=Analysis.gevreyTwo_optimal_scalar B c hB hc
  have hscale:=Analysis.complexity_real_tendsto_atTop 1
  obtain ⟨Nc,hNc⟩:=eventually_atTop.1 (hscale.eventually (eventually_ge_atTop Hc))
  obtain ⟨No,hNo⟩:=eventually_atTop.1 (hscale.eventually (eventually_ge_atTop H))
  let G:ℕ:=max Nu (max Nc (max No 2))
  have hG2:2≤G:=by dsimp[G];omega
  have hGNu:Nu≤G:=le_max_left _ _
  have hGNc:Nc≤G:=((le_max_left _ _).trans (le_max_right _ _))
  have hGNo:No≤G:=by dsimp[G];omega
  have herrAll:∀g:ℕ,G≤g→∀K:ℕ,(K:ℝ)≤c*Real.sqrt (2*(g:ℝ)-1)→∀n:ℕ,
      |volumeModel P g n/leadingVolume g n-
        ∑j∈Finset.range (K+1),absoluteCoefficient P j g n/(2*(g:ℝ)-1)^j|≤
          C*B^(K+1)*((K+1).factorial:ℝ)^2/(2*(g:ℝ)-1)^(K+1):=by
    intro g hg K hK n
    have hg2:2≤g:=hG2.trans hg
    have hh:(0:ℝ)<2*(g:ℝ)-1:=by
      have hgR:(2:ℝ)≤g:=by exact_mod_cast hg2
      linarith
    have hco:=complexity_one_cast g (by omega)
    cases n with
    | zero=>
      have hw:(K:ℝ)≤cu*Real.sqrt (complexity g 1:ℝ):=by
        rw[hco]
        exact hK.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) (Real.sqrt_nonneg _))
      have he:=huerr g (hGNu.trans hg) K hw
      simp only[hco] at he
      simp only[absoluteCoefficient,ite_true]
      exact he.trans (gevreyTwo_majorant_mono Cu Bu C B _ (K+1) hBu.le hC.le hCuC hBuB hh)
    | succ k=>
      have hw:(K:ℝ)≤cc*Real.sqrt (complexity g 1:ℝ):=by
        rw[hco]
        exact hK.trans (mul_le_mul_of_nonneg_right (min_le_right _ _) (Real.sqrt_nonneg _))
      have he:=hcerr g k K (hNc g (hGNc.trans hg)) hw
      dsimp only at he
      rw[←volume_ratio_succ_extraction_ratio P g k (by omega)] at he
      have he':|volumeModel P g (k+1)/leadingVolume g (k+1)-
          ∑j∈Finset.range (K+1),absoluteCoefficient P j g (k+1)/(2*(g:ℝ)-1)^j|≤
          Cc*Bc^(K+1)*((K+1).factorial:ℝ)^2/(2*(g:ℝ)-1)^(K+1):=by
        simpa only[absoluteCoefficient,show k+1≠0 by omega,ite_false,Nat.add_sub_cancel,hco] using he
      exact he'.trans (gevreyTwo_majorant_mono Cc Bc C B _ (K+1) hBc.le hC.le hCcC hBcB hh)
  have hnormAll:∀g:ℕ,G≤g→∀j n:ℕ,|absoluteCoefficient P j g n|≤C*B^j*(j.factorial:ℝ)^2:=by
    intro g hg j n
    have hg2:2≤g:=hG2.trans hg
    have hh:(0:ℝ)<2*(g:ℝ)-1:=by
      have hgR:(2:ℝ)≤g:=by exact_mod_cast hg2
      linarith
    cases n with
    | zero=>
      simp only[absoluteCoefficient,ite_true]
      apply (hunorm j).trans
      gcongr
    | succ k=>
      have hY: densityY (2*(k:ℝ)/(2*(g:ℝ)-1))∈Set.Icc (0:ℝ) y₀:=by
        have he:=Analysis.densityY_spec (2*(k:ℝ)/(2*(g:ℝ)-1)) (by positivity)
        exact ⟨he.1.1,he.1.2.le⟩
      have he:=hbound j (densityY (2*(k:ℝ)/(2*(g:ℝ)-1))) (hcover _ hY)
      rw[hrest j _ hY,Complex.norm_real,Real.norm_eq_abs] at he
      simp only[absoluteCoefficient,show k+1≠0 by omega,ite_false,Nat.add_sub_cancel]
      apply he.trans
      gcongr
  refine ⟨C,B,c,hC,hB,hc,G,by omega,herrAll,hnormAll,⟨C*B,mul_pos hC hB,?_⟩,⟨c',a,C,hc',hc'c,ha0,hC,?_⟩⟩
  · intro g hg n
    have hg2:2≤g:=hG2.trans hg
    have hgR:(2:ℝ)≤g:=by exact_mod_cast hg2
    have hh:0<2*(g:ℝ)-1:=by linarith
    have he:=herrAll g hg 0 (by simp only[Nat.cast_zero];positivity) n
    simp only[Finset.sum_range_one,absoluteCoefficient_zero,pow_zero,div_one,Nat.zero_add,
      Nat.factorial_one,Nat.cast_one,one_pow,mul_one,pow_one] at he
    exact he.trans (div_le_div_of_nonneg_left (mul_pos hC hB).le (by linarith) (by linarith))
  · intro g hg n
    have hco:=complexity_one_cast g (by have :=hG2.trans hg;omega)
    let h:ℝ:=2*(g:ℝ)-1
    let K:ℕ:=⌊c'*Real.sqrt h⌋₊
    have hw:(K:ℝ)≤c*Real.sqrt h:=
      (Nat.floor_le (mul_nonneg hc'.le (Real.sqrt_nonneg h))).trans
        (mul_le_mul_of_nonneg_right hc'c (Real.sqrt_nonneg h))
    have he:=herrAll g hg K hw n
    have ht:=hopt h (by have hh:=hNo g (hGNo.trans hg);simpa only[hco] using hh)
    change B^(K+1)*((K+1).factorial:ℝ)^2/h^(K+1)≤Real.exp (-a*Real.sqrt h) at ht
    apply he.trans
    convert mul_le_mul_of_nonneg_left ht hC.le using 1 <;>ring
end WP.HigherOrder
