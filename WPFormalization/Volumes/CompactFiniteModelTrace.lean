import WPFormalization.Volumes.CompactFiniteModelGrowth
/-! Exact full finite-order real traces for the genuine compact model,
including its actual standardized tilt and integer saddle center. -/
noncomputable section
namespace WP.Analysis
open Set Filter
open scoped Topology
lemma compact_finite_centered_physical_at (P:PsiTheory)(g p J:ℕ)(hs:Stable g p)
    (S l Bc:ℂ→ℂ)(f:ℕ→ℂ→ℂ)(x t:ℝ)
    (hx:x∈Ioo (0:ℝ) xCritical)(hz:compactRealTilt l x t∈Ioo (0:ℝ) xCritical)
    (hl:l (x:ℂ)=(1/Real.sqrt (WP.euler WP.Psi x):ℝ))
    (hSx:S (x:ℂ)=(extractionS x:ℂ))
    (hSz:S (compactRealTilt l x t:ℂ)=(extractionS (compactRealTilt l x t):ℂ))
    (hν:complexEuler S (x:ℂ)=(WP.Psi x:ℂ))
    (hBx:Bc (x:ℂ)=(extractionB p x:ℂ))
    (hBz:Bc (compactRealTilt l x t:ℂ)=(extractionB p (compactRealTilt l x t):ℂ))
    (hf:∀Y∈Icc (0:ℝ) y₀,f 0 (Y:ℂ)=(HigherOrder.markedCoefficient P p 0 Y:ℂ)):
    Complex.exp ((complexity g p:ℂ)*centeredExponentialPhase S l ((x:ℂ),-Complex.I*(t:ℂ)))*
        (∑j∈Finset.range (J+1),compactPremorseAmplitude P Bc l f j ((x:ℂ),-Complex.I*(t:ℂ))/(complexity g p:ℂ)^j)/
          HigherOrder.finiteMarkedFactor f (complexity g p:ℝ) J (PositiveConvolution.planarInverse P (x:ℂ))=
      ((Real.exp (-(complexity g p:ℝ)*WP.Psi x*t/Real.sqrt (WP.euler WP.Psi x))*
        (markedModel g p (inverseY (compactRealTilt l x t))/markedModel g p (inverseY x)):ℝ):ℂ)*
          (HigherOrder.finiteMarkedFactor f (complexity g p:ℝ) J (inverseY (compactRealTilt l x t):ℂ)/
            HigherOrder.finiteMarkedFactor f (complexity g p:ℝ) J (inverseY x:ℂ)):=by
  let z:ℝ:=compactRealTilt l x t
  have hpoint:compactModelPoint l ((x:ℂ),-Complex.I*(t:ℂ))=(z:ℂ):=by
    dsimp only[compactModelPoint,z,compactRealTilt]
    rw[hl]
    simp only[Complex.ofReal_re]
    have he:(Complex.I*(1/(Real.sqrt (WP.euler WP.Psi x):ℂ)))*(-Complex.I*(t:ℂ))=
        ((t*(1/Real.sqrt (WP.euler WP.Psi x)):ℝ):ℂ):=by
      push_cast
      rw[←mul_assoc]
      ring_nf
      simp
    rw[Complex.ofReal_div,Complex.ofReal_one,he,←Complex.ofReal_exp,←Complex.ofReal_mul]
  have hzI:z∈Ico (0:ℝ) xCritical:=⟨hz.1.le,hz.2⟩
  have hY:inverseY z∈Ico (0:ℝ) y₀:=(inverseY_branch z hzI).1
  have hfp:f 0 (PositiveConvolution.planarInverse P (z:ℂ))=1:=by
    rw[PositiveConvolution.planarInverse_ofReal P z hzI,hf _ ⟨hY.1,hY.2.le⟩]
    simp
  have hsum:(∑j∈Finset.range (J+1),compactPremorseAmplitude P Bc l f j ((x:ℂ),-Complex.I*(t:ℂ))/(complexity g p:ℂ)^j)=
      compactPremorseAmplitude P Bc l f 0 ((x:ℂ),-Complex.I*(t:ℂ))*
        HigherOrder.finiteMarkedFactor f (complexity g p:ℝ) J (PositiveConvolution.planarInverse P (z:ℂ)):=by
    unfold compactPremorseAmplitude HigherOrder.finiteMarkedFactor
    rw[hpoint,hfp,mul_one,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    push_cast
    ring
  rw[hsum,←mul_assoc,compact_centered_leading_real_trace P g p hs S l Bc f x t hx hz hl hSx hSz hν hBx hBz hf,
    PositiveConvolution.planarInverse_ofReal P x ⟨hx.1.le,hx.2⟩,
    PositiveConvolution.planarInverse_ofReal P z hzI]
  ring
end WP.Analysis

namespace WP.Analysis
open Set Filter
open scoped Topology
lemma compact_centered_finite_standard_trace (P:PsiTheory)(g p k J:ℕ)(hs:Stable g p)
    (S l Bc:ℂ→ℂ)(f:ℕ→ℂ→ℂ)(x w:ℝ)(hh:0<(complexity g p:ℝ))
    (hx:x∈Ioo (0:ℝ) xCritical)
    (hz:compactRealTilt l x (w/Real.sqrt (complexity g p:ℝ))∈Ioo (0:ℝ) xCritical)
    (hl:l (x:ℂ)=(1/Real.sqrt (WP.euler WP.Psi x):ℝ))
    (hSx:S (x:ℂ)=(extractionS x:ℂ))
    (hSz:S (compactRealTilt l x (w/Real.sqrt (complexity g p:ℝ)):ℂ)=
      (extractionS (compactRealTilt l x (w/Real.sqrt (complexity g p:ℝ))):ℂ))
    (hν:complexEuler S (x:ℂ)=(WP.Psi x:ℂ))
    (hBx:Bc (x:ℂ)=(extractionB p x:ℂ))
    (hBz:Bc (compactRealTilt l x (w/Real.sqrt (complexity g p:ℝ)):ℂ)=
      (extractionB p (compactRealTilt l x (w/Real.sqrt (complexity g p:ℝ))):ℂ))
    (hfr:∀j Y,Y∈Icc (0:ℝ) y₀→f j (Y:ℂ)=(HigherOrder.markedCoefficient P p j Y:ℂ))
    (hk:(k:ℝ)=(complexity g p:ℝ)*WP.Psi x):
    let h:ℝ:=complexity g p
    let z:ℝ:=x*Real.exp (w/Real.sqrt (h*WP.euler WP.Psi x))
    z∈Ioo (0:ℝ) xCritical ∧
    compactCenteredFiniteModel P Bc S l f h J (x:ℂ) (w:ℂ)=
      Complex.exp (-(k:ℂ)*(w:ℂ)/(Real.sqrt (h*WP.euler WP.Psi x):ℂ))*
        ((markedModel g p (inverseY z)/markedModel g p (inverseY x)*
          HigherOrder.realFiniteMarkedFactor P p h J (inverseY z)/
            HigherOrder.realFiniteMarkedFactor P p h J (inverseY x):ℝ):ℂ):=by
  dsimp only
  let h:ℝ:=complexity g p
  let v:ℝ:=WP.euler WP.Psi x
  let z:ℝ:=compactRealTilt l x (w/Real.sqrt h)
  have hzEq:z=x*Real.exp (w/Real.sqrt (h*v)):=by
    dsimp only[z,compactRealTilt]
    rw[hl,Complex.ofReal_re,Real.sqrt_mul hh.le]
    congr 1
    congr 1
    ring
  have hu:-Complex.I*(w:ℂ)/(Real.sqrt h:ℂ)= -Complex.I*((w/Real.sqrt h:ℝ):ℂ):=by push_cast;ring
  have ht:=compact_finite_centered_physical_at P g p J hs S l Bc f x (w/Real.sqrt h)
    hx hz hl hSx hSz hν hBx hBz (hfr 0)
  have hfinite(Y:ℝ)(hYi:Y∈Ico (0:ℝ) y₀):
      HigherOrder.finiteMarkedFactor f h J (Y:ℂ)=(HigherOrder.realFiniteMarkedFactor P p h J Y:ℂ):=by
    unfold HigherOrder.finiteMarkedFactor HigherOrder.realFiniteMarkedFactor
    push_cast
    apply Finset.sum_congr rfl
    intro j hj
    rw[hfr j Y ⟨hYi.1,hYi.2.le⟩]
  have hYx:inverseY x∈Ico (0:ℝ) y₀:=(inverseY_branch x ⟨hx.1.le,hx.2⟩).1
  have hYz:inverseY z∈Ico (0:ℝ) y₀:=(inverseY_branch z ⟨hz.1.le,hz.2⟩).1
  refine ⟨by rw[←hzEq];exact hz,?_⟩
  unfold compactCenteredFiniteModel
  rw[hu]
  simp only[Complex.ofReal_natCast]
  rw[ht]
  change ((Real.exp (-h*WP.Psi x*(w/Real.sqrt h)/Real.sqrt v)*
      (markedModel g p (inverseY z)/markedModel g p (inverseY x)):ℝ):ℂ)*
      (HigherOrder.finiteMarkedFactor f h J (inverseY z:ℂ)/HigherOrder.finiteMarkedFactor f h J (inverseY x:ℂ))=_
  rw[hfinite _ hYz,hfinite _ hYx,←hzEq]
  have hexp:((Real.exp (-h*WP.Psi x*(w/Real.sqrt h)/Real.sqrt v):ℝ):ℂ)=
      Complex.exp (-(k:ℂ)*(w:ℂ)/(Real.sqrt (h*v):ℂ)):=by
    rw[Complex.ofReal_exp,Real.sqrt_mul hh.le]
    have hkc:(k:ℂ)=(h:ℂ)*(WP.Psi x:ℂ):=by exact_mod_cast hk
    rw[hkc]
    push_cast
    congr 1
    ring
  rw[Complex.ofReal_mul,hexp]
  push_cast
  ring
end WP.Analysis
