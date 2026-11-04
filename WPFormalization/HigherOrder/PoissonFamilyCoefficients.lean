import WPFormalization.HigherOrder.PoissonCentralScaling
import WPFormalization.HigherOrder.OriginPoissonAmplitude
noncomputable section
namespace WP.HigherOrder
open Set

def poissonFamilyCoefficient (f:ℕ→ℂ × ℂ → ℂ) (n:ℕ) (ν:ℂ):ℂ:=
  ∑s∈Finset.range (n+1),poissonCentralAmplitude (f s) (n-s) ν

lemma poissonFamilyCoefficient_zero (f:ℕ→ℂ × ℂ → ℂ) (ν:ℂ):
    poissonFamilyCoefficient f 0 ν=f 0 (ν,ν):=by simp[poissonFamilyCoefficient]
lemma poissonFamilyCoefficient_at_zero (f:ℕ→ℂ × ℂ → ℂ) (n:ℕ):
    poissonFamilyCoefficient f n 0=f n (0,0):=by
  unfold poissonFamilyCoefficient
  rw[Finset.sum_eq_single n]
  · simp
  · intro s hs hsn
    have hsle:s≤n:=Nat.le_of_lt_succ (Finset.mem_range.mp hs)
    exact poissonCentralAmplitude_at_zero (f s) (n-s) (by omega)
  · simp
lemma poissonFamilyCoefficient_analyticOnNhd (f:ℕ→ℂ × ℂ → ℂ) (U:Set ℂ)
    (ha:∀s i,AnalyticOnNhd ℂ (poissonCentralAmplitude (f s) i) U) (n:ℕ):
    AnalyticOnNhd ℂ (poissonFamilyCoefficient f n) U:=by
  intro ν hν
  exact Finset.analyticAt_fun_sum _ (fun s hs=>ha s (n-s) ν hν)
end WP.HigherOrder
namespace WP.Analysis
lemma phaseAmplitude_at_origin (Z:ℂ × ℂ → ℂ) (H:ℂ→ℂ) (hZ0:Z 0=0)
    (hq:phaseQuotient Z 0 0≠0):phaseAmplitude Z H 0=H 0:=by
  have hd:deriv (fun u:ℂ=>Z (u,0)) 0≠0:=by simpa only[phaseQuotient,ite_true] using hq
  simp only[phaseAmplitude,Prod.fst_zero,Prod.snd_zero,hZ0,phaseQuotient,ite_true]
  field_simp
end WP.Analysis
namespace WP.HigherOrder
open Set
lemma originPoissonAmplitude_at_origin (P:PsiTheory) (p j:ℕ) (Bc:ℂ→ℂ) (L:ℕ→ℂ→ℂ)
    (Z:ℂ × ℂ → ℂ) (hBc:Bc 0=1) (hL:L j 0=(markedCoefficient P p j 0:ℂ))
    (hZ:Z 0=0) (hq:phaseQuotient Z 0 0≠0):
    originPoissonAmplitude P p j Bc L Z 0=(markedCoefficient P p j 0:ℂ):=by
  rw[originPoissonAmplitude,Analysis.phaseAmplitude_at_origin Z _ hZ hq]
  simp only[originMarkedAmplitude,hBc,PositiveConvolution.planarInverse_zero,hL,one_mul]
end WP.HigherOrder
