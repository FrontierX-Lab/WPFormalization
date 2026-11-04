import WPFormalization.Volumes.LeadingNormalization
import WPFormalization.Volumes.DiagonalChainAlgebra
/-! The exact finite volume/coefficient identity in (14.10), including
the maximal planar cusp type k=n. -/
noncomputable section
namespace WP.RandomGeometry

def primitivePlanarWeight (P:PsiTheory)(k:ℕ):ℝ:=
  volumeModel P 0 (k+1)/((k.factorial:ℝ)*(2*Real.pi^2)^(k-2))

lemma primitive_planar_coefficient_identity (P:PsiTheory)(g n k:ℕ)
    (hg:2≤g)(hk:2≤k)(hkn:k≤n):
    (n.choose k:ℝ)*volumeModel P 0 (k+1)*volumeModel P g (n-k+1)/volumeModel P g n=
      primitivePlanarWeight P k*((n:ℝ)/(2*Real.pi^2))*
        (realCoeff (iteratedDeriv 1 (Phi P g)) (n-k)/
          realCoeff (iteratedDeriv 1 (Phi P g)) (n-1)):=by
  have hn:1≤n:=by omega
  have hV:volumeModel P g n≠0:=
    (diagonal_volume_pos_nonempty P g n hn (by unfold Stable;omega)).ne'
  have hP:2*Real.pi^2≠0:=by positivity
  have hd:dimension g n=dimension g (n-k+1)+(k-2)+1:=by unfold dimension;omega
  have hp:(2*Real.pi^2)^(dimension g n)=
      (2*Real.pi^2)^(dimension g (n-k+1))*(2*Real.pi^2)^(k-2)*(2*Real.pi^2):=by
    rw[hd,pow_add,pow_add,pow_one]
  have hnf:(n.factorial:ℝ)=(n:ℝ)*((n-1).factorial:ℝ):=by
    have he:n.factorial=n*(n-1).factorial:=by
      calc
        n.factorial=(n-1+1).factorial:=by congr 1;omega
        _=(n-1+1)*(n-1).factorial:=Nat.factorial_succ _
        _=n*(n-1).factorial:=by congr 1;omega
    exact_mod_cast he
  rw[marked_one_realCoeff_volume,marked_one_realCoeff_volume,
    Nat.sub_add_cancel hn,hp,Nat.cast_choose ℝ hkn,hnf]
  unfold primitivePlanarWeight
  field_simp [hV,hP]
end WP.RandomGeometry
