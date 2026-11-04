import WPFormalization.Statements
import WPBlueprint.Chapters.C12
import Verso
import VersoManual
import VersoBlueprint

open Verso.Genre Verso.Genre.Manual Informal

#doc (Manual) "13b-instanton" =>

# Relation to the instanton prediction

:::lemma_ "eq:instanton-correspondence" (parent := "paper_core") (tags := "paper-new") (priority := "high") (uses := "eq:P1, eq:C1")
%%%
source := { document := "paper-v3", spans := #[{ page := "56", anchor := "subsec:instanton-model", citation := "Section 13.7 exact action, residue normalization and stationary equation", pdf := some { path := "source/paper.pdf" } }, { page := "57", anchor := "subsec:instanton-model", citation := "Section 13.7 exact action, residue normalization and stationary equation", pdf := some { path := "source/paper.pdf" } }] }
%%%

R35 implementation: the complete mathematical deduction has a Lean producer linked below. The physical interpretation cited here is background; the local identities and remainder estimates are proved from the defined mathematical functions, without a new physical-model assumption.

The denominator $`H` in 13.4 is the normalized ordinary Weil–Petersson instanton action. To see the correspondence, choose the positive sign convention 

$$`A_{\rm inst}(w)=\frac{\sin(2\pi w)-2\pi w\cos(2\pi w)}{4\pi^3}
     =\frac23 w^3 H(2\pi^2w^2).`

 With $`x=w^2`, this is the effective potential of \[25\] equation (3.15), whose values at its stationary points are the instanton actions. The ordinary-volume polynomial prediction in \[28\] Section 3.3 and the one-boundary term in \[45\] equation (4.22) contain, up to an overall factor independent of the coefficient degree, the contour expression 

$$`\frac{\Gamma(h)}{L}\oint
       \frac{\mathrm{e}^{Lw}}{w A_{\rm inst}(w)^h}\,\mathrm{d}w,\qquad h=2g-1.`

 The coefficient of $`L^{2k}`, multiplied by $`(2k+1)!`, is proportional to 

$$`\Gamma(h)\operatorname*{Res}_{w=0} w^{2k}A_{\rm inst}(w)^{-h}\,\mathrm{d}w.`

 Since $`3h-2k-1=2m`, expansion at zero gives the exact identity 

$$`\Gamma(h)\operatorname*{Res}_{w=0} w^{2k}A_{\rm inst}(w)^{-h}\,\mathrm{d}w
 =\Gamma(h)(3/2)^h(2\pi^2)^m \widetilde A_m(h)
 =2\,4^{-k}M_{g,k}.`

 Thus the model for the coefficients $`a_{g,k}` has precisely the normalization $`4^{-k}M_{g,k}`, up to the degree-independent overall factor in the prediction. Moreover, the exponent in the $`\mathrm{d}w/w` representation has its stationary point at 

$$`\frac{2k+1}{h}=\frac{wA_{\rm inst}'(w)}{A_{\rm inst}(w)}
 =\frac{t^2\sin t}{\sin t-t\cos t},\qquad t=2\pi w.`

 Thus both the comparison model and the saddle equation already appear in the instanton calculus. The estimates 13.5 and the concavity argument above justify the asymptotic formula for adjacent ratios of the true mixed intersection numbers, including both endpoint regimes; that proof does not use the contour expression.


:::
