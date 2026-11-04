import WPFormalization.Statements
import WPBlueprint.Chapters.C09
import Verso
import VersoManual
import VersoBlueprint

open Verso.Genre Verso.Genre.Manual Informal

#doc (Manual) "11-absolute" =>

# Absolute volumes at every cusp count

We now assemble the preceding estimates to prove Theorem {bpref "thm:intro-absolute"}[1.1]. The extraction theorem, Theorem {bpref "thm:sharp-extraction"}[10.1], gives the explicit leading term with relative error $`O(g^{-1})`, and also the quantitative volume ratios. The expansion of Theorem {bpref "thm:canonical-expansion"}[10.2] then gives all higher corrections and their uniform remainder. We treat positive cusp counts first and recover $`n=0` from the exact dilaton relation.

For $`g\ge2` and $`n\ge1`, set $`h=2g-1`, $`k=n-1`, and choose $`x=X(Y)` by $`h\Psi(x)=k`. At $`k=0` take $`x=Y=0`. Define 

$$`\begin{aligned}
 \widehat V_{g,n}&=
 (2\pi^2)^{3g-3+n}\frac{\mathcal J_{g,1}(Y)}{\pi}
 \left(\frac{k}{\mathrm{e} x}\right)^k
 \sqrt{\frac{k}{h\mathscr D\Psi(x)}}\quad(n\ge1),\\
 \widehat V_{g,0}&=
 \frac{\Gamma(2g-2)(4\pi^2)^{2g-3}}{\sqrt{\pi g}}.
 \end{aligned}`

 At $`k=0`, both $`k`-dependent factors on the first line are defined by their limits, which are one. All functions in this formula were defined in 6.22, {bpref "eq:PF1"}[7.1], and {bpref "eq:PF3"}[7.3]. Since $`r=2\Delta`, $`Aar=I/\sqrt\Delta` by 6.22, and $`\Theta=-1/\bar K_Y'(1)=-a/(r\,\partial_zK_Y(r))` by {bpref "eq:PF1"}[7.1], one has $`r^{1/2}\sqrt{A\Theta}=\varpi(Y)` and $`\mathcal Z=\sqrt2\,I`, with $`\varpi` as in the introduction. Hence 11.1 is the formula {bpref "eq:intro-leading"}[1.5], with $`\mathscr D\Psi(x)=x\Psi'(x)`.

:::theorem "thm:absolute" (parent := "paper_core") (tags := "paper-new") (priority := "high") (uses := "eq:intro-leading")
%%%
source := { document := "paper-v3", spans := #[{ page := "48", anchor := "thm:absolute", citation := "Theorem 11.1", pdf := some { path := "source/paper.pdf" } }] }
%%%

Theorem 11.1 — The leading term.

There is a constant $`C>0` such that, for all sufficiently large $`g`, 

$$`\sup_{n\ge0}\left|\frac{V_{g,n}}{\widehat V_{g,n}}-1\right|
       \le\frac Cg.`

 The order $`g^{-1}` is sharp for the leading model 11.1: 

$$`\liminf_{g\to\infty}g\sup_{n\ge0}
       \left|\frac{V_{g,n}}{\widehat V_{g,n}}-1\right|
       \ge\frac7{12}-\frac{17}{6\pi^2}>0.`



Lean scope (stage one): these declarations use the explicit mathematical interfaces shown in their Lean types. Their proof status and registered external dependencies are recorded in the compiled phase-one audit. Concrete DM/WP and other classical instances remain unconstructed; no unconditional geometric verification is asserted.

:::



:::proof "thm:absolute" (uses := "thm:sharp-extraction, cor:constant, ext:fixed-cusps")
For $`n\ge1`, apply Theorem {bpref "thm:sharp-extraction"}[10.1] with $`p=1`. The coefficient identity 9.17 gives 

$$`V_{g,n}=(2\pi^2)^{3g-3+n}(n-1)!x^{-k}
     \frac{\mathcal J_{g,1}(Y)}\pi\,
       \mathfrak p_k\sqrt{\frac{k}{h\mathscr D\Psi(x)}}
       (1+O(g^{-1})),`

 uniformly, including $`k=0` by continuity. Since $`k!\mathfrak p_k=(k/\mathrm{e})^k`, this is precisely the first line of 11.1 with uniform relative error $`O(g^{-1})`. For $`n=0`, the constant was independently identified in Section 7. The fixed-cusp expansion of Mirzakhani–Zograf \[66\] Theorem 1.2 and Remark 1.3 yields 

$$`\frac{V_{g,0}}{\widehat V_{g,0}}
 =1+\frac1g\left(\frac7{12}-\frac{17}{6\pi^2}\right)+O(g^{-2}).`

 This closes 11.2 and proves 11.3. The latter concerns the uncorrected model chosen here, rather than an obstruction to adding further asymptotic corrections.
:::



The model 11.1 is explicit and contains no unknown constant. Its action $`I(Y)` and the spectral-edge parameter $`Y` have the matrix-model interpretation recalled in Subsection 15.1; what is proved here is the uniform relative comparison with the true volumes. The normalization is fixed at the pure-$`\psi` endpoint (Section 7); the fixed-cusp expansion of \[66\] enters only afterwards, for $`n=0` in the proof above.

## An inverse-genus error for the volume ratios

The sharper extraction estimate also gives a uniform rate in the volume-ratio theorem. The two genus-exchange generating functions have the same saddle. Adding a cusp changes the complexity by one; the following argument controls the resulting saddle displacement even near the endpoints.

Proof discussion. For $`n\ge1` put $`h=2g-1`, $`k=n-1`, and $`h\Psi(x)=k`. Apply Theorem {bpref "thm:sharp-extraction"}[10.1] at $`(g,p)=(g,1)` and $`(g-1,3)`. Their Poisson and variance factors cancel exactly, and {bpref "eq:PF3"}[7.3] gives $`\mathcal J_{g-1,3}/\mathcal J_{g,1}=4r`. Consequently 9.17 yields 

$$`B_{g,n}=\mathcal B(2k/h)(1+O(h^{-1})).`



For the cusp ratio assume first that $`k\ge1`, and let $`x'` satisfy $`(h+1)\Psi(x')=k`. Write $`q=\log x`, $`q'=\log x'` and $`v=\mathscr D\Psi`. The convergent endpoint expansions give 

$$`\sup_{0<x<x_c}\left\{
 \frac{\Psi(x)^2}{v(x)}+
 \left|\frac{\Psi(x)}{v(x)}\mathscr D\log v(x)\right|
 +|\beta_2(x)|\right\}<\infty.`

 Indeed, near zero $`\Psi\sim v\sim2x`; near criticality $`\Psi\sim5/(4\varepsilon)` and $`v\sim5/(4\varepsilon^2)`. The function $`\beta_2` is bounded by 7.7. Since $`\Psi(x')/\Psi(x)=h/(h+1)`, integration with respect to $`\log\Psi` shows that 

$$`\frac{v(x')}{v(x)}=1+O(h^{-1}),\qquad
 |q'-q|\le\frac{C\Psi(x)}{h v(x)}.`

 For $`L(q)=\log\mathcal J_{g,2}(\mathrm{e}^q)-kq`, the exact model identities give 

$$`L'(q)=(h+1)\Psi(\mathrm{e}^q)-k+\beta_2(\mathrm{e}^q)\Psi(\mathrm{e}^q).`

 On $`[q',q]` its absolute value is at most $`C\Psi(x)`, so $`|L(q')-L(q)|\le C\Psi(x)^2/(hv(x))=O(h^{-1})`. Thus the saddle displacement and the variance factor in 10.2 each change the coefficient ratio by $`1+O(h^{-1})`. At the common point $`x`, {bpref "eq:PF3"}[7.3] gives exactly 

$$`\frac{\mathcal J_{g,2}(x)}{\mathcal J_{g,1}(x)}
 =\frac{h}{Aar}\sqrt{\frac{h}{h+1}}.`

 Using the coefficient normalization in 9.20, we obtain 

$$`C_{g,n}=\frac{h}{2g}\mathcal C(2k/h)(1+O(h^{-1})).`

 At $`k=0` both saddles are zero. The conventions in Theorem {bpref "thm:sharp-extraction"}[10.1] give the same two ratio formulas directly, without logarithmic coordinates.

The positive profiles are analytic at zero, and their expansions at infinity in 3.2–3.4 are convergent in the inverse square root of the density. Hence 

$$`\sup_{\lambda\ge0}(1+\lambda)
 \bigl(|(\log\mathcal B)'(\lambda)|+
       |(\log\mathcal C)'(\lambda)|\bigr)<\infty.`

 For $`\lambda_*=2(n-1)/(2g-1)` and $`\lambda=n/g`, $`|\lambda_* -\lambda|/(1+\min(\lambda_*,\lambda))=O(g^{-1})` uniformly in $`n\ge1`. Integrating the preceding bound replaces $`\lambda_*` by $`\lambda` with relative error $`O(g^{-1})`. For $`n=0`, the fixed-cusp expansion of \[66\] at the finitely many cusp counts $`0,1,2` gives the required rate directly. Finally $`D_{g,n}=C_{g,n-1}/C_{g,n}` and the same logarithmic derivative bound prove $`\sup_{n\ge1}|D_{g,n}-1|=O(g^{-1})`.



## Proof of Theorem {bpref "thm:intro-absolute"}[1.1]

For $`n\ge1` the expansion is obtained by applying the extraction theorem, Theorem {bpref "thm:canonical-expansion"}[10.2], with $`p=1`, keeping the same leading term. The unmarked case $`n=0` is recovered from $`n=1` by the exact dilaton relation, so its higher coefficients need no separate asymptotic normalization. For $`h=2g-1`, the scalar $`\mathsf C_0` of {bpref "eq:FE1"}[C.13] obeys

:::proposition "eq:AV6" (parent := "paper_core") (tags := "paper-new") (priority := "high") (uses := "eq:intro-leading")
%%%
source := { document := "paper-v3", spans := #[{ page := "50", anchor := "eq:AV6", citation := "Equation 11.6", pdf := some { path := "source/paper.pdf" } }] }
%%%

Proposition 11.6 — Exact unmarked dilaton reduction.

In the setup and notation of this section, the paper defines or asserts:



$$`V_{g,0}=\frac{V_{g,1}\mathsf C_0(h-1;0)}{4\pi^2(h-1)},\qquad
 \frac{\widehat V_{g,1}}{4\pi^2(h-1)\widehat V_{g,0}}
       =\sqrt{1+\frac1h}.`



Lean scope (stage one): these declarations use the explicit mathematical interfaces shown in their Lean types. Their proof status and registered external dependencies are recorded in the compiled phase-one audit. Concrete DM/WP and other classical instances remain unconstructed; no unconditional geometric verification is asserted.

:::



Indeed {bpref "eq:TL12"}[6.4] holds at $`p=0`; at $`Y=0`, undo its normalizations with $`r=\pi^2/2`, $`A=1/\pi^2`. The scalar expansion of $`\mathsf C_0` follows directly from the last line of C.17, using the proved one-marking profile and its summable remainder. This step does not require an unmarked harmonic comparison. The second identity follows from 11.1 exactly.

The coefficients in Theorem {bpref "thm:intro-absolute"}[1.1] are defined as follows. For $`n=0`, define constants $`a_{0,j}` by the finite-order formal rule

:::definition "eq:AV7" (parent := "paper_definitions") (tags := "paper-definition") (priority := "high") (uses := "eq:CG3, eq:FE1")
%%%
source := { document := "paper-v3", spans := #[{ page := "50", anchor := "eq:AV7", citation := "Equation 11.7", pdf := some { path := "source/paper.pdf" } }] }
%%%

Definition 11.7 — Unmarked correction coefficients.

In the setup and notation of this section, the paper defines or asserts:



$$`1+\sum_{j\ge1}a_{0,j}t^j
 =(1+t)^{1/2}\mathsf C_0\!\left(\frac t{1-t};0\right)
       \left(1+\sum_{j\ge1}\mathcal L_{1,j}(0)t^j\right).`


:::



Here the second argument denotes $`Y=0`, and $`t=1/h`; thus the cusp scalar uses complexity $`h-1`. Put $`A_j(g,0)=a_{0,j}`, and, for $`n\ge1`, put $`A_j(g,n)=\mathcal A_{1,j}(Y_{g,n})` with the coefficients {bpref "eq:CG3"}[10.5] of Theorem {bpref "thm:canonical-expansion"}[10.2], where $`(2g-1)\Psi(X(Y_{g,n}))=n-1`.

:::proof "thm:intro-absolute" (uses := "thm:canonical-expansion, eq:AV6, prop:hierarchy")
For $`n\ge1`, take $`p=1,k=n-1` in Theorem {bpref "thm:canonical-expansion"}[10.2]. The coefficient identity 9.17 and $`k!\mathfrak p_k=(k/\mathrm{e})^k` identify $`[z^k]\Phi_g^{(1)}/\mathcal Q_{g,1,k}` with $`V_{g,n}/\widehat V_{g,n}`, including $`k=0`. For $`n=0`, the dilaton scalar in {bpref "eq:AV6"}[11.6] has a one-marking child of complexity $`h`, so exactly 

$$`\mathsf C_0(h-1;0)=\frac1{A(0)}
       \sum_{d\ge1}b_d(0)c_{g,1}(d;0).`

 Apply C.19 at this child with $`L=K+1`. Choose its fixed $`M` large enough for the absolute exponential $`b_d` moment. With $`S=1+ML`, 

$$`\sum_d\frac{|b_d(0)|}{A(0)}(S+d)^{2L}
 \le S^{2L}\sum_d\frac{|b_d(0)|}{A(0)}\mathrm{e}^{2d/M}
 \le C D^L(L!)^2.`

 This gives a Gevrey-2 remainder for the whole scalar sum, including invalid degrees. Its coefficient series is precisely $`\mathsf C_0(t/(1-t);0)`: the child substitution in C.17 becomes $`(t/(1-t))/(1+t/(1-t))=t`.

The other two exact factors in {bpref "eq:AV6"}[11.6] are $`\sqrt{1+1/h}`, with a convergent expansion, and the $`n=1` ratio, with the marked estimate at zero. All three exact factors are bounded. The finite-product identity used in Proposition {bpref "prop:hierarchy"}[C.3] contains one remainder per term; its factorial weights obey $`(j!)^2((L-j)!)^2\le(L!)^2`. Applied twice, it gives the same bound for their product and exactly the coefficients in {bpref "eq:AV7"}[11.7]. Take common constants with the $`n\ge1` case. The coefficient bound $`|A_j(g,n)|\le CB^j(j!)^2` follows from those of Theorem {bpref "thm:canonical-expansion"}[10.2] and Proposition {bpref "prop:hierarchy"}[C.3]. Finally, for $`K=\lfloor c'\sqrt{2g-1}\rfloor` with $`c'\le c` chosen after the final base $`B` so that $`B(c')^2<1`, the inequality $`B^L(L!)^2h^{-L}\le(BL^2/h)^L` gives the exponentially small error.
:::



In particular, the explicit first correction {bpref "eq:CG12"}[D.24] gives a relative error $`O(g^{-2})` uniformly over all cusp counts. At the unmarked endpoint $`a_{0,1}=7/6-17/(3\pi^2)`, consistently with 11.5 after $`h=2g-1`. The fixed-cusp existence of an all-order expansion is the theorem of Mirzakhani–Zograf \[66\]; here the coefficients and remainders remain controlled as the cusp count crosses every density scale.
