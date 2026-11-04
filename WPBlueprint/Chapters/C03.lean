import WPFormalization.Statements
import WPBlueprint.Chapters.C02
import Verso
import VersoManual
import VersoBlueprint

open Verso.Genre Verso.Genre.Manual Informal

#doc (Manual) "04-amplitudes" =>

# Intersection amplitudes and the comparison model

We deform the Weil–Petersson intersection brackets into pure $`\psi` intersection numbers and derive a positive recursion along the deformation. We call the resulting functions shifted amplitudes. The harmonic model introduced below is an explicit, solvable comparison for this recursion. Section 5 compares the full recursion with that model, uniformly in the degrees and in the deformation parameter. This comparison is the common starting point for the volume and coefficient asymptotics.

## Intersection identities and normalization

We use the following notation for a stable pair $`(g,n)` and a degree tuple $`\mathbf d`: $`h` is the complexity, $`N` the dimension of $`\overline{\mathcal M}_{g,n}`, and the deficit $`m` is the number of $`\kappa_1` factors needed to fill up the dimension. Write 

$$`h=2g-2+n,\qquad N=3g-3+n,\qquad
D=\sum_{i=1}^n d_i,\qquad m=N-D.`

 Throughout the comparison theorem $`n\ge1`, the pair is stable, and $`0\le D\le N`. A tuple with a negative degree or an unstable pair has amplitude zero.

Recall $`X`, $`a=X'>0` on $`[0,y_0)` and the kernels $`K_Y` and $`H_Y` of {bpref "eq:P1"}[2.1], and write $`r_Y=r(Y)` for the first positive zero of $`K_Y`. The properties of these kernels used below were established in Section 2. Put

:::definition "eq:H2" (parent := "paper_definitions") (tags := "paper-definition") (priority := "high") (uses := "eq:P9")
%%%
source := { document := "paper-v3", spans := #[{ page := "19", anchor := "eq:H2", citation := "Equation 4.1", pdf := some { path := "source/paper.pdf" } }] }
%%%

Definition 4.1 — Normalized kernels and recursion coefficients.

In the setup and notation of this section, the paper defines or asserts:



$$`\bar H_Y(z)=\frac{H_Y(r_Yz)}a,\qquad
\bar K_Y(z)=\frac{K_Y(r_Yz)}a
      =\bar H_Y(z)+\frac23z\bar H_Y'(z),\qquad
\theta_\ell(Y)=[z^\ell]\bar K_Y(z)^{-1}.`


:::



At $`Y=y_0` these have the continuous definitions

:::definition "eq:H3" (parent := "paper_definitions") (tags := "paper-definition") (priority := "high") (uses := "eq:P9")
%%%
source := { document := "paper-v3", spans := #[{ page := "19", anchor := "eq:H3", citation := "Equation 4.2", pdf := some { path := "source/paper.pdf" } }] }
%%%

Definition 4.2 — Critical normalized kernels.

In the setup and notation of this section, the paper defines or asserts:



$$`\bar H_{y_0}(z)=1-\frac35z,\qquad \bar K_{y_0}(z)=1-z,\qquad
\theta_\ell(y_0)=1.`


:::



In particular $`\theta_0=1`. These are the rescaled kernels and coefficients of {bpref "eq:P9"}[2.5] and {bpref "eq:P11"}[2.7], recalled here together with their endpoint values.

We use the following facts from intersection theory. The ordinary string, dilaton, and Dijkgraaf–Verlinde–Verlinde (DVV) identities hold for Witten’s psi intersections \[81\]; \[51\]; \[21\], with $`\langle\tau_0^3\rangle_0=1` and $`\langle\tau_1\rangle_1=1/24`. The normalized forms used here are written in Appendix B. For pure $`\psi` intersection numbers we use the normalization

:::definition "eq:H4" (parent := "paper_definitions") (tags := "paper-definition") (priority := "high") (uses := "def:intersections")
%%%
source := { document := "paper-v3", spans := #[{ page := "19", anchor := "eq:H4", citation := "Equation 4.3", pdf := some { path := "source/paper.pdf" } }] }
%%%

Definition 4.3 — Pure psi normalization.

In the setup and notation of this section, the paper defines or asserts:



$$`C_g(\mathbf e)=
\frac{4^g\prod_i(2e_i+1)!!}
 {3^{\,2g-2+q}\Gamma(2g-2+q)}
\left\langle\prod_{i=1}^q\tau_{e_i}\right\rangle_g,
\qquad \sum_i e_i=3g-3+q.`



Lean scope (stage one): these declarations use the explicit mathematical interfaces shown in their Lean types. Their proof status and registered external dependencies are recorded in the compiled phase-one audit. Concrete DM/WP and other classical instances remain unconstructed; no unconditional geometric verification is asserted.

:::



For positive degrees we use only 

$$`\frac16\le C_g(\mathbf e)\le1.`

 Appendix B proves these coarse bounds directly from DVV and the published two-point estimate. The argument adapts the recursion estimates of Guo, Yang and Zagier \[32\]; their stronger lower bound $`C_g(3g-2)\le C_g(\mathbf e)` is not needed here.

With $`m=3g-3+n-|\mathbf d|`, our mixed brackets are 

$$`[\tau_{d_1}\cdots\tau_{d_n}]_{g,n}
 =\prod_i(2d_i+1)!!\,4^{|\mathbf d|}\frac{(2\pi^2)^m}{m!}
 \int_{\overline{\mathcal M}_{g,n}}\kappa_1^m\prod_i\psi_i^{d_i}.`

 Here $`\kappa_1` is the logarithmic Mumford class, $`\psi_i` is the cotangent class, and $`[\omega_{\mathrm{WP}}]=2\pi^2\kappa_1` \[83\]; see also \[66\] Section 2. Thus 

$$`V_{g,n}(2\mathbf L)=\sum_{|\mathbf d|\le3g-3+n}
 [\tau_{d_1}\cdots\tau_{d_n}]_{g,n}
 \prod_i\frac{L_i^{2d_i}}{(2d_i+1)!}.`

 Angle brackets below denote unweighted pure-$`\psi` integrals. Intersections of the wrong dimension and negative-degree amplitudes are zero. Unstable factors in the positive recursion are zero; explicitly specified genus-zero initial derivatives are kept separate.

The mixed-kappa/psi transform \[48\]; \[55\] gives, at $`Y=0`,

:::proposition "eq:H5" (parent := "paper_core") (tags := "paper-new") (priority := "high") (uses := "def:intersections")
%%%
source := { document := "paper-v3", spans := #[{ page := "20", anchor := "eq:H5", citation := "Equation 4.4", pdf := some { path := "source/paper.pdf" } }] }
%%%

Proposition 4.4 — Mixed kappa to psi transform.

In the setup and notation of this section, the paper defines or asserts:



$$`\frac{[\tau_{d_1}\cdots\tau_{d_n}]_{g,n}}
 {4^D(2\pi^2)^m}
=\prod_i(2d_i+1)!!
\sum_{\substack{\ell_k\ge0,\ k\ge2\\
                 \sum_{k\ge2}(k-1)\ell_k=m}}
\left\langle\tau_{\mathbf d}\prod_{k\ge2}\tau_k^{\ell_k}\right\rangle_g
\prod_{k\ge2}\frac{((-1)^k/(k-1)!)^{\ell_k}}{\ell_k!}.`



Lean scope (stage one): these declarations use the explicit mathematical interfaces shown in their Lean types. Their proof status and registered external dependencies are recorded in the compiled phase-one audit. Concrete DM/WP and other classical instances remain unconstructed; no unconditional geometric verification is asserted.

:::



Since $`X'(0)=1` and $`-X^{(k)}(0)=(-1)^k/(k-1)!`, the weights in {bpref "eq:H5"}[4.4] are the derivatives $`-X^{(k)}(0)`, $`k\ge2`. The shifted amplitudes replace them by the derivatives $`-X^{(k)}(Y)` at a point $`Y`. For general $`Y<y_0`, define the shifted amplitudes by the finite sum

:::definition "eq:H6" (parent := "paper_definitions") (tags := "paper-definition") (priority := "high") (uses := "def:intersections, eq:P1")
%%%
source := { document := "paper-v3", spans := #[{ page := "20", anchor := "eq:H6", citation := "Equation 4.5", pdf := some { path := "source/paper.pdf" } }] }
%%%

Definition 4.5 — Shifted amplitudes.

In the setup and notation of this section, the paper defines or asserts:



$$`U^Y_{g,n}(\mathbf d)=\prod_i(2d_i+1)!!
\sum_{\substack{\ell_k\ge0,\ k\ge2\\
                 \sum(k-1)\ell_k=m}}
\left\langle\tau_{\mathbf d}\prod_{k\ge2}\tau_k^{\ell_k}\right\rangle_g
\frac{\prod_{k\ge2}(-X^{(k)}(Y))^{\ell_k}/\ell_k!}
 {a^{h+\sum\ell_k}}.`



Lean scope (stage one): these declarations use the explicit mathematical interfaces shown in their Lean types. Their proof status and registered external dependencies are recorded in the compiled phase-one audit. Concrete DM/WP and other classical instances remain unconstructed; no unconditional geometric verification is asserted.

:::



The denominator is obtained by summing degree-one background insertions with time $`t_1=1-a`: the dilaton equation gives the factor $`\sum_{j\ge0}(h+\sum\ell_k)_j t_1^j/j!=a^{-h-\sum\ell_k}`. Define the normalized amplitudes

:::definition "eq:H7" (parent := "paper_definitions") (tags := "paper-definition") (priority := "high") (uses := "eq:H6, eq:H2")
%%%
source := { document := "paper-v3", spans := #[{ page := "20", anchor := "eq:H7", citation := "Equation 4.6", pdf := some { path := "source/paper.pdf" } }] }
%%%

Definition 4.6 — Normalized shifted amplitudes.

In the setup and notation of this section, the paper defines or asserts:



$$`\mathcal U_{g,n}(\mathbf d;Y)=a^h r_Y^m U^Y_{g,n}(\mathbf d).`



Lean scope (stage one): these declarations use the explicit mathematical interfaces shown in their Lean types. Their proof status and registered external dependencies are recorded in the compiled phase-one audit. Concrete DM/WP and other classical instances remain unconstructed; no unconditional geometric verification is asserted.

:::



They extend to $`Y=y_0` through their positive recursion below.

When all degrees vanish, the shifted amplitudes are derivatives of the cusp generating function. This is the familiar shift of the Kontsevich–Witten (KW) times along the string flow \[43\]; \[48\]; the identification of $`\Phi_g` with the KW free energy at the shifted times $`t_0=x`, $`t_1=0`, $`t_k=(-1)^k/(k-1)!` is recorded in \[90\] Remark 1, where it is attributed to Dubrovin, and the corresponding deformation in $`(t_0,t_1)` is used in \[71\] Section 2.4. We recall it in the present normalization. Start with KW times $`t_0=x,\ t_1=0,\ t_k=-X^{(k)}(0)`, $`k\ge2`. The finite formal string flow sends them to 

$$`t_0'=x-X(Y),\qquad t_1'=1-X'(Y),\qquad
t_k'=-X^{(k)}(Y)\quad(k\ge2).`

 Its vector field is $`\sum_{k\ge0}t_{k+1}'\partial_{t_k'}-\partial_{t_0'}`. The string equation makes the genus-$`g` free energy invariant for $`g\ge1`; its genus-zero anomaly disappears after three $`t_0` derivatives. Since $`\partial_{t_0}` commutes with this flow, setting $`x=X(Y)` gives

:::proposition "eq:H8" (parent := "paper_core") (tags := "paper-new") (priority := "high") (uses := "eq:H6, eq:intro-Phi")
%%%
source := { document := "paper-v3", spans := #[{ page := "20", anchor := "eq:H8", citation := "Equation 4.7", pdf := some { path := "source/paper.pdf" } }] }
%%%

Proposition 4.7 — String-flow identification with geometric volumes.

In the setup and notation of this section, the paper defines or asserts:



$$`U^Y_{g,n}(0^n)=\Phi_g^{(n)}(x),\qquad
\Phi_g(x)=\sum_{n\ge0}\frac{V_{g,n}}{(2\pi^2)^{3g-3+n}}\frac{x^n}{n!},`



Lean scope (stage one): these declarations use the explicit mathematical interfaces shown in their Lean types. Their proof status and registered external dependencies are recorded in the compiled phase-one audit. Concrete DM/WP and other classical instances remain unconstructed; no unconditional geometric verification is asserted.

:::



whenever the amplitude is stable. Unmarked $`\Phi_g` is used only for $`g\ge2`. The unstable genus-zero derivatives are separate initial terms and are not substituted into the positive recursion.

## The positive recursion

We single out the first marking and call it the pivot. Write $`\langle\!\langle\tau_{d_1}\cdots\tau_{d_q}\rangle\!\rangle_g
=\prod_i(2d_i+1)!!\,\langle\tau_{d_1}\cdots\tau_{d_q}\rangle_g`. In this normalization the Dijkgraaf–Verlinde–Verlinde equation for the pivot reads, with $`(-1)!!=1`, 

$$`\begin{aligned}
\langle\!\langle\tau_{d_1}\tau_{d_2}\cdots\tau_{d_q}\rangle\!\rangle_g
={}&\sum_{j=2}^q(2d_j+1)\,
 \langle\!\langle\tau_{d_1+d_j-1}\textstyle\prod_{i\ne1,j}\tau_{d_i}\rangle\!\rangle_g
 +\frac12\sum_{u+v=d_1-2}
 \langle\!\langle\tau_u\tau_v\tau_{d_2}\cdots\tau_{d_q}\rangle\!\rangle_{g-1}\\
&+\frac12\sum_{u+v=d_1-2}\ \sum_{\substack{g_1+g_2=g\\ I\sqcup J=\{2,\ldots,q\}}}
 \langle\!\langle\tau_u\tau_I\rangle\!\rangle_{g_1}
 \langle\!\langle\tau_v\tau_J\rangle\!\rangle_{g_2}.
\end{aligned}`

 For $`d_1=0` and $`d_1=1` this is the string and the dilaton equation. In the amplitudes {bpref "eq:H6"}[4.5], besides the $`n` external markings, the intersection numbers contain background insertions: $`\tau_k` with weight $`t_k=-X^{(k)}(Y)` for $`k\ge2`, and, after the dilaton sum that produced the factor $`a^{-h-\sum\ell_k}`, also $`\tau_1` with weight $`t_1=1-a`. Apply the displayed equation with the pivot $`\tau_{d_1}` and sum over the background. Three kinds of terms appear.

1. The pivot merges with an external marking $`j\ge2`. By the first term above, this gives $`(2d_j+1)\,U^Y_{g,n-1}(d_1+d_j-1,\ldots)`, with the background unchanged.

2. The pivot merges with a background insertion $`\tau_k`, $`k\ge1`. Background insertions carry no double factorial, so the factor $`2k+1` of the first term is divided by $`(2k+1)!!` and becomes $`1/(2k-1)!!`. Choosing which of the $`\ell_k` copies is used turns $`t_k^{\ell_k}/\ell_k!` into $`t_k\cdot t_k^{\ell_k-1}/(\ell_k-1)!`. The result is 
   $$`\frac{t_k}{(2k-1)!!}\,U^Y_{g,n}(d_1+k-1,d_2,\ldots,d_n).`
   

3. Contractions. The two remaining terms give the nonseparating and separating contributions with coefficient $`1/2`. In the separating case the background splits between the two components with the binomial factors of exponential generating functions, so the term is a product of two amplitudes.

Let $`E` be the operator raising the pivot degree by one. The terms of type (b) form $`(1-a)U^Y+\sum_{k\ge2}t_kE^{k-1}U^Y/(2k-1)!!`. Moving them to the left-hand side and recalling $`t_k=-X^{(k)}(Y)` gives 

$$`\left(a+\sum_{k\ge2}\frac{X^{(k)}(Y)}{(2k-1)!!}E^{k-1}\right)U^Y
=K_Y(E)\,U^Y=\bigl(\text{terms of types (a) and (c)}\bigr),`

 where we compared with the series {bpref "eq:P1"}[2.1] for $`K_Y`. For a fixed parent, raising the pivot degree more than $`m` times leaves the dimension range, so $`E^{m+1}U^Y=0` and $`K_Y(E)` has the finite inverse $`\sum_{\ell\le m}[z^\ell]K_Y(z)^{-1}E^\ell`. This is how the Taylor coefficients of $`1/K_Y` enter. Components of the wrong dimension vanish, and for external complexity $`h\ge2` no exceptional initial tuple occurs.

After {bpref "eq:H7"}[4.6], the exact recursion is

:::proposition "eq:H9" (parent := "paper_core") (tags := "paper-new") (priority := "high") (uses := "eq:H7, eq:H3")
%%%
source := { document := "paper-v3", spans := #[{ page := "21", anchor := "eq:H9", citation := "Equation 4.8", pdf := some { path := "source/paper.pdf" } }] }
%%%

Proposition 4.8 — Exact positive geometric recursion.

In the setup and notation of this section, the paper defines or asserts:



$$`\begin{aligned}
\mathcal U_{g,n}(\mathbf d)={}&
\sum_{j=2}^n(2d_j+1)\sum_{\ell=0}^m\theta_\ell
 \mathcal U_{g,n-1}(d_1+d_j+\ell-1,\mathbf d_{\widehat{1,j}})\\
&+\frac12\sum_{\ell=0}^m\theta_\ell
 \sum_{u+v=d_1+\ell-2}
 \mathcal U_{g-1,n+1}(u,v,\mathbf d_{\widehat1})\\
&+\frac12\sum_{\ell=0}^m\theta_\ell
 \sum_{u+v=d_1+\ell-2}
 \sum_{\substack{g_1+g_2=g\\I\sqcup J=\{2,\ldots,n\}}}
 \mathcal U_{g_1,|I|+1}(u,\mathbf d_I)
 \mathcal U_{g_2,|J|+1}(v,\mathbf d_J).
\end{aligned}`



Lean scope (stage one): these declarations use the explicit mathematical interfaces shown in their Lean types. Their proof status and registered external dependencies are recorded in the compiled phase-one audit. Concrete DM/WP and other classical instances remain unconstructed; no unconditional geometric verification is asserted.

:::



Here $`\mathbf d_{\widehat{1,j}}` denotes the tuple $`\mathbf d` with the entries $`d_1` and $`d_j` removed, and $`\mathbf d_{\widehat1}` the tuple with $`d_1` removed. The indices $`u` and $`v` are the degrees at the two new markings corresponding to the branches of the node. The last split is ordered. We call the amplitudes on the right of {bpref "eq:H9"}[4.8] the children of the amplitude on the left: a merging or nonseparating child has complexity $`h-1`, and the two factors of a separating term have complexities summing to $`h-1`. Its initial values, computed directly from {bpref "eq:H6"}[4.5], are

:::proposition "eq:H10" (parent := "paper_core") (tags := "paper-new") (priority := "high") (uses := "eq:H7")
%%%
source := { document := "paper-v3", spans := #[{ page := "22", anchor := "eq:H10", citation := "Equation 4.9", pdf := some { path := "source/paper.pdf" } }] }
%%%

Proposition 4.9 — Initial amplitudes.

In the setup and notation of this section, the paper defines or asserts:



$$`\mathcal U_{0,3}(0,0,0)=1,\qquad
\mathcal U_{1,1}(1)=\frac18,\qquad
\mathcal U_{1,1}(0)=\frac{\theta_1}{8}.`



Lean scope (stage one): these declarations use the explicit mathematical interfaces shown in their Lean types. Their proof status and registered external dependencies are recorded in the compiled phase-one audit. Concrete DM/WP and other classical instances remain unconstructed; no unconditional geometric verification is asserted.

:::



Equations {bpref "eq:H9"}[4.8]–{bpref "eq:H10"}[4.9], with negative degrees and unstable factors set to zero, determine all amplitudes by increasing $`h`.

By {bpref "eq:P11"}[2.7], 

$$`1=\theta_0\le\theta_1\le\cdots\le C_\theta`

 uniformly in $`Y\in[0,y_0]`. Thus every term of {bpref "eq:H9"}[4.8] is nonnegative, and the continuous endpoint {bpref "eq:H3"}[4.2] defines a positive limiting theory.

## The harmonic model

We now introduce the explicit model with which the amplitudes will be compared. It depends on the degrees only through the deficit $`m`, and it is chosen so that the linear part of {bpref "eq:H9"}[4.8] reproduces it exactly on average; this is the mass identity {bpref "eq:H13"}[4.12] below, and the reason for the name: the model is harmonic for the linear part of the recursion. At the endpoint $`Y=y_0` the model is the denominator in the normalization {bpref "eq:H4"}[4.3] of pure $`\psi` intersection numbers (see {bpref "eq:PF13"}[7.14]), so the comparison theorem extends the coarse bounds on pure $`\psi` intersections to the whole parameter interval.

Suppress $`Y` temporarily and put

:::definition "eq:H12" (parent := "paper_definitions") (tags := "paper-definition") (priority := "high") (uses := "eq:H7, eq:P9")
%%%
source := { document := "paper-v3", spans := #[{ page := "22", anchor := "eq:H12", citation := "Equation 4.11", pdf := some { path := "source/paper.pdf" } }] }
%%%

Definition 4.11 — Harmonic comparison model.

In the setup and notation of this section, the paper defines or asserts:



$$`A_m(h)=[z^m]\bar H(z)^{-h},\qquad
\mathcal M_{g,n}(\mathbf d)=3^h\Gamma(h)4^{-g}A_m(h),\qquad
R=\mathcal U/\mathcal M.`



Lean scope (stage one): these declarations use the explicit mathematical interfaces shown in their Lean types. Their proof status and registered external dependencies are recorded in the compiled phase-one audit. Concrete DM/WP and other classical instances remain unconstructed; no unconditional geometric verification is asserted.

:::



All $`A_m(h)` are positive. Define 

$$`q_\ell=\theta_\ell\,\frac{A_{m-\ell}(h-1)}{A_m(h)},
\qquad S_0=\sum_{\ell=0}^m q_\ell,\qquad
L=2D+n=3h-2m.`

 For $`h\ge2`, the identity $`\bar K=\bar H+(2/3)z\bar H'` gives exactly

:::proposition "eq:H13" (parent := "paper_core") (tags := "paper-new") (priority := "high") (uses := "eq:H12")
%%%
source := { document := "paper-v3", spans := #[{ page := "22", anchor := "eq:H13", citation := "Equation 4.12", pdf := some { path := "source/paper.pdf" } }] }
%%%

Proposition 4.12 — Linear mass identity.

In the setup and notation of this section, the paper defines or asserts:



$$`\sum_{\ell=0}^m q_\ell
\left(1-\frac{2(m-\ell)}{3(h-1)}\right)=1.`


:::



Indeed, the generating series of the left side, before division by $`A_m(h)`, is 

$$`\bar K^{-1}\left(\bar H^{-(h-1)}
-\frac{2z}{3(h-1)}(\bar H^{-(h-1)})'\right)
=\bar K^{-1}\bar K\bar H^{-h}=\bar H^{-h}.`



Dividing {bpref "eq:H9"}[4.8] by the model turns its linear terms into a weighted sum of the ratios $`R` at the children. We check that these weights have total mass one when the pivot degree $`d_1` is positive; this is the meaning of {bpref "eq:H13"}[4.12]. Assume $`g\ge2`; states of genus at most one are terminal in the argument of Section 5. A merging child has type $`(g,n-1)` and a nonseparating child type $`(g-1,n+1)`; both have complexity $`h-1` and deficit $`m-\ell`. Hence the model ratio of a merging child to its parent is $`A_{m-\ell}(h-1)/(3(h-1)A_m(h))`, and that of a nonseparating child is four times larger, because of the factor $`4^{-g}` in {bpref "eq:H12"}[4.11]. The merging children carry the coefficients $`(2d_j+1)\theta_\ell`, $`j\ge2`, and there are $`d_1+\ell-1` ordered nonseparating pairs, each with coefficient $`\theta_\ell/2`. Since $`2D+n=3h-2m`, the total weight is 

$$`\sum_{\ell=0}^m q_\ell\,
 \frac{\sum_{j\ge2}(2d_j+1)+2(d_1+\ell-1)}{3(h-1)}
 =\sum_{\ell=0}^m q_\ell\,\frac{3(h-1)-2(m-\ell)}{3(h-1)}=1`

 by {bpref "eq:H13"}[4.12]. Thus, for a positive pivot, the linear model weights form a probability kernel $`P`, and positivity of the separating terms gives $`R\ge PR`.

At an all-zero state, where every degree and hence the pivot vanishes, the formal $`\ell=0` count includes one nonseparating pair with multiplicity $`-1`, and also includes $`n-1` invalid mergers. The true linear mass is instead

:::proposition "eq:H14" (parent := "paper_core") (tags := "paper-new") (priority := "high") (uses := "eq:H12")
%%%
source := { document := "paper-v3", spans := #[{ page := "23", anchor := "eq:H14", citation := "Equation 4.13", pdf := some { path := "source/paper.pdf" } }] }
%%%

Proposition 4.13 — All-zero mass defect.

In the setup and notation of this section, the paper defines or asserts:



$$`s=1+\frac{3-n}{3(h-1)}
       \frac{A_m(h-1)}{A_m(h)}.`


:::



Since $`\bar H(0)=1` and $`\bar H^{-1}` has positive coefficients, $`A_m(h-1)\le A_m(h)`. In the range $`g\ge2`, therefore, 

$$`s\ge\frac23,\qquad
s\le1\ (n\ge3),\qquad s\le1+O(h^{-1})\ (n=1,2).`

 Thus for a zero pivot the linear terms need not have mass exactly one.

We now record the analytic information needed below. The function 

$$`P_Y(w)=\frac{\bar H_Y(1)}{\bar H_Y(w)}`

 is the probability generating function of {bpref "eq:P12"}[2.8], recalled here. By Subsection 2.2, it has mean $`3/2` and, uniformly in the compact parameter interval, it is analytic on a disk of radius $`1+\eta>1`; its constant and linear coefficients are bounded below by positive constants; and its variance is bounded above and away from zero. Let $`S_h` be the sum of $`h` independent variables with probability generating function 4.15. The uniform local limit theorem {bpref "eq:P13"}[2.9], proved there by Fourier inversion, gives 

$$`\Pr(S_h=m)\ge c_Bh^{-1/2}
\quad\text{when }|m-3h/2|\le B\sqrt h,`

 and at bounded displacement, where the odd cubic term integrates to zero, 

$$`\Pr(S_h=3h/2+d)
=\frac{\mathrm{e}^{-d^2/(2h\sigma_Y^2)}}{\sqrt{2\pi h\sigma_Y^2}}
  (1+O_B(h^{-1})),\qquad |d|\le B,`

 at integer arguments. The same Fourier argument applies after tilting at a positive radius $`\rho` in a compact subset of the analytic interval; here $`\rho` is a radius in the normalized $`z`-coordinate. If $`\mu_Y(\rho)=-\rho\bar H_Y'(\rho)/\bar H_Y(\rho)=m/h`, it gives 

$$`A_m(h)=
\frac{\bar H_Y(\rho)^{-h}\rho^{-m}}{\sqrt{2\pi h\,\rho\mu_Y'(\rho)}}
 (1+O(h^{-1}))`

 uniformly on such compact tilted families. Near the mean, the tilted rate function has bounded second derivative and vanishing value and first derivative; hence, for a fixed sufficiently small $`c_0>0`, 

$$`\Pr(S_h=3h/2-u)\ge ch^{-1/2}\mathrm{e}^{-Cu^2/h},
\qquad 0\le u\le c_0h.`



The coefficient/probability relation is 

$$`A_m(h)=\bar H(1)^{-h}\Pr(S_h=m).`

 Consequently, when $`L\le\sqrt h`, 4.10, 4.16, and the sum of the numerator probabilities give $`S_0\le C\sqrt h`. When $`L\ge6`, the minimum factor in {bpref "eq:H13"}[4.12] is $`(L-3)/(3(h-1))`, so $`S_0\le Ch/L`. Combining the two estimates,

:::proposition "eq:H22" (parent := "paper_core") (tags := "paper-new") (priority := "high") (uses := "eq:H12")
%%%
source := { document := "paper-v3", spans := #[{ page := "23", anchor := "eq:H22", citation := "Equation 4.21", pdf := some { path := "source/paper.pdf" } }] }
%%%

Proposition 4.21 — Uniform linear coefficient mass bounds.

In the setup and notation of this section, the paper defines or asserts:



$$`S_0\le C\sqrt h,\qquad S_0\le Ch/L\quad(L\ge6).`


:::



All constants here are uniform in $`Y`, and the finitely many states of bounded complexity are absorbed into them.
