import WPFormalization.Statements
import WPBlueprint.Chapters.C03
import Verso
import VersoManual
import VersoBlueprint

open Verso.Genre Verso.Genre.Manual Informal

#doc (Manual) "05-comparison" =>

# Comparison with the harmonic model

:::proposition "prop:harmonic" (parent := "paper_core") (tags := "paper-new") (priority := "high") (uses := "eq:H12")
%%%
source := { document := "paper-v3", spans := #[{ page := "24", anchor := "prop:harmonic", citation := "Proposition 5.1", pdf := some { path := "source/paper.pdf" } }] }
%%%

Proposition 5.1 — Uniform harmonic comparison.

For every fixed $`n\ge1`, there is a constant $`C_n` such that 

$$`-C_n\log^2(h+1)\le
 \log\frac{\mathcal U_{g,n}(\mathbf d;Y)}
 {3^h\Gamma(h)4^{-g}[z^m]\bar H_Y(z)^{-h}}
 \le C_n\sqrt h`

 for every stable pair $`(g,n)`, every $`\mathbf d\in\mathbb Z_{\ge0}^n` with $`|\mathbf d|\le3g-3+n`, and every $`Y\in[0,y_0]`. Here $`h=2g-2+n` and $`m=3g-3+n-|\mathbf d|`.

Lean scope (stage one): these declarations use the explicit mathematical interfaces shown in their Lean types. Their proof status and registered external dependencies are recorded in the compiled phase-one audit. Concrete DM/WP and other classical instances remain unconstructed; no unconditional geometric verification is asserted.

:::



The idea is the following. Write $`R=\mathcal U/\mathcal M` for the ratio of a true amplitude to the model amplitude {bpref "eq:H12"}[4.11], and divide the recursion {bpref "eq:H9"}[4.8] by the model. Because the model satisfies the linear part of the recursion with total mass one (identity {bpref "eq:H13"}[4.12]), the linear terms express $`R` at a state as an average of $`R` over the states of complexity $`h-1` reached in one step, and the separating terms add a nonnegative amount. Thus $`R` is bounded below by its expectation along a random walk that lowers the complexity, and it is bounded above as soon as the separating contribution is small.

The comparison of intersection recursions with random walks has an important precedent in Aggarwal’s proof of uniform asymptotics for pure $`\psi` intersections \[2\]. Here the recursion and its comparison model vary with $`Y`; the estimates must also remain uniform as this parameter approaches the pure-$`\psi` endpoint.

Throughout this section a state is a stable pair $`(g,n)`, $`n\ge1`, with a degree tuple $`\mathbf d\in\mathbb Z_{\ge0}^n`, $`|\mathbf d|\le3g-3+n`, and a parameter $`Y\in[0,y_0]`; constants are uniform in $`Y` and in the state unless stated otherwise. We write $`Z_0` for the number of entries of $`\mathbf d` equal to zero. A state is terminal if $`m=0` or $`g\le1`; the random walks below stop there. The proof has three steps.

1. Lemma {bpref "lem:terminal"}[5.2] bounds $`R` at terminal states, using only the string and dilaton equations and the coarse bounds of Appendix B.

2. Lemma {bpref "lem:lower"}[5.3] proves the lower bound. The only defect of the averaging is at entries of degree zero, where some linear terms are missing; we show that the random walk does not create many such entries.

3. Lemmas {bpref "lem:weighted-linear"}[5.4]–{bpref "lem:upper"}[5.6] prove the upper bound. We divide $`R` by a weight that penalizes entries of degree zero and one, show that the weighted separating terms have relative size $`O(h^{-1/2})`, and conclude by examining, at each complexity, the state at which the weighted ratio is largest.

## Bounds at terminal states

:::lemma_ "lem:terminal" (parent := "paper_core") (tags := "paper-new") (priority := "high") (uses := "eq:H12")
%%%
source := { document := "paper-v3", spans := #[{ page := "24", anchor := "lem:terminal", citation := "Lemma 5.2", pdf := some { path := "source/paper.pdf" } }] }
%%%

Lemma 5.2 — Terminal bounds.

There are constants $`c_\psi,C_\psi,c,C>0` with the following properties.

1. For every pure $`\psi` tuple $`\mathbf e` with $`Z_0` zero entries, $`c_\psi(2/3)^{Z_0}\le C_g(\mathbf e)\le C_\psi2^{Z_0}`, in the normalization {bpref "eq:H4"}[4.3].

2. At every terminal state, $`R\ge c\,\mathrm e^{-CZ_0}`.

3. At every state, $`R\le\mathrm e^{Ch}`.

Lean scope (stage one): these declarations use the explicit mathematical interfaces shown in their Lean types. Their proof status and registered external dependencies are recorded in the compiled phase-one audit. Concrete DM/WP and other classical instances remain unconstructed; no unconditional geometric verification is asserted.

:::



:::proof "lem:terminal" (uses := "lem:primitive-bounds, eq:H9")
For (i), the standard normalized string and dilaton identities imply 

$$`c_\psi(2/3)^{Z_0}\le C_g(\mathbf e)\le C_\psi2^{Z_0},`

 where $`Z_0` is the number of zero entries. To prove this, first remove the entries equal to one by the normalized dilaton equation, retaining the final genus-one tuple $`(1)`. At a noninitial tuple with a zero, let $`p_+` denote the number of positive entries; normalized string has total positive coefficient 

$$`\frac{2(3g-3+q)+p_+}{3(2g-3+q)}`

 between $`2/3` and $`2`. Once the ones have been removed, each string child has one fewer zero; any newly created one can again be removed. With no zeros use the primitive bounds stated after {bpref "eq:H4"}[4.3]; the remaining bases are $`C_0(0,0,0)=1/3` and $`C_1(1)=1/6`. Induction proves 5.1, which is (i).

For (ii) we use a lower comparison that requires no asymptotic information on volumes. Set all kernel coefficients in {bpref "eq:H9"}[4.8] equal to one. The corresponding background of KW times has $`t_1=0,t_2=3,t_k=0` for $`k\ge3`, so its amplitudes are 

$$`\mathcal U^{\rm PI}_{g,n}(\mathbf d)
=\frac{3^m}{m!}\prod_i(2d_i+1)!!
\left\langle\tau_{\mathbf d}\tau_2^m\right\rangle_g.`

 They have the same initial $`(0,3)` and degree-one $`(1,1)` values, and the degree-zero $`(1,1)` value $`1/8`. By 4.10, induction in the positive recursion gives $`\mathcal U\ge\mathcal U^{\rm PI}`.

Uniform analyticity of $`\bar H_Y^{-1}` at zero gives a fixed $`B\ge1` such that $`[z^j]\bar H_Y^{-1}\le B^j`. Thus 

$$`A_m(h)\le B^m(h)_m/m!.`

 Dividing 5.2 by {bpref "eq:H12"}[4.11] and using {bpref "eq:H4"}[4.3] gives 

$$`R\ge C_g(\mathbf d,2^m)
       \left(\frac3{5B}\right)^m.`

 If $`g\le1`, dimension and $`D\ge n-Z_0` imply $`m\le Z_0`. Hence $`R\ge c\mathrm{e}^{-CZ_0}` in this terminal range. At $`m=0`, exactly $`R=C_g(\mathbf d)`, so 5.1 applies directly. This proves (ii).

Finally we prove the global bound (iii), 

$$`R\le \mathrm{e}^{Ch}.`

 Note that in the normalized finite sum {bpref "eq:H6"}[4.5]–{bpref "eq:H7"}[4.6] a background insertion of degree $`k` has weight 

$$`v_k(Y)=-r_Y^{k-1}X^{(k)}(Y)/a.`

 The corresponding absolute majorant is 

$$`B_Y(z)=\sum_{k\ge2}\frac{3|v_k(Y)|}{(2k+1)!!}z^{k-1}.`

 This family has a uniformly bounded analytic germ and vanishes at zero. Indeed it is the coefficientwise absolute version of $`1-\bar H_Y`; the normalized family in {bpref "eq:H2"}[4.1]–{bpref "eq:H3"}[4.2] is compact and analytic on a common disk. Thus a fixed $`z_*>0` makes $`B_Y(z_*)\le1/2`. Using the upper bound in 5.1 on every primitive term of {bpref "eq:H6"}[4.5] gives 

$$`\mathcal U\le
C2^{Z_0}3^h\Gamma(h)4^{-g}[z^m](1-B_Y(z))^{-h}
\le C2^{Z_0}3^h\Gamma(h)4^{-g}z_*^{-m}2^h.`

 The linear coefficient of $`-\log \bar H_Y` is uniformly positive. Therefore 

$$`A_m(h)\ge (ch)^m/m!\ge \mathrm{e}^{-C'h},`

 because $`m\le3h/2`; the case $`m=0` is immediate. Since $`Z_0\le n\le h+2`, division proves 5.4.
:::



## The lower bound: control of zero degrees

:::lemma_ "lem:lower" (parent := "paper_core") (tags := "paper-new") (priority := "high") (uses := "eq:H12")
%%%
source := { document := "paper-v3", spans := #[{ page := "25", anchor := "lem:lower", citation := "Lemma 5.3", pdf := some { path := "source/paper.pdf" } }] }
%%%

Lemma 5.3 — Lower bound.

There are constants $`c,C>0` such that, at every state, 

$$`R\ge c\exp\{-C(Z_0+\log(h+1))\log(h+1)\}.`



Lean scope (stage one): these declarations use the explicit mathematical interfaces shown in their Lean types. Their proof status and registered external dependencies are recorded in the compiled phase-one audit. Concrete DM/WP and other classical instances remain unconstructed; no unconditional geometric verification is asserted.

:::



:::proof "lem:lower" (uses := "lem:terminal, eq:H13, eq:H14, ext:optional-stopping")
Since the separating terms of {bpref "eq:H9"}[4.8] are nonnegative, $`R` is at least the average of $`R` over its linear children. Iterating, $`R` is bounded below by the expected terminal value along a random walk that lowers the complexity by one at each step. Two losses occur: the terminal bounds 5.1 and 5.3 lose a factor exponential in the number of zero entries, and the averaging may have mass $`s<1` at states with all degrees zero, again with a loss controlled by the number of zeros. It therefore suffices to show that the walk rarely creates many zero entries.

At a nonterminal state choose any positive pivot if one exists; otherwise choose a zero. Stop only at $`m=0` or $`g\le1`. Use the linear model weights, divided by their mass $`s`, as transition probabilities. For a positive pivot $`s=1`; at an all-zero state use {bpref "eq:H14"}[4.13]–4.14.

Let $`Z` be the current zero count. At a positive pivot, a merger with a marking of degree zero lowers $`Z` by one, except when the pivot has degree one and $`\ell=0`; that merger leaves $`Z` unchanged. A nonseparating ordered pair can increase $`Z` by at most two, and at each $`\ell` there are at most two pairs containing a zero. Each pair has twice the model weight of a merger with one zero marking. Thus 

$$`p_{\rm birth}\le4p_{\rm death}/Z\qquad(Z\ge1).`

 That exceptional term contributes neither a birth nor a death. At an all-zero state, a birth occurs only at $`\ell=2`, raises the count by one, and its weight is at most $`2/(Z-1)` times the mass of mergers with a zero marking. Those mergers have $`\ell\ge1` and lower the count by at least one. Hence 5.5 still holds for $`Z\ge2`. Normalization by $`s` preserves these comparisons.

For $`Z\ge24`, the conditional drift obeys 

$$`\frac{\mathbb E(2^{Z_{\rm next}})}{2^Z}-1
\le3p_{\rm birth}-\frac12p_{\rm death}\le0.`

 During each excursion above 24, optional stopping bounds the probability of reaching $`M` by $`2^{Z_{\rm start}-M}`. An excursion entered from below starts at a value at most 26. Since complexity decreases by one, there are at most $`h_{\rm initial}+1` excursions. A union bound therefore shows that, with probability at least $`1/2`, 

$$`\max Z\le Z_{\rm initial}+C+C\log(h_{\rm initial}+1).`

 All stopping times are bounded, so optional stopping applies without further integrability conditions.

Only all-zero steps can have $`s<1`. By {bpref "eq:H14"}[4.13]–4.14, 

$$`-\log\min(s,1)\le CZ/h.`

 On the event 5.6, write its upper bound as $`M`. Summing over the decreasing complexities costs at most 

$$`CM+CM\sum_{j=M+1}^{h_{\rm initial}}\frac1j
\le CM\log(h_{\rm initial}+1).`

 Iterated positivity gives 

$$`R_{\rm initial}\ge
\mathbb E\!\left[R_{\rm terminal}\prod_{\rm steps}s\right].`

 Here the initial zero count is $`Z_0`. The terminal bounds of Lemma {bpref "lem:terminal"}[5.2](ii), applied at terminal zero counts at most $`M`, and the probability in 5.6 now prove 

$$`R\ge c\exp\{-C(Z_0+\log(h+1))\log(h+1)\}.`

 No asymptotics for volumes enter at the terminal states.
:::



## The upper bound: a weight for degrees zero and one

For the upper bound the separating terms must be shown to be small, and for general states they are not: a state with many entries of degree zero or one can distribute these markings between the two components in many ways. We therefore divide $`R` by a weight that grows with the number of such entries. It is chosen so that the linear terms still average $`R/\mathcal W` up to a factor $`1+O(h^{-1/2})` (this is 5.9), while the weighted separating terms become small (Subsection 5.4).

Call degrees zero or one inactive. Let $`\iota` be their number, $`Z_0` the number of zeros, and $`R_{\rm act}` the number of degrees at least two. Fix a sufficiently small constant $`c_*>0`, and set

:::definition "eq:H30" (parent := "paper_definitions") (tags := "paper-definition") (priority := "high") (uses := "def:stable")
%%%
source := { document := "paper-v3", spans := #[{ page := "26", anchor := "eq:H30", citation := "Equation 5.8", pdf := some { path := "source/paper.pdf" } }] }
%%%

Definition 5.8 — Clipped inactive weight.

In the setup and notation of this section, the paper defines or asserts:



$$`\phi(\iota)=\prod_{j=1}^\iota\max(1,c_*\sqrt j),\qquad
\mathcal W(\mathbf d)=4^{Z_0}\phi(\iota).`


:::



We call the truncation $`\max(1,\cdot)` clipping; it makes $`\phi` nondecreasing, since every factor is at least one. Up to fixed multiplicative constants, $`\phi(\iota)` equals $`c_*^\iota\sqrt{\iota!}`. Its monotonicity is essential when an inactive pivot splits into two active degrees.

In the upper bound we choose the pivot as follows: an active entry when one exists, an entry equal to one if no active entry exists, and a zero only at an all-zero state. Again the walk stops only at terminal states. The linear model weights $`p_{\rm child}` of a state are the weights that appear when {bpref "eq:H9"}[4.8] is divided by the model; their mass is given by {bpref "eq:H13"}[4.12]–4.14, and may exceed one at an all-zero state with one or two markings.

:::lemma_ "lem:weighted-linear" (parent := "paper_core") (tags := "paper-new") (priority := "high") (uses := "eq:H30")
%%%
source := { document := "paper-v3", spans := #[{ page := "27", anchor := "lem:weighted-linear", citation := "Lemma 5.4", pdf := some { path := "source/paper.pdf" } }] }
%%%

Lemma 5.4 — Weighted linear terms.

If $`c_*` is sufficiently small, then at every nonterminal state 

$$`\sum_{\rm linear}p_{\rm child}
\frac{\mathcal W_{\rm child}}{\mathcal W}
\le1+CS_0/h\le1+Ch^{-1/2}.`


:::



:::proof "lem:weighted-linear" (uses := "eq:H13, eq:H14, eq:H22")
The second inequality is {bpref "eq:H22"}[4.21]. We consider the three possible pivots in turn.

For an active pivot, an ordinary inactive merger reduces $`\iota` by at least one and does not increase $`Z_0`. For all sufficiently large $`\iota`, its weight ratio is at most $`1/2`. The exception is a pivot of degree two merged with a zero at $`\ell=0`: it turns that zero into a one, leaves $`\iota` fixed, and divides the weight by four. The favorable mass is therefore at least a fixed positive multiple of $`\iota S_0/h`.

At each $`\ell`, at most four nonseparating pairs contain an inactive degree. A pair creating two inactive degrees has weight ratio, for large $`\iota`, at most 

$$`16c_*^2\sqrt{(\iota+1)(\iota+2)}.`

 Its total model mass per $`\ell` is bounded by a fixed multiple of $`q_\ell/h`. Choose $`c_*` so small that the coefficient of $`\iota` in this upper bound is less than half the favorable merger coefficient. Pairs creating only one inactive degree cost $`O(\sqrt \iota)`, and all other pairs leave the weight unchanged. The remaining expression is bounded above by $`CS_0/h`. Bounded $`\iota`, including the clipping threshold, also costs only $`CS_0/h`, because there are at most four exceptional pairs and boundedly many inactive mergers.

If the pivot has degree one and all markings are inactive, every merger decreases $`\iota`, while a nonseparating step increases it by at most one. Only four pairs per $`\ell` can increase the weight; a pair with two active new degrees decreases $`\iota` and cannot increase the clipped weight. The same argument applies, with $`\iota-1` favorable merging labels.

At an all-zero state, all valid mergers have $`\ell\ge1` and decrease both the zero count and the inactive weight. Increasing pairs have $`\ell\ge2` and increase $`\iota` by at most one. Use $`S_0-q_0` in both birth and merger estimates. The unweighted mass correction {bpref "eq:H14"}[4.13] is nonpositive for $`n\ge3` and $`O(h^{-1})` otherwise. This proves 5.9 in every case.
:::



## Bounding the separating terms

We now show that, after weighting, the separating terms of {bpref "eq:H9"}[4.8] have total relative size $`O(h^{-1/2})`, uniformly in the state. Splitting off a component of complexity $`h_1\le h_2` costs the factor $`\Gamma(h_1)\Gamma(h_2)/\Gamma(h)`, which is at most $`\binom{h-3}{h_1-1}^{-1}`; the point is that this beats the number of ways of distributing the marking labels, once the weight has absorbed the inactive ones. For a separating term with node degrees $`u,v` and kernel index $`\ell`, write $`\mathcal M_1,\mathcal M_2` and $`\mathcal W_1,\mathcal W_2` for the model amplitudes and weights of its two factors.

:::lemma_ "lem:weighted-separating" (parent := "paper_core") (tags := "paper-new") (priority := "high") (uses := "eq:H30")
%%%
source := { document := "paper-v3", spans := #[{ page := "27", anchor := "lem:weighted-separating", citation := "Lemma 5.5", pdf := some { path := "source/paper.pdf" } }] }
%%%

Lemma 5.5 — Weighted separating terms.

Let $`\eta=1/12`. At every nonterminal state, 

$$`\sum_{\rm separating}\frac{\theta_\ell}{2}\,
 \frac{\mathcal M_1\mathcal M_2}{\mathcal M}\,
 \frac{\mathcal W_1\mathcal W_2}{\mathcal W}\,
 \mathrm e^{\eta\min(h_1,h_2)}
 \le CS_0h^{-3/2}(1+\iota)\le Ch^{-1/2},`

 where the sum runs over all separating terms of {bpref "eq:H9"}[4.8].
:::



:::proof "lem:weighted-separating" (uses := "eq:H12, eq:H22")
The degree-dimension constraint supplies 

$$`4R_{\rm act}+n\le3h,\qquad R_{\rm act}\le3h/5.`

 Remove the pivot, leaving $`\iota_*` inactive and $`R_*` active labeled markings, with $`\iota_*+R_*=n-1`, $`\iota_*\le \iota`, and $`R_*\le R_{\rm act}`. In one separating component put $`u` inactive and $`j` active original labels, and write $`s=u+j`. Each child receives one new marking. Comparing {bpref "eq:H30"}[5.8] with $`4^{Z_0}c_*^\iota\sqrt{\iota!}`, uniformly over the two new degrees, 

$$`\frac{\mathcal W_1\mathcal W_2}{\mathcal W}
\le C\frac{\sqrt{(s+2)h}}{\sqrt{\binom{\iota_*}u}}.`

 Indeed, when the $`\iota_*` inactive original labels split as $`u,\iota_*-u`, the factorial part of this estimate is bounded by 

$$`\frac{\sqrt{(u+1)!(\iota_*-u+1)!}}{\sqrt{\iota_*!}}
 =\frac{\sqrt{(u+1)(\iota_*-u+1)}}{\sqrt{\binom{\iota_*}u}}.`

 Each child receives at most one inactive new marking. Since $`u\le s` and $`\iota_*\le h+2`, the numerator is at most $`C\sqrt{(s+2)h}`. The powers of $`c_*`, the factor for zeros, and the clipping comparison change by bounded integer exponents. An inactive pivot supplies an additional factor $`\iota^{-1/2}`, which was discarded. The exponential factors and clipping comparison contribute only a fixed constant, since the total inactive and zero counts change by bounded amounts.

Orient $`h_1\le h_2`, and put 

$$`h'=h-3,\qquad k=h_1-1\le h'/2,\qquad s=k+2-2g_1.`

 Then 

$$`\frac{\Gamma(h_1)\Gamma(h_2)}{\Gamma(h)}
=\frac1{(h-1)(h-2)\binom{h'}k}.`

 For all sufficiently large $`h`, 5.10 gives $`R_*\le2h'/3`.

The required label sum is 

$$`\Lambda_s=\sum_{u+j=s}\binom{\iota_*}u^{1/2}\binom{R_*}j.`

 Cauchy–Schwarz and Vandermonde give 

$$`\Lambda_s\le
\binom{\iota_*+R_*}s^{1/2}
\left(\sum_{j\le s}\binom{R_*}j\right)^{1/2}.`

 For $`k\ge1`, take $`\xi =k/(h'-k)\le1`. The two factors before square roots are bounded by $`\xi ^{-s}(1+\xi )^{\iota_*+R_*}` and $`\xi ^{-s}(1+\xi )^{R_*}`, respectively. The binomial mass at its mean gives 

$$`\binom{h'}k\ge c(k+1)^{-1/2}\xi ^{-k}(1+\xi )^{h'}.`

 Thus, if $`g_1\ge1`, so $`s\le k`, 

$$`\frac{\Lambda_s}{\binom{h'}k}
\le C\sqrt{k+1}\,\xi ^{k-s}(1+\xi )^{-h'/6}
\le C\sqrt{k+1}\mathrm{e}^{-k/6}.`

 Here $`\iota_*+R_*=n-1\le h'`, $`R_*\le2h'/3`, and $`h'\log(1+\xi )\ge k`. The case $`k=0` is immediate.

If $`g_1=0`, then $`s=k+2`. Validity of this component forces $`2j\le s-2=u+j-2`, hence $`u\ge j+2\ge2`. Use 

$$`\binom{\iota_*}u=\frac{\iota_*(\iota_*-1)}{u(u-1)}\binom{\iota_*-2}{u-2}.`

 After taking the square root, discard the denominator and extract a factor $`\iota_*`. The remaining sum has $`u-2+j=k`, so 5.13–5.14 apply with $`\iota_*-2` in place of $`\iota_*`. This use of the degree constraint is what replaces a factorial penalty on active labels.

Combining these estimates with 5.11–5.12, and summing the polynomially many genus choices at fixed $`k`, proves, for example with $`\eta=1/12`, 

$$`\sum_{\rm genus/label\ splits}
\frac{\Gamma(h_1)\Gamma(h_2)}{\Gamma(h)}
\sup_{\rm valid\ node\ degrees}
\frac{\mathcal W_1\mathcal W_2}{\mathcal W}
\mathrm{e}^{\eta\min(h_1,h_2)}
\le C h^{-3/2}(1+\iota).`

 An empty supremum contributes zero. Thus the bound is uniform in the possible node degrees; their sum, with its model coefficients, is handled next.

For a separating recursion term, exact model normalization gives 

$$`\frac{\theta_\ell}{2}\frac{\mathcal M_1\mathcal M_2}{\mathcal M}
=\frac{\theta_\ell}{6}
\frac{\Gamma(h_1)\Gamma(h_2)}{\Gamma(h)}
\frac{A_{m_1}(h_1)A_{m_2}(h_2)}{A_m(h)}.`

 Since $`h_1+h_2=h-1` and $`m_1+m_2=m-\ell`, positivity and coefficient convolution bound the sum over node degrees by $`A_{m-\ell}(h-1)`. More explicitly, for each genus/label partition first apply the node-independent envelope 5.11, then extend the allowed nonnegative model-coefficient sum to the full convolution. The resulting label envelope is exactly the one summed in 5.13–5.15, so variable degree supports cause no interchange issue. Consequently the entire weighted separating mass, including the exponential factor $`\mathrm e^{\eta\min(h_1,h_2)}` of 5.15, is at most 

$$`CS_0h^{-3/2}(1+\iota)=O(h^{-1/2}).`

 For $`L\ge6`, use $`S_0\le Ch/L` and $`\iota\le n\le L`. For $`L\le5`, both $`\iota` and $`L` are bounded, and $`S_0\le C\sqrt h` gives the smaller $`O(h^{-1})` bound.
:::



## The upper bound from successive maxima

:::lemma_ "lem:upper" (parent := "paper_core") (tags := "paper-new") (priority := "high") (uses := "eq:H30")
%%%
source := { document := "paper-v3", spans := #[{ page := "29", anchor := "lem:upper", citation := "Lemma 5.6", pdf := some { path := "source/paper.pdf" } }] }
%%%

Lemma 5.6 — Upper bound.

There is a constant $`C` such that $`R\le C\mathcal W\mathrm e^{C\sqrt h}` at every state.

Lean scope (stage one): these declarations use the explicit mathematical interfaces shown in their Lean types. Their proof status and registered external dependencies are recorded in the compiled phase-one audit. Concrete DM/WP and other classical instances remain unconstructed; no unconditional geometric verification is asserted.

:::



:::proof "lem:upper" (uses := "lem:terminal, lem:weighted-linear, lem:weighted-separating")
By Lemmas {bpref "lem:weighted-linear"}[5.4] and {bpref "lem:weighted-separating"}[5.5], the weighted ratio satisfies an approximate maximum principle: at each nonterminal state, $`R/\mathcal W` is at most $`1+O(h^{-1/2})` times the largest value at its linear children, plus a separating contribution that is small. We apply this at complexities where the maximum of $`R/\mathcal W` reaches a record, first to exclude exponential growth 5.18, and then to obtain the bound $`\mathrm e^{C\sqrt h}` in 5.19.

At $`m=0`, 5.1 and {bpref "eq:H30"}[5.8] give $`R/\mathcal W\le C`. At $`g\le1`, one has $`D\le n`, so $`R_{\rm act}\le n/2` and $`\iota\ge n/2`. Thus $`\log\mathcal W\ge(n/4)\log n-O(n)`, which dominates 5.4, since $`h=n+O(1)`. Hence $`R/\mathcal W` is bounded at every terminal state.

Let 

$$`M_h=\max_{\substack{Y\in[0,y_0]\\\text{valid states of complexity }h}}
\frac{R}{\mathcal W}.`

 The maximum exists: the tuple set is finite and the normalized parameter interval is compact. Equation 5.4 gives $`\gamma=\limsup h^{-1}\log M_h<\infty`. Suppose $`\gamma>0`, and choose $`0<\gamma'<\gamma`, $`\delta>0`, so close that $`\gamma+\delta-\gamma'<\eta` from 5.15. Call $`h` a record for a sequence $`a_h` if $`a_h>a_j` for all $`j<h`. There are arbitrarily large records of $`M_h\mathrm{e}^{-\gamma'h}`, and their maximizing states are nonterminal. At such a record, 

$$`M_j/M_h\le \mathrm{e}^{-\gamma'(h-j)}\quad(j<h),\qquad
M_j\le C_\delta \mathrm{e}^{(\gamma+\delta)j}.`

 The linear part, after division by the maximizing value, is bounded by $`(1+Ch^{-1/2})\mathrm{e}^{-\gamma'}`. For a separating term use the record inequality on the larger child and the global bound on the smaller. Their product divided by $`M_h` is at most a fixed constant times $`\mathrm{e}^{(\gamma+\delta-\gamma')h_{\rm small}}`. Equation 5.17, which includes the factor $`\mathrm e^{\eta\min(h_1,h_2)}`, makes the total separating contribution $`o(1)`. The recursion would therefore give $`1\le \mathrm{e}^{-\gamma'}+o(1)`, a contradiction. Thus 

$$`\limsup h^{-1}\log M_h\le0.`



To obtain the quantitative envelope, fix $`0<\delta<\eta`, so 5.18 gives $`M_j\le C_\delta \mathrm{e}^{\delta j}`. Consider record maxima of $`M_h/\mathrm{e}^{A\sqrt h}`. If these were unbounded, their large maximizing states would again be nonterminal. For the larger separating child, the record bound supplies $`M_{\rm large}/M_h\le \mathrm{e}^{A(\sqrt{h_{\rm large}}-\sqrt h)}\le1`; bound the smaller child by $`C_\delta \mathrm{e}^{\delta h_{\rm small}}`. The separating contribution is therefore $`C'h^{-1/2}`, with $`C'` independent of $`A`. The linear record ratio is 

$$`\mathrm{e}^{A(\sqrt{h-1}-\sqrt h)}
=1-\frac{A}{2\sqrt h}+O_A(h^{-1}).`

 Using 5.9, the recursion would give 

$$`1\le1+\frac{C+C'-A/2}{\sqrt h}+O_A(h^{-1}).`

 Choosing $`A>2(C+C'+1)` excludes unbounded records. We have proved 

$$`R/\mathcal W\le C \mathrm{e}^{C\sqrt h},`

 uniformly in the entire normalized parameter family.
:::



## Completion of the comparison

:::proof "prop:harmonic" (uses := "lem:lower, lem:upper")
For fixed $`n`, the zero count and the inactive count are at most $`n`, so $`\mathcal W\le4^n\phi(n)` is bounded. Lemmas {bpref "lem:lower"}[5.3] and {bpref "lem:upper"}[5.6] therefore give, for every fixed $`n\ge1`, 

$$`-C_n\log^2(h+1)\le
\log\frac{\mathcal U_{g,n}(\mathbf d;Y)}
 {3^h\Gamma(h)4^{-g}[z^m]\bar H_Y(z)^{-h}}
\le C_n\sqrt h,`

 uniformly for $`Y\in[0,y_0]` and every degree tuple in the range of Proposition {bpref "prop:harmonic"}[5.1]. This proves the proposition.
:::



In particular the uniform error is $`o(g)`.

We record the case $`Y=0`, which compares the Weil–Petersson brackets themselves with an explicit model; it is the input for the coefficient ratios in Section 13. At $`Y=0`, $`a=1`, $`r_0=\pi^2/2`, and 

$$`H_0(z)=\frac{3(\sin\sqrt{2z}-\sqrt{2z}\cos\sqrt{2z})}
 {(\sqrt{2z})^3}.`

 By {bpref "eq:H5"}[4.4] and {bpref "eq:H7"}[4.6], $`\mathcal U=b/4^N`, where $`b=[\tau_{d_1}\cdots\tau_{d_n}]_{g,n}`. Undoing this same scaling in the model yields 

$$`M^{\rm WP}_{g,n}(\mathbf d)
=4^D3^h\Gamma(h)4^{-g}(2\pi^2)^m
 [z^m]H_0(z)^{-h}.`

 Thus 5.20 applies unchanged to $`b/M^{\rm WP}`. For $`n=1`, $`h=2g-1`, $`m=3g-2-k`, it gives exactly 

$$`\mathrm{e}^{-C\log^2(g+1)}
\le
\frac{[\tau_k]_{g,1}}
 {4^k3^{2g-1}\Gamma(2g-1)4^{-g}(2\pi^2)^{3g-2-k}
 [z^{3g-2-k}]H_0(z)^{-(2g-1)}}
\le \mathrm{e}^{C\sqrt g},`

 uniformly over $`0\le k\le3g-2`.
