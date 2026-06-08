#import "../typst/commands.typ": *

/*
#import "@preview/lemmify:0.1.8": *
#let (
  theorem, lemma, corollary,
  remark, proposition, example,
  proof, rules: thm-rules
) = default-theorems("thm-group", lang: "en")
#show: thm-rules


#set heading(numbering: "1.")
#set math.equation(numbering: "(1.1)")
#show: equate.with(breakable: true, sub-numbering: true)
#show: intertext-rule
*/

#lemma[
    For:
    - $E$ a pre-Hilbert space, 
    - $F subset E$ a non empty set stable by scaling #ie ($forall x in F, forall lambda in RR, lambda x in F$)
    - $f: F -> E$ respect some scaling homogeneity ($exists p in NN^*,forall x in F, forall lambda in RR, f(lambda x) = lambda^p f(x)$)
    - $y in E$.

    If $(exists x in F, scalarp(f(x), y) > 0)$ we have that:
    $ 
         argmax(d in F | norm(f(d)) <= 1) scalarp(y, f(d)) = argmax(d in F | norm(f(d)) = 1) scalarp(y, f(d))
    $
    and:
    $
      argmin(x in F) norm(y - f(x)) = argmin(x in F | norm(f(x)) != 0) norm(y - f(x))
    $

] <lemma:argument_scaling>
#proof[
  Let $I := argmax(d in F|norm(f(d)) <= 1) scalarp(y, f(d))$ and $R := argmax(d in F|norm(f(d)) = 1) scalarp(y, f(d))$.

  - Let us show that $I subset R$. Let $d^* in I$; we show that $norm(f(d^*)) = 1$.


    Let $x in F$ with $scalarp(f(x), y) > 0$ (exists by hypothesis). For $epsilon > 0$ small enough $norm(f(epsilon x)) = epsilon^p norm(f(x)) <= 1$, so $epsilon x$ is feasible for $I$, and $scalarp(y, f(epsilon x)) = epsilon^p scalarp(y, f(x)) > 0$. By optimality of $d^*$ in $I$, $scalarp(y, f(d^*)) >= scalarp(y, f(epsilon x)) > 0$, hence $f(d^*) != 0$.
    Let $lambda := 1 / norm(f(d^*))^(1/p) > 0$ as $abs(lambda) >= 1$:
    $ scalarp(y, f(d^*)) <= lambda^p scalarp(y, f(d^*)) = scalarp(y, f(lambda d^*)) $ by homogeneity of $f$.
    By maximality of $d^*$ in $I$, as $norm(f(lambda d^*)) = 1$, this is an equality hence $lambda = 1$ and $norm(f(d^*)) = 1$.
    Therefore $d^* in R$ and $I subset R$.

  - Let us show that $R subset I$. Let $d^* in R$; since $I subset R$, $d^*$ maximizes the score over ${d in F | norm(f(d)) <= 1}$, and as $norm(f(d^*)) <= 1$ we have that $d^* in I$. We conclude that $R subset I$.
  
  For the second equality, with the witness $x$ above $norm(y - f(epsilon x))^2 = norm(y)^2 - 2 epsilon^p scalarp(y, f(x)) + epsilon^(2p) norm(f(x))^2 < norm(y)^2$ for $epsilon > 0$ small, while $f(x') = 0$ gives $norm(y - f(x'))^2 = norm(y)^2$; so no minimizer of $norm(y - f(x))$ has $f(x) = 0$.
]


#lemma[
  For:
  - $E$ a pre-Hilbert space,
  - $F subset E$ a non empty set,
  - $f: F -> E$,
  - $y in E$,
  - $n: F -> F$ a sign-flip operator: $forall d in F, f(n(d)) = - f(d)$.

  Then $scalarp(f(.), y)$ takes a strictly positive value as soon as it takes a non-zero one:
  $ (exists x in F, scalarp(f(x), y) != 0) ==> (exists x in F, scalarp(f(x), y) > 0) . $
] <lemma:sign_symmetrization>
#proof[
  Let $x in F$ with $scalarp(f(x), y) != 0$. If $scalarp(f(x), y) > 0$ we are done; otherwise $scalarp(f(x), y) < 0$ and $n(x) in F$ satisfies $scalarp(f(n(x)), y) = - scalarp(f(x), y) > 0$.
]


#theorem[
    For:
    - $E$ a pre-Hilbert space,
    - $F subset E$ a non empty set stable by scaling #ie ($forall x in F, forall lambda in RR, lambda x in F$)
    - $f: F -> E$ respect some scaling homogeneity ($exists p in NN^*,forall x in F, forall lambda in RR, f(lambda x) = lambda^p f(x)$)
    - $n: F -> F$ a sign-flip operator: $forall d in F, f(n(d)) = - f(d)$
    - $y in E$ such that $exists x in F, scalarp(f(x), y) != 0$ (non-degeneracy).

    We have that:
    $
        argmin(x in F) norm(y - f(x)) = {scalarp(y, f(d^*))^(1/p) d^* |  d^* in argmax(d in F | norm(f(d)) <= 1) scalarp(y, f(d)) }
     $ <eq:fixed_norm_optimisation_equivalence>
] <lemma:argmin_norm_to_argmax_scalarp>

#proof[
  By @lemma:sign_symmetrization the non-degeneracy hypothesis yields some $x in F$ with $scalarp(f(x), y) > 0$, so by @lemma:argument_scaling we can add the constraint $norm(f(x)) != 0$ in the left-hand side and replace $<= 1$ by $= 1$ in the right-hand side.
  Let's proceed by set equality.
  $ argmin(x in F | norm(f(x)) != 0) norm(y - f(x)) &= argmin(x in F) (norm(y)^2 - 2scalarp(y, f(x))) + norm(f(x))^2 \
  &= argmin(x in F | norm(f(x)) != 0) ( - 2scalarp(y, f(x)) + norm(f(x))^2 )\
  &= argmin(x in F | norm(f(x)) != 0) ( - 2scalarp(y, norm(f(x)) f(x) / norm(f(x))) + norm(f(x))^2 ) \
  #flushl[As $f$ is homogenous:]
  &= argmin(x in F | norm(f(x)) != 0) ( - 2 norm(f(x)) scalarp(y, f(x / norm(f(x))^(1/p))) + norm(f(x))^2 ) \
  &= argmin(x in F | norm(f(x)) != 0) ( - 2 t scalarp(y, f(d)) + t^2 )
  $
  with $d := x / norm(f(x))^(1/p) in F$ and $t := norm(f(x)) >= 0$.
 The solution over $t$ is achieved at $t = scalarp(y, f(d))$. #unclear[Substituting $t = scalarp(y, f(d))$ presupposes $scalarp(y, f(d)) >= 0$; for a direction with negative score the minimum over the feasible $t > 0$ is the (unattained) infimum at $t -> 0^+$ of value $0$, so such directions yield no minimizer. The next line $argmin (- scalarp(y, f(d))^2) = argmax scalarp(y, f(d))$ likewise silently uses $argmax abs(dot) = argmax (dot)$, which holds only because the witness forces the maximal score to be strictly positive. The conclusion is correct, but these two points deserve a word.] Hence we get:
  $ argmin(x in F | norm(f(x)) != 0) norm(y - f(x)) 
  &= argmin(x in F | norm(f(x)) != 0) ( - scalarp(y, f(d))^2 )\
  &= argmax(x in F | norm(f(x)) != 0) scalarp(y, f(d)) \
  &= { scalarp(y, f(d^*))^(1/p) d^* |  d^* in argmax(d in F | norm(f(d)) = 1) scalarp(y, f(d)) }
  $
]

#corollary[
    For:
    - $E$ a pre-Hilbert space, 
    - $F subset E$ a non empty set stable by scaling #ie ($forall x in F, forall lambda in RR, lambda x in F$)
    - $f: F -> E$ respect some scaling homogeneity ($exists p in NN^*,forall x in F, forall lambda in RR, f(lambda x) = lambda^p f(x)$)
    - $n: F -> F$ a sign-flip operator: $forall d in F, f(n(d)) = - f(d)$
    - $y in E$ such that $(exists x in F, scalarp(f(x), y) != 0)$ or $ker f = {0}$.

    We have that:
    $
        argmin(x in F) norm(y - f(x)) prop argmax(d in F|norm(f(d)) <= 1) scalarp(y, f(d))
     $
] <corollary:argmin_norm_to_argmax_scalarp>

#proof[
  - If $exists x in F, scalarp(f(x), y) != 0$, the non-degeneracy hypothesis of @lemma:argmin_norm_to_argmax_scalarp is met (using the same $n$), and its right-hand side is exactly the rescaled $argmax$.
  - Otherwise $forall x in F, scalarp(f(x), y) = 0$ and $ker f = {0}$. Then $norm(y - f(x))^2 = norm(y)^2 + norm(f(x))^2 >= norm(y)^2$, with equality iff $f(x) = 0$, hence $argmin(x in F) norm(y - f(x)) = ker f = {0}$. On the other side $max_(norm(f(d)) <= 1) scalarp(y, f(d)) = 0$, so every maximizer $d^*$ satisfies $scalarp(y, f(d^*)) = 0$ and the rescaled set ${scalarp(y, f(d^*))^(1/p) d^*} = {0}$. Both sides reduce to ${0}$, so the proportionality holds.
]

#let ssel = [$overline(s)$]
#lemma[
  For:
  - $n, p, a, b, p in NN$ 
  - $Y in (n, p), X in (n, a), A in (a, b), B in (b, p)$
  - $s(A): A mapsto argmin(B) norm(Y - X A B)$
  - $ssel: A mapsto overline(s)(A) in s(A)$
  - $hat(Y) := X A ssel(A)$

  $
    norm(Y - hat(Y))^2 = norm(Y)^2 - norm(hat(Y))^2
  $
] <lemma:optimal_projection>
#proof[
  By definition of $ssel(A)$ being optimal, we have that $hat(Y)$ is the orthogonal projection of $Y$ onto the space spanned by the columns of $X A$. Hence $Y - hat(Y)$ is orthogonal to $hat(Y)$ and the Pythagorean theorem gives the result.
]

#theorem[
  For:
  - $n, p, a, b, p in NN$ 
  - $Y in (n, p), X in (n, a), A in (a, b), B in (b, p)$
  - $s(A): A mapsto argmin(B) norm(Y - X A B)$
  - $ssel: A mapsto overline(s) in s(A)$

  We have that:
  $
      argmin(A\,B) norm(Y - X A B) = union.big_(A^*) {A^*} times s(A^*) | A^* in argmax(A) norm(X A ssel(A))
  $
] <theorem:separable_optimization>
#proof[
  $ argmin(A\,B) norm(Y - X A B)
  &= argmin(A) norm(Y - X A B), B in s(A) $

  Hence:
  $ argmin(A) norm(Y - X A B)
  &= argmin(A) norm(Y - X A ssel(A)) \
  #flushl[By @lemma:optimal_projection:]
  &= argmin(A) norm(Y)^2 - norm(hat(Y))^2 \
  &= argmax(A) norm(X A ssel(A)) \
  &= union.big_(A^*) {A^*} times s(A^*) | A^* in argmax(A) norm(X A ssel(A))
  $
]

#theorem[
   For:
   - $norm(.)$ a Euclidean norm
   - $A in (n, m)$
   - $X in (m, n)$
    We have that:
    $
        norm(A X) = norm((trans(A) A)^(1/2) X)
    $
] <theorem:rimannian_norm>
#proof[
  $
    norm(A X)^2 &= scalarp(A X, A X) \
    &= scalarp(trans(A) A X, X) \
    &= scalarp((trans(A) A)^(1/2) (trans(A) A)^(1/2) X, X) \
    &= norm((trans(A) A)^(1/2) X)^2
  $
]
