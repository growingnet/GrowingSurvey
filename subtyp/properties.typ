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
    - $f: F -> E$ scaling equivariant #ie ($forall x in F, forall lambda in RR, f(lambda x) = lambda f(x)$)
    - $y in E$.

    If $(exists x in F, scalarp(f(x), y) != 0)$ we have that:
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

  - By definition: $R subset I$.
  - Let show that $I subset R$, let $d^* in I$, let show that $norm(f(d^*)) = 1$.


    Let $x in F$ with $scalarp(f(x), y) != 0$ (exists by hypothesis). Let $x' := sign(scalarp(f(x), y))x$. Then $scalarp(f(x'), y) > 0$.
    By definition of $d^*$ being optimal in $I$,
    $scalarp(y, f(d^*)) >= scalarp(y, f(x')) > 0$ and therefore $f(d^*) != 0$.
    Let $lambda := 1 / norm(f(d^*)) > 0$ as $abs(lambda) <= 1$:
    $ scalarp(y, f(d^*)) >= lambda scalarp(y, f(d^*)) = scalarp(y, f(lambda d^*)) $ by scaling equivariance of $f$.
    By maximality of $d^*$ in $I$, this is an equality hence $norm(f(d^*)) = 1$.
  Therefore $d^* in R$ and $I subset R$.

  For the second equality, we can do the same reasoning using that $norm(y - f(x))^2 = norm(y)^2 - 2 scalarp(y, f(x)) + norm(f(x))^2$.
]


#theorem[
    For:
    - $E$ a pre-Hilbert space, 
    - $F subset E$ a non empty set stable by scaling #ie ($forall x in F, forall lambda in RR, lambda x in F$)
    - $f: F -> E$ scaling equivariant #ie ($forall x in F, forall lambda in RR, f(lambda x) = lambda f(x)$)
    - $y in E$.

    We have that:
    $ 
        argmin(x in F) norm(y - f(x)) = {scalarp(y, d^*) d^* |  d^* in argmax(d in F | norm(f(d)) <= 1) scalarp(y, f(d)) }
     $ <eq:fixed_norm_optimisation_equivalence>
] <lemma:argmin_norm_to_argmax_scalarp>

#proof[
- If $forall x in F, scalarp(f(x), y) = 0$, then both sides of <eq:fixed_norm_optimisation_equivalence> equal ${0}$.
- If $exists x in F, scalarp(f(x), y) != 0$, by @lemma:argument_scaling, we have that in left hand side we can add $norm(f(x)) != 0$ and in the right hand side of <eq:fixed_norm_optimisation_equivalence>, we can replace $<= 1$ by $= 1$.
  Let's proceed by double inclusion.
  $ argmin(x in F | norm(f(x)) != 0) norm(y - f(x)) &= argmin(x in F) (norm(y)^2 - 2scalarp(y, f(x))) + norm(f(x))^2 \
  &= argmin(x in F | norm(f(x)) != 0) ( - 2scalarp(y, f(x)) + norm(f(x))^2 )\
  &= argmin(x in F | norm(f(x)) != 0) ( - 2scalarp(y, norm(f(x)) f(x) / norm(f(x))) + norm(f(x))^2 ) \
  #flushl[As $f$ is scaling equivariant:]
  &= argmin(x in F | norm(f(x)) != 0) ( - 2 norm(f(x)) scalarp(y, f(x / norm(f(x)))) + norm(f(x))^2 ) \
  &= argmin(x in F | norm(f(x)) != 0) ( - 2 t scalarp(y, f(d)) + t^2 )
  $
  with $d := x / norm(f(x)) in F$ and $t := norm(f(x)) >= 0$.
 The solution over $t$ is achieved at $t = scalarp(y, f(d))$. Hence we get:
  $ argmin(x in F | norm(f(x)) != 0) norm(y - f(x)) 
  &= argmin(x in F | norm(f(x)) != 0) ( - scalarp(y, f(d))^2 )\
  &= argmax(x in F | norm(f(x)) != 0) scalarp(y, f(d)) \
  &= { scalarp(y, d^*) d^* |  d^* in argmax(d in F | norm(f(d)) = 1) scalarp(y, f(d)) }
  $
]

#corollary[
    For:
    - $E$ a pre-Hilbert space, 
    - $F subset E$ a non empty set stable by scaling #ie ($forall x in f, forall lambda in RR, lambda x in F$)
    - $f: F -> E$ scaling equivariant #ie ($forall x in F, forall lambda in RR, f(lambda x) = lambda f(x)$)
    - $y in E$.

    We have that:
    $ 
        argmin(x in F) norm(y - f(x)) prop argmax(d in F|norm(f(d)) <= 1) scalarp(y, f(d)) 
     $
] <corollary:argmin_norm_to_argmax_scalarp>

#proof[
  Direct consequence of @lemma:argmin_norm_to_argmax_scalarp.
]

#let ssel = [$overline(s)$]
#lemma[
  For:
  - $n, p, a, b, p in NN$ 
  - $Y in (n, p), X in (n, a), A in (a, b), B in (b, p)$
  - $s(A): A mapsto argmin(B) norm(Y - X A B)$
  - $ssel: A mapsto overline(s) in s(A)$
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
   - $X in (m, n$
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
