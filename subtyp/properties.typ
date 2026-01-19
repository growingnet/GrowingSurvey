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

    We have that:
    $ 
        (exists x in F, scalarp(f(x), y) != 0) => argmax(d in F|norm(f(d)) <= 1) scalarp(y, f(d)) = argmax(d in F|norm(f(d)) = 1) scalarp(y, f(d))
    $
] <lemma:argument_scaling>
#proof[
  /*
  Let $I := argmax(d in F|norm(f(d)) <= 1) scalarp(y, f(d))$ and $J := argmax(d in F|norm(f(d)) = 1) scalarp(y, f(d))$.

  - By definition: $J subset I$.
  - Let show that $I subset J$, let $d^* in I$, let show that $norm(f(d^*)) = 1$.


    Let $x in F$ with $scalarp(f(x), y) != 0$ (exists by hypothesis). Let $lambda := sign(scalarp(f(x), y)) / norm(f(x))$. Then $norm(f(lambda x)) = 1$.
    By definition of $d^*$ being optimal in $I$:
    $ scalarp(y, f(d^*)) >= scalarp(y, f(x)) $ 
    contradicting the optimality of $d^*$.
  
  
  
  
  
  let $x in F$ with $norm(f(x)) = 1$. Let's show that $scalarp(y, f(d^*)) >= scalarp(y, f(x))$.
  */
]


#theorem[
    For:
    - $E$ a pre-Hilbert space, 
    - $F subset E$ a non empty set stable by scaling #ie ($forall x in F, forall lambda in RR, lambda x in F$)
    - $f: F -> E$ scaling equivariant #ie ($forall x in F, forall lambda in RR, f(lambda x) = lambda f(x)$)
    - $y in E$.

    We have that:
    $ 
        argmin(x in F) norm(y - f(x)) = {scalarp(y, d^*) d^* |  d^* in argmax(d in F|norm(f(d)) <= 1) scalarp(y, f(d)) }
     $ <eq:fixed_norm_optimisation_equivalence>
] <lemma:argmin_norm_to_argmax_scalarp>

#proof[
  /*
   Denote $A := argmin(X in F) norm(Y - X)$ and $B := {scalarp(Y, d^*) d^* | d^* in argmax(d in F | norm(d) = 1) scalarp(Y, d)}$.

    We prove $A = B$ by double inclusion.

    *($B subset A$):* Let $X^* in B$. Then there exists $d^* in argmax(d in F | norm(d) = 1) scalarp(Y, d)$ such that $X^* = scalarp(Y, d^*) d^*.$
    Let $X in F$, we show $norm(Y - X^*) <= norm(Y - X)$.

    + *Case 1:* $scalarp(Y, d^*) = 0$ hence $X^* = 0$.
      + *Subcase 1a:* $X = 0$. Then $X = X^* = 0$ and the inequality holds.
      + *Subcase 1b:* $X != 0$. By maximality of $d^*$, $0 = scalarp(Y, d^*) >= scalarp(Y, X / norm(X))$. Hence:
    $ norm(Y - X)^2 = norm(Y)^2 - 2 scalarp(Y, X) + norm(X)^2 >= norm(Y)^2 ouset(=, X^*  =0) norm(Y - X^*)^2 $.
    + *Case 2:* $scalarp(Y, d^*) != 0$ hence $d^* != 0$. 
      - Let's show that $norm(d^*) = 1$:
      As $norm(d^*) <= 1$,
      $scalarp(Y, d^* / norm(d^*)) >= scalarp(Y, d^*)$ by maximality of $d^*$ this is an equality hence $norm(d^*) = 1$.
      - Let's show that $norm(Y - X)^2 >= norm(Y)^2 - 2 norm(X) max_(d in F | norm(d) = 1) scalarp(Y, d) + norm(X)^2$:
        - If $X = 0$ it is immediate.
        - If $X != 0$,
        $ norm(Y - X)^2 &= norm(Y)^2 - 2 scalarp(Y, X) scalarp(Y, d) + norm(X)^2\
        &= norm(Y)^2 - 2 norm(X) scalarp(Y, X/norm(X)) scalarp(Y, d) + norm(X)^2\
        &>=norm(Y)^2 - 2 norm(X) max_(d in F | norm(d) = 1) scalarp(Y, d) + norm(X)^2 $
        Finally we have as $d^*$ is optimal in a larger set ($norm(d) <= 1$), it is also optimal in the smaller set ($norm(d) = 1$):
        $ norm(Y - X)^2 
      &>= norm(Y)^2 - 2 norm(X) scalarp(Y, d^*) + norm(X)^2 \
      &>= norm(Y)^2 + min_(Z in F)[ - 2 norm(Z) scalarp(Y, d^*) + norm(Z)^2] \
      #flushl[As only $||Z||$ matters:]
      &= norm(Y)^2 + min_(t >= 0)[ - 2 t scalarp(Y, d^*) + t^2] \
      #intertext[The minimum is achieved at $t = scalarp(Y, d^*)$:]#<equate:revoke>\
      &= norm(Y)^2 - scalarp(Y, d^*)^2 \
      &= norm(Y)^2 - 2 scalarp(Y, d^*)^2 + scalarp(Y, d^*)^2 \
      &= norm(Y - X^*)^2 
      $.

    In all cases, $norm(Y - X^*) <= norm(Y - X)$. Since $X in F$ was arbitrary, $X^* in A$.

    *($A subset B$):* 
    For $alpha >= 0$ such that $norm(alpha d) = norm(X^*)$
    $ 
      norm(Y - X^*) &<= norm(Y - alpha d) \
      <=> norm(Y)^2 - 2 scalarp(Y, X^*) + norm(X^*)^2 &<= norm(Y)^2 - 2 alpha scalarp(Y, d) + norm(alpha d)^2 \
      <=> scalarp(Y, X^*) &>= alpha scalarp(Y, d)
    $
    
    Let $X^* in A$. We show $X^* in B$.

    + *Case 1:* $X^* = 0$.
      Let $d in F$ with $norm(d) <= 1$. Let $d^* = X^* in F$, we show that $scalarp(Y, d^*) >= scalarp(Y, d)$.  
      Using the inequality above with $alpha = 0$:
      $scalarp(Y, 0) = 0 >= scalarp(Y, d)$.
      Hence $d^* := 0 in argmax(d in F | norm(d) <= 1) scalarp(Y, d)$ and $X^* = 0 = scalarp(Y, d^*) d^* in B$.

    + *Case 2:* $X^* != 0$. Let $d in F$ with $norm(d) <= 1$. Let $d^* = X^* / norm(X^*) in F$, we show that $scalarp(Y, d^*) >= scalarp(Y, d)$. 
    
      + *Subcase 2a:* $norm(d) = 1$.
      With $alpha = norm(X^*)$ we get:
      $ scalarp(Y, X^*) >= norm(X^*) scalarp(Y, d)
      <=> scalarp(Y, d^*) >= scalarp(Y, d) $. Hence $d^* in argmax(d in F | norm(d) <= 1) scalarp(Y, d)$ and $X^* = scalarp(Y, d^*) d^* in B$.

      Since $d in F$ with $norm(d) = 1$ was arbitrary, $d^* in argmax_(d in F | norm(d) <= 1) scalarp(Y, d)$. Therefore $X^* = scalarp(Y, d^*) d^* in B$.
    */
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
