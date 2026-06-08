#import "../typst/commands.typ": *


= Notations

== Linear Algebra

- $scalarp(.,.)$ is a scalar product and $norm(.)$ the associated norm.
- $frob(.)$ is the Frobenius norm.
- $times_k$ is to indicate multiplication over a common dimension $k$.
- $pinv(.)$ is the Moore-Penrose pseudoinverse.

== Data and Model

We consider a data distribution $datadist$, a per-data-point loss function $ell: hat(y) times y |-> ell(hat(y), y)$, and a model $f: X times theta |-> f_theta (x) = hat(y)$ with parameters $theta$ mapping inputs $X$ to predictions $hat(y)$. The overall loss is:
$ loss(f_theta) = expectation((x, y) ~ datadist) [ell(f_theta (x), y)] $

== Network Architecture

We consider a feedforward neural network with layers indexed by $l$. For a data point $x$, the forward pass through consecutive layers is:
$ x ouset(->, postact(l: l- 2)) postact(l: l- 2)(x) ouset(->, Layer(W: W_(l-1))) preact(l: l - 1)(x) ouset(->, sigma) postact(l:l-1)(x) ouset(->, Layer(W: W_(l))) preact(l: l)(x) -> f(x) $

For readability, we drop layer indices when unambiguous:
$ x ouset(->, postact(l: - 2)) postact(l: - 2)(x) ouset(->, Layer(W: W_(-1))) preact(l: - 1)(x) ouset(->, sigma) postact(l:-1)(x) ouset(->, Layer(W: W)) preact()(x) -> f(x) $

== Dimensions and Batched Notation

The size of each layer $l$ is $C_l$ (written as $cm$, $cmid$, $cp$ for layers $l-2$, $l-1$, $l$ respectively). The number of data points is $n$.

For a single sample: $postact(l: -2)(x) in (cm, 1) = (cm)$.

For $n$ batched samples, we stack row-wise:
$ Postact(l: -2) = vec(trans(postact(l: -2)(x_1)), dots, trans(postact(l: -2)(x_n))) in (n, cm) $

The linear layer acts as:
$ Layer()(postact(l: -2)(x)) &= W_(l-1) times_(cm) postact(l: -2)(x) in (cmid, 1)\
Layer()(bold(Postact(l: -2))) &= Postact(l: -2) times_(cm) trans(W) in (n, cmid) $

== Gradient Notation

The gradient of the loss with respect to pre-activations, stacked row-wise:
$ Gradpreact = vec(trans(nabla_(preact()(x_1)) ell(f(x_1))), dots, trans(nabla_(preact()(x_n)) ell(f(x_n)))) in (n, cp) $

== Neuron Addition

We aim to expand the intermediate representation $preact(l: -1)$ and $postact(l: -1)$ by adding $cext$ new neurons. This is done by adding fan-in weights $Fanin = vec(fanin_1, dots, fanin_k ) in (cext, cm)$ and fan-out weights $Fanout = mat(fanout_1, dots, fanout_k) in (cp, cext)$:

$ postact(l: - 2)(x) ouset(->, Layer(W: Fanin)) preactext(x) ouset(->, sigma) postactext(x) ouset(->, Layer(W: Fanout)) deltas(x) $

The change to the pre-activation at layer $l$ is:
$ preact() <- preact() + deltas $
with $deltas = Layer(W: Fanout) compose sigma compose Layer(W: Fanin) compose postact(l: -2)$.

== Key Statistics

Several statistics computed over the dataset are used across all methods:

#definition[
  The *activation covariance* at layer $l$ is:
  $ covpostact_(l) := Edata[postact(l: l)(x) times_1 transp(postact(l: l)(x))] approx 1/ n trans(Postact(l: l)) times_n Postact(l: l) in (C_l, C_l) $
]

#definition[
  The *gradient-activation cross-covariance* with activation at layer $l$ is:
  $ B_(l) := Edata[(-gradpreact()(x)) times_1 transp(postact(l: l)(x))] approx - 1/ n trans(Gradpreact) times_n Postact(l: l) in (cp, C_l) $
]

#definition[
  The *gradient covariance* is:
  $ covgrad := Edata[transp((partial f) / (partial preact()) (x)) times_(C_L) (partial f) / (partial preact()) (x)] in (cp, cp) $
]

== Residual Gradient (Bottleneck)

To avoid redundancy between added neurons and existing ones, several methods project the gradient orthogonally to the space spanned by existing neurons' activity. The idea is to find the optimal update $dW^*$ to the existing weights $W$ and then consider only the residual gradient that cannot be addressed by this update.

#lemma[
  The optimal weight update $dW^*$ that minimizes the residual gradient is:
  $ dW^* := argmin(dW) frob(-gradpreact() - Layer(W: dW) compose postact(l:-1) ) = B_(-1) times_(cmid) pinv(covpostact_(-1)) $
]<lemma:optimal_dW>

#proof[
  We solve it for a batch of data points:
  $dW^* = argmin(dW) frob(- Gradpreact - Postact(l:-1) times_(cmid) trans(dW))$
  This is a least-squares problem:
  $ trans(dW^*) = pinvp(trans(Postact(l:-1)) times_n Postact(l:-1)) times_cmid trans(Postact(l: -1)) times_n (- Gradpreact)  =   pinv(covpostact_(-1)) times_(cmid) trans(B_(-1))$
]

#definition[
  The *residual gradient* (or *bottleneck*) is the residual after subtracting the contribution of the optimal weight update $dW^*$:
  $ bottleneck(x) := -gradpreact()(x) - Layer(W: dW^*)(postact(l: -1)(x)) in (cp) $
  
  In batched form:
  $ Bottleneck := - Gradpreact - Postact(l:-1) times_(cmid) covpostact_(-1)^(-1) times_(cmid) trans(B_(-1)) in (n, cp) $
]

#proposition[
  The residual gradient $Bottleneck$ is orthogonal to existing activations:
  $ trans(Postact(l:-1)) times_n Bottleneck = 0 in (cmid, cp) $
]<prop:bottleneck_orthogonality>
#proof[
  By construction, $bottleneck$ is the residual of the least-squares projection of $-gradpreact()$ onto the space spanned by $postact(l:-1)$. The residual is orthogonal to the projection space.
]


= Existing Methods

This section presents each method with its motivation and derives its simplified objective function.

== TINY

=== Motivation

The TINY @verbockhavenGrowingTinyNetworks2024 method seeks to find new neurons whose contribution $deltas$ most directly reduces the loss. Using a first-order Taylor expansion:
$ loss(preact() + deltas) = loss(preact()) + scalarp(nabla_(preact()) loss(preact()), deltas) + o(norm(deltas)) $

Hence TINY with no projection aims to align $deltas$ with the negative gradient $-nabla_(preact()) loss(preact())$. To avoid redundancy with existing neurons, TINY with projection aligns $deltas$ with the residual gradient $bottleneck$.

=== Objective Formulation

TINY approximates $deltas(x) approx sigma'(0) dot Fanout times_(cext) Fanin times_(cm) postact(l: -2)(x)$ (linearizing $sigma$ around $0$). Dropping the constant $sigma'(0)$, the objective becomes:

#proposition[
  *TINY optimization problem (with projection).* The TINY method solves:
  $ argmin(Fanin\, Fanout) frob(Bottleneck - Postact(l:-2) times_(cm) trans(Fanin) times_(cext) trans(Fanout)) $ <eq:tiny_projection_optimization>
  
  Without projection, replace $Bottleneck$ with $- Gradpreact$.
]
#proof[
  We maximize the first-order loss decrease, by @corollary:argmin_norm_to_argmax_scalarp:
  $ argmin(Fanin\,Fanout\; norm(deltas) <= 1)scalarp(nabla_(preact()) loss(preact()), deltas)
  prop argmin(Fanin\,Fanout) norm(-nabla_(preact()) loss(preact())-  deltas)
  $
  Then substituting the linearized $deltas$ and using batched notation gives the result.
]
== GradMax

=== Motivation

GradMax @evciGradMaxGrowingNeural2021 takes a different approach: initialize new neurons with zero contribution ($deltas = 0$ by setting $Fanin = 0$), then maximize the gradient magnitude that will be available for subsequent training.

=== Objective Formulation

With $Fanin = 0$ and $sigma(0) = 0$, we have $postactext = 0$, so $nabla_Fanout loss(f) = 0$. The loss decrease after one gradient step on $(Fanin, Fanout)$ is:
$ loss(f_(Fanin + dFanin)) approx loss(f) - frob(nabla_Fanin loss(f))^2 - frob(nabla_Fanout loss(f))^2 $
As $nabla_Fanout loss(f) = 0$ at initialization, GradMax maximizes $frob(nabla_Fanin loss(f))$. 

#proposition[
  *GradMax optimization problem.* GradMax solves:
  $ Fanout^* = argmax(frob(Fanout)^2 <= cext) frob(nabla_Fanin loss(f)) $
  such that $trans(Fanout) times_cext Fanout = I_cext$. 
]

=== Simplified Objective

#lemma[
  With $Fanin = 0$ and $sigma'(0) = 1$:
  $ nabla_Fanin loss(f) = trans(Fanout) times_(cp) Edata[gradpreact()(x) times_1 trans(postact(l: -2)(x))] = -trans(Fanout) times_(cp) B_(-2) $
]

#proposition[
  *GradMax reduced objective.* The GradMax optimization reduces to:
  $ cal(J)_("GradMax")(Fanout) := frob(trans(B_(-2)) times_(cp) Fanout)^2 $ <eq:gradmax_reduced>
  such that $trans(Fanout) Fanout = I_cext$.
  
  The optimal $Fanout^*$ are the leading left-singular vectors of $B_(-2)$.
]<prop:gradmax_reduced>

=== GradMax-Opt

GradMax-Opt is the same, but instead of using SVD it uses gradient descent. This allows switching the roles of $Fanin$ and $Fanout$: setting $Fanout = 0$ and maximizing $frob(nabla_Fanout loss(f))$.

== SENN

=== Motivation

SENN @mitchellSelfExpandingNeuralNetworks2024 extends GradMax by considering *natural gradient* descent instead of standard gradient descent. It also avoids redundancy by maximizing the _increase_ in natural gradient norm after neuron addition. They choose to fix $Fanout = 0$ at initialization to ensure $deltas = 0$ (unlike GradMax that fixes $Fanin = 0$).

The natural gradient step is $vec(dFanout, dW) prop - F^(-1) nabla_vec(Fanout, W) loss(f)$ where $F$ is the Fisher information matrix with respect to $vec(Fanout, W)$, the first order equation becomes (also because $nabla_Fanin loss(f) = 0$):
$ loss(f_(W + dW, Fanout + dFanout)) approx loss(f) - scalarp( nabla_vec(Fanout, W)loss(f), F^(-1) nabla_vec(Fanout, W) loss(f))_2 $
Hence they want to maximize $etasenn(vec(Fanout, W)) := scalarp( nabla_vec(Fanout, W)loss(f), F^(-1) nabla_vec(Fanout, W) loss(f))_2$.

=== Objective Formulation

Using the KFAC @dangelKroneckerfactoredApproximateCurvature2025 approximation $F approx covgrad times.o covpostact_(-1)$ for the Fisher information matrix:

#definition[
  The *SENN criterion* measures the natural gradient norm:
  $ etasenn(vec(Fanout, W)) &:= scalarp( nabla_vec(Fanout, W)loss(f), F^(-1) nabla_vec(Fanout, W) loss(f))_2\
  #flushl[Using KFAC:]
  &= scalarp( nabla_vec(Fanout, W) loss(f) (covpostact^"conc"_(-1))^(-1), covgrad^(-1) nabla_vec(Fanout, W) loss(f))_2
   $
  where:
  - $covpostact^"conc"_( -1)$ is the covariance of concatenated activations $vec(postactext, postact(l:-1))$
]

SENN maximizes the increase $Delta etasenn := etasenn(vec(Fanout, W)) - etasenn(W)$.

=== Simplified Objective

SENN uses a tractable lower bound $Delta etasenn' <= Delta etasenn$ involving the residual gradient.

#definition[
  The *extended activation covariance* (using exact activations):
  $ covpostact_(-1)^("ext") := Edata[postactext(x) times_1 trans(postactext(x))] in (cext, cext) $
]

#definition[
  The *residual gradient-activation cross-covariance* (using exact activations):
  $ partial Fanout := Edata[bottleneck(x) times_1 trans(postactext(x))] in (cp, cext) $
]

#proposition[
  *SENN reduced objective.* The SENN lower bound objective is
  $etasenn(Fanout)$ but computing the gradient of $Fanout$ backpropagating only the residual gradient (hence the definition of $partial Fanout$ the pseudo gradient of $Fanout$):
  $ cal(J)_("SENN")(Fanin) &:= scalarp(partial Fanout times_cext pinv(covpostact_(-1)^("ext")), covgrad^(-1) times_cp partial Fanout)_2\
  &= frob(isqrtS times_cp partial Fanout times_cext isqrtAext)^2
   $ <eq:senn_reduced>
]<prop:senn_reduced>


== NeST

=== Motivation

NeST @daiNeSTNeuralNetwork2019 considers sparse networks where connections are added incrementally. NeST provides criteria for both *connection activation* (adding a connection in an existing layer) and *neuron addition* (adding a new neuron with a single connection pair).

=== Connection Activation

NeST considers sparse layers where $W$ is sparse. To choose which connection to add, they look at which connection between neuron $i$ in layer $l-1$ and neuron $j$ in layer $l$ would maximally decrease the loss if added and optimized with a gradient step:
$ loss(f_(W + dW[i, j])) = loss(f) + scalarp(nabla_(W[ i, j]) loss(f), dW[ i, j]) + o(frob(dW[ i, j])) $

When choosing $dW[ i, j] prop - nabla_(W[ i, j]) loss(f)$, this becomes:
$ loss(f_(W + dW[i, j])) = loss(f) - frob(nabla_(W[ i, j]) loss(f))^2 + o(frob(dW[ i, j])) $

Note that NeST justifies this choice with Hebbian theory and considers $abs(nabla_(W[ i, j]) loss(f))$.

#proposition[
  *NeST connection activation.* For adding a connection in an existing layer, NeST selects:
  $ i^*, j^* = argmax(i\, j) abs(B_(-1))[j, i] $
]<prop:nest_connection>

=== Neuron Addition

When adding a new neuron, NeST only adds a few connections between pairs of neurons $(i, j)$ with neuron $i$ in layer $l-2$ and neuron $j$ in layer $l$. They set $Fanin$ and $Fanout$ to zero except for the values at indices $(i)$ and $(j)$ respectively. This gives:
$ deltas(x)[j] = Fanout[j] sigma(Fanin[i] postact(l: -2)(x)[i]) approx Fanout[j] sigma'(0) Fanin[i] postact(l: -2)(x)[i] $

Dropping the constant $sigma'(0)$, they optimize the decrease in loss after the addition:
$ loss(preact() + deltas) 
&= loss(preact()) + scalarp(nabla_(preact()[j]) loss(preact()), deltas[j]) + o(norm(deltas[j])) \
&approx loss(preact()) - nabla_(preact()[j]) loss(preact()) dot Fanout[j] dot Fanin[i] dot postact(l: -2)[i] $

Hence they maximize $nabla_(preact()[j]) loss(preact()) dot postact(l: -2)[i] dot Fanout[j] dot Fanin[i]$ under the constraint that $abs(Fanout[j] dot Fanin[i])$ is small.

#proposition[
  *NeST neuron addition.* For adding a new neuron, NeST selects:
  $ i^*, j^* = argmax(i\, j) abs(B_(-2))[j, i] $
  to add a single connection, or the pairs in the top $beta$ fraction to add several connections.
]<prop:nest_objective>

=== Initialization

Once $(i^*, j^*)$ is chosen, NeST initializes the weights so that the change $deltas[j]$ is similar to that created by a gradient step on a virtual connection between $postact(l: -2)[i]$ and $preact()[j]$, yielding a loss decrease of $frob(B_(-2)[j^*, i^*])^2$. The sign is randomized:

#proposition[
  *NeST initialization.* Once $(i^*, j^*)$ is selected, NeST initializes:
  $
  epsilon &~ "Rademacher" #ie "Uniform"({-1, 1}) \
  Fanin[i^*] &= epsilon dot "sign"(B_(-2)[j^*, i^*]) dot sqrt(abs(B_(-2)[j^*, i^*])) \
  Fanout[j^*] &= epsilon dot sqrt(abs(B_(-2)[j^*, i^*]))
  $
  
  All other entries of $Fanin$ and $Fanout$ are zero.
]<prop:nest_init>


== NORTH

=== Motivation

NORTH @maileWhenWhereHow2022 takes a geometric perspective: new neurons should add *new directions* in activation space, orthogonal to existing activations.

=== Objective Formulation

NORTH seeks $fanin$ such that the new activations $Postactext = sigma(Postact(l:-2) trans(fanin))$ are orthogonal to existing ones  which is equivalent to lie in $ker(trans(Postact(l:-1)))$.

#proposition[
  *NORTH-Pre construction.* Let $V in (n, n - cmid)$ be an orthonormal basis of $ker(trans(Preact(l:-1)))$ (computed via SVD). For random directions $R in (n - cmid, cext)$:
  $ trans(Fanin) = covpostact_(-2)^(-1) times_(cm) trans(Postact(l:-2)) times_n V times_(n - cmid) R $ <eq:north_proposition>
]<prop:north_construction>

==== Justification

They use the approximation $sigma approx "Identity"$ to relax the problem to replace $Postactext$ with $Preactext =  Postact(l:-2) times_(cm) trans(fanin)$ and $ker(trans(Postact(l:-1)))$ with $ker(trans(Preact(l:-1)))$.

First they compute a basis $V in (n, n - cmid)$ of $ker(trans(Preact(l:-1)))$ using SVD. Then they generate random combinations of the basis vectors $V times_(n - cmid) r$ for random $r$ as candidates for $Preactext$. For each candidate they solve for $fanin$ such that $Postact(l:-2) times_(cm) trans(fanin) = V times_(n - cmid) r$ which gives:
$ trans(fanin) = pinvp(Postact(l:-2)) times_n V r $

Or for a batched version with $cext$ candidates $R in (n - cmid, cext)$ with orthogonal columns:
$ trans(Fanin) &= pinvp(Postact(l:-2)) times_n V times_(n - cmid) R in (cm, cext) \
&= pinvp(trans(Postact(l:-2)) times_n Postact(l:-2)) times_(cm) trans(Postact(l:-2)) times_n V times_(n - cmid) R \
&prop covpostact_(-2)^(-1) times_(cm) trans(Postact(l:-2)) times_n V times_(n - cmid) R
$
($prop$ because we skip the $1/n$ factor.)
Then they select the best candidates according to the orthogonality of $Postactext = sigma(Postact(l:-2)  trans(fanin) )$ to $Postact(l:-1)$ using this time the exact activation function $sigma$.

= Unified Framework

We now show that all methods can be understood as special cases of a common optimization objective.

== General Objective

#theorem[
  *Unified objective for neuron addition.* All neuron addition methods studied in this document can be derived from the following optimization problem:
  $ Fanin^*, Fanout^*
  &= argmax(Fanin\, Fanout\, frob(sqrtAext times_(cext) trans(Fanout) times_cp sqrtS) <= 1) scalarp(T times_cp isqrtS, 1/n Postactext times_(cext) trans(Fanout) times_cp sqrtS) #<eq:unified_objective_scalarp> \
  #intertext[if we linearize $sigma$ around $0$:]#<equate:revoke>\
  &prop argmin(Fanin\, Fanout) frob(T times_cp isqrtS - sigma(Postact(l:-2) times_(cm) trans(Fanin)) times_(cext) trans(Fanout) times_cp sqrtS) #<eq:unified_objective_norm> 
  $ <eq:unified_objective>
  
  where:
  - $T in (n, cp)$ is the target (negative gradient $- Gradpreact$ or residual gradient $Bottleneck$)
  - $covgrad in (cp, cp)$ is the gradient weighting metric
  - $sigma$ is an activation function
  - Additional constraints may be imposed on $Fanin$ and $Fanout$

  The following table summarizes the specialization for each method:
  
  #figure(
    table(
      columns: 9,
      stroke: 0.5pt,
      align: center,
      table.header(
        [*Method*], [$T$], [$covpostact_(-1)^"ext"$], [$covgrad$], [*Extra constraints*], [$Fanin$], [$Fanout$], [$postactext perp postact(l:-1)$], [$sigma$]
      ),
      [Full], [$Bottleneck$], [$covpostact_(-1)^"ext"$], [$covgrad$], [$emptyset$], [$Fanin^*$], [$Fanout^*$], [#sym.checkmark], [Any],
      [TINY (proj.)], [$Bottleneck$], [$Fanin covpostact_(-2) trans(Fanin)$], [$I_(cp)$], [$emptyset$], [$Fanin^*$], [$Fanout^*$], [#sym.checkmark], [Identity],
      [TINY (no proj.)], [$- Gradpreact$], [$Fanin covpostact_(-2) trans(Fanin)$], [$I_(cp)$], [$emptyset$], [$Fanin^*$], [$Fanout^*$], [#sym.times], [Identity],
      [GradMax], [$- Gradpreact$], [$Fanin trans(Fanin)$], [$I_(cp)$], [$Fanin trans(Fanin)=I_(cext); trans(Fanout) Fanout = I_(cext)$], [$0$], [$Fanout^*$], [#sym.times], [Any],
      [SENN], [$Bottleneck$], [$covpostact_(-1)^"ext"$], [$covgrad$], [$emptyset$], [$Fanin^*$], [$0$], [#sym.checkmark], [Any],
      [NeST], [$- Gradpreact$], [$Fanin  trans(Fanin)$], [$I_(cp)$], [$norm(Fanin)_0 = norm(Fanout)_0 = 1$], [$Fanin^*$], [$Fanout^*$], [#sym.times], [Identity],
    ),
    caption: [Neuron addition methods as special cases of the unified objective @eq:unified_objective.]
  ) <tab:comparison>

Notes:
- Assuming $covpostact_(-1)^"ext" = Fanin covpostact_(-2) trans(Fanin)$ in @eq:unified_objective_scalarp is equivalent to linearizing $sigma$ around $0$ in @eq:unified_objective_norm.
- The GradMax assumption $covpostact_(-1)^"ext" = Fanin trans(Fanin)$ is like assuming the input data is whitened in addition to linearizing $sigma$ around $0$.
- The equivalence between the two optimization problems is correct either if we use the first order approximation of $sigma$ or if we allow to have different proportionality constants for $Fanin$ and $Fanout$.
]<thm:unified_objective>

#proof[
  The derivations for each method are provided in the following sections.
  We only prove the equivalence between the minimization and maximization forms. By @lemma:argmin_norm_to_argmax_scalarp from the preliminaries, we have:
  $ Fanin^*, Fanout^* 
  &= argmin(Fanin\, Fanout) frob(T times_cp isqrtS - sigma(Postact(l:-2) times_(cm) trans(Fanin)) times_(cext) trans(Fanout) times_cp sqrtS) \
  &= argmin(Fanin\, Fanout) 1/n frob(T times_cp isqrtS - Postactext times_(cext) trans(Fanout) times_cp sqrtS) \
  #intertext[Linearizing $sigma$ around $0$, $Postactext = Postact(l:-2) times_(cm) trans(Fanin)$ is linear in $Fanin$, so $(Fanin, Fanout) |-> 1/n Postactext trans(Fanout) sqrtS$ is homogeneous of degree $2$ and @corollary:argmin_norm_to_argmax_scalarp applies:]#<equate:revoke>\
  &prop argmax(Fanin\, Fanout\, frob(1/sqrt(n) Postactext times_(cext) trans(Fanout) times_cp sqrtS) <= 1) scalarp(T times_cp isqrtS, 1/n Postactext times_(cext) trans(Fanout) times_cp sqrtS) \
  &= argmax(Fanin\, Fanout\, frob(sqrtAext times_(cext) trans(Fanout) times_cp sqrtS) <= 1) scalarp(T times_cp isqrtS, 1/n Postactext times_(cext) trans(Fanout) times_cp sqrtS)
  $

  the last step using @theorem:rimannian_norm together with $covpostact_(-1)^"ext" = 1/n trans(Postactext) times_n Postactext$. This equivalence is only needed for the norm-form methods, i.e. TINY, which assumes $sigma approx "Identity"$; GradMax, NeST and SENN are obtained directly from the maximization form @eq:unified_objective_scalarp.
]

== Derivation of Each Method

We now prove that each method can be derived from the unified objective @eq:unified_objective by appropriate specialization.

=== Derivation of TINY

#proposition[
  *TINY from unified objective.* Setting $covgrad = I_(cp)$ and $sigma approx "Identity"$ in @eq:unified_objective_norm yields the TINY optimization problem.
]<prop:tiny_derivation>

#proof[
  With $covgrad = I_(cp)$, we have $isqrtS = I_(cp)$. The unified objective becomes:
  $ argmin(Fanin\, Fanout) frob(T - sigma(Postact(l:-2) times_(cm) trans(Fanin)) times_(cext) trans(Fanout)) $
  
  Using the linear approximation $sigma approx "Identity"$ (which is equivalent to $covpostact_(-1)^"ext" = Fanin covpostact_(-2) trans(Fanin)$), this becomes:
    $
   argmin(Fanin\, Fanout) frob(T - Postact(l:-2) times_(cm) trans(Fanin) times_(cext) trans(Fanout)) $
  
  With $T = Bottleneck$, this is exactly @eq:tiny_projection_optimization. With $T = - Gradpreact$, this is TINY without projection.
]

=== Derivation of GradMax

#proposition[
  *GradMax from unified objective.* Setting $T <- - Gradpreact$, $covpostact_(-2) <- I_(cm)$, $covgrad <- I_(cp)$, with the constraint $trans(Fanout) Fanout = I_(cext)$, and then setting $Fanin = 0$ after optimization yields GradMax.
]<prop:gradmax_derivation>
This proof is largely inspired by the work from @verbockhavenSpottingExpressivityBottlenecks2025.

#proof[
  Starting from @eq:unified_objective_scalarp with $covgrad <- I_(cp)$ and $T <- - Gradpreact$, the objective is:
  $ argmax(Fanin\, Fanout\, frob((Fanin trans(Fanin))^(1/2) trans(Fanout)) <= 1)& scalarp(- Gradpreact, Postactext times_(cext) trans(Fanout)) $
  Using @theorem:rimannian_norm with $A <- trans(Fanin)$ we have that $frob((Fanin trans(Fanin))^(1/2) trans(Fanout)) = frob(trans(Fanin) trans(Fanout))$.
  In addition, we replace $Postactext$ with its linear approximation $Postact(l:-2) trans(Fanin)$. However this approximation is not a strong assumption as it is only used during backward at $sigma(Postact(l: -2) trans(Fanin)) = sigma(0)$ as GradMax set $Fanin = 0$. Therefore as long as $sigma'(0) = 1$ the approximation is exact. We get:

  $
  = argmax(frob(trans(Fanin) times_(cext) trans(Fanout)) <= 1)& scalarp(- Gradpreact, 1/n Postact(l:-2) trans(Fanin) times_(cext) trans(Fanout)) \
  = argmax(frob(trans(Fanin) times_(cext) trans(Fanout)) <= 1)&  scalarp(trans(1/n Postact(l:-2)) times_n (- Gradpreact), trans(Fanin) times_(cext) trans(Fanout)) \
  = argmax(frob(trans(Fanin) times_(cext) trans(Fanout)) <= 1)& scalarp(trans(B_(-2)), trans(Fanin) times_(cext) trans(Fanout))\
  #flushl[Using @corollary:argmin_norm_to_argmax_scalarp:]
  prop argmin(Fanin\, Fanout)& frob(trans(B_(-2)) - trans(Fanin) times_(cext) trans(Fanout))
  $
  
  This is equivalent to a low-rank approximation of $trans(B_(-2))$. By @theorem:separable_optimization, optimizing over $Fanout$ with $trans(Fanin) <- trans(Fanin^*)  = trans(B_(-2)) Fanout pinvp(trans(Fanout) Fanout) = trans(B_(-2)) Fanout$ gives:
  $
    &prop argmax(frob(Fanout)^2 <= cext) frob(trans(B_(-2)) Fanout trans(Fanout)) \
    #flushl[Using $trans(Fanout) Fanout = I_(cext)$:]
    &=argmax(frob(Fanout)^2 <= cext) frob(trans(B_(-2)) Fanout)
  $
  
  This is exactly the GradMax objective $cal(J)_("GradMax")(Fanout)$ from @eq:gradmax_reduced. Finally, setting $Fanin = 0$ after optimization matches GradMax's initialization.
]

=== Derivation of SENN

#proposition[
  *SENN from unified objective.* The SENN objective $cal(J)_("SENN")$ is recovered from the maximization form @eq:unified_objective_scalarp with $T = Bottleneck$ and the full gradient covariance $covgrad$, setting $Fanout = 0$ after optimization.
]<prop:senn_derivation>

#proof[
  We start from the maximization form @eq:unified_objective_scalarp with $T = Bottleneck$ and the full metric $covgrad$. Since $scalarp(Bottleneck times_cp isqrtS, X times_cp sqrtS) = scalarp(Bottleneck, X)$ for any $X$, the $covgrad$ factors cancel in the objective (the metric only enters through the constraint), which becomes
  $ argmax(Fanin\, Fanout\, frob(sqrtAext times_(cext) trans(Fanout) times_cp sqrtS) <= 1) 1/n scalarp(Bottleneck, Postactext times_(cext) trans(Fanout)) . $
  Fix $Fanin$ and let $M := sqrtAext times_(cext) trans(Fanout) times_cp sqrtS$, so the constraint reads $frob(M) <= 1$ and $trans(Fanout) = isqrtAext times_cext M times_cp isqrtS$. Moving $Postactext$ across the inner product brings out the cross-covariance $partial Fanout = 1/n trans(Bottleneck) times_n Postactext$, and since $isqrtAext$ and $isqrtS$ are symmetric,
  $ 1/n scalarp(Bottleneck, Postactext times_(cext) trans(Fanout))
  &= scalarp(1/n trans(Postactext) times_n Bottleneck, trans(Fanout)) = scalarp(trans(partial Fanout), trans(Fanout)) \
  &= scalarp(trans(partial Fanout), isqrtAext times_cext M times_cp isqrtS) \
  &= scalarp(isqrtAext times_cext trans(partial Fanout) times_cp isqrtS, M) , $
  whose maximum over $frob(M) <= 1$ is, by Cauchy–Schwarz (attained at $M prop isqrtAext trans(partial Fanout) isqrtS$),
  $ frob(isqrtAext times_cext trans(partial Fanout) times_cp isqrtS) = frob(isqrtS times_cp partial Fanout times_cext isqrtAext) = sqrt(cal(J)_("SENN")(Fanin)) $
  with $cal(J)_("SENN")$ as in @eq:senn_reduced. The outer maximization over $Fanin$ is thus $argmax(Fanin) cal(J)_("SENN")(Fanin)$, the SENN objective. As in @prop:senn_reduced the optimal $Fanout$ only serves to score $Fanin$; SENN keeps $Fanout = 0$ at initialization to preserve the function.
]


=== Derivation of NeST

#proposition[
  *NeST from unified objective.* Setting $T <- - Gradpreact$, $covgrad <- I_(cp)$, linearizing $sigma$ and adding the sparsity constraint $norm(Fanin)_0 = norm(Fanout)_0 = 1$ yields NeST.
]<prop:nest_derivation>

#proof[
  Starting from @eq:unified_objective_scalarp with $covpostact_(-1)^"ext" <- Fanin trans(Fanin)$, $covgrad <- I_(cp)$, $T <- - Gradpreact$ and $sigma="Id"$, the objective is:
  $ argmax(Fanin\, Fanout\, frob((Fanin trans(Fanin))^(1/2) trans(Fanout)) <= 1\, norm(Fanin)_0 = norm(Fanout)_0 = 1)& scalarp(- Gradpreact, Postact(l:-2) times_(cm) trans(Fanin) times_(cext) trans(Fanout))\
  = argmax(Fanin\, Fanout\, frob( trans(Fanin) trans(Fanout)) <= 1\, norm(Fanin)_0 = norm(Fanout)_0 = 1)& scalarp(trans(B_(-2)), trans(Fanin) times_(cext) trans(Fanout)) $


  To maximize the decrease in objective, we choose:
  $ i^*, j^* = argmax(i\, j) abs(B_(-2)[j, i]) $
  and set: $Fanin[i^*] = Fanout[j^*] = epsilon sqrt(abs(B_(-2)[j^*, i^*])) sign(B_(-2)[j^*, i^*])$ for random $epsilon in {-1, 1}$.
  This is exactly the NeST selection criterion from @prop:nest_objective. (Note that we don't respect the exact scaling constraint $frob(trans(Fanin) trans(Fanout)) <= 1$, but evrything is done up to scaling, so this is not an issue.)
]

== NORTH Satisfaction

#proposition[
  *Implicit orthogonality in projected methods.* Methods using the residual gradient $T = Bottleneck$ implicitly encourage new activations to be orthogonal to existing ones, similar to NORTH's explicit construction.
]<prop:north_satisfaction>

#proposition[
  $fanin$ selected by any method with $T <- Bottleneck$ and $covpostact_(-1)^"ext" <- Fanin covpostact_(-2) trans(Fanin)$ are in the set of $fanin$ constructed by NORTH-Pre.
] 
#proof[
  By @prop:bottleneck_orthogonality, $trans(Postact(l:-1)) times_n Bottleneck = 0$, so $Bottleneck$ spans directions orthogonal to $Postact(l:-1)$, similarly to $V$, which spans directions orthogonal to $Preact(l:-1)$ (the same under the first-order approximation, though further from NORTH's actual goal).
  
  For those methods the optimal solution satisfies:
  $ Postact(l:-2) times_(cm) trans(Fanin) times_(cext) trans(Fanout) approx Bottleneck $
  
  Hence ($prop$ because we skip the $1/n$ factor):
  $ trans(Fanin) prop pinv(covpostact_(-2)) times_(cm) trans(Postact(l:-2)) times_n Bottleneck times_cp pinv(trans(Fanout)) $
  
  Comparing with NORTH-Pre's construction (@eq:north_proposition):
  $ trans(Fanin) = covpostact_(-2)^(-1) times_(cm) trans(Postact(l:-2)) times_n V times_(n - cmid) R $
  
  The structures are identical with $V <- Bottleneck$ and $R <- pinv(trans(Fanout))$.
]
/*
== Intuition: Role of $covgrad^(-1)$

#block(stroke: 1pt + gray, inset: 1em, radius: 5pt)[
*Why does $covgrad^(-1)$ appear in SENN but not in TINY?*

The gradient serves two distinct purposes:

1. *In $Bottleneck$ (or $partial Fanout$)*: The gradient defines _which directions_ the new neurons should contribute to. This answers "what should we optimize?"

2. *In $covgrad^(-1)$*: The gradient covariance defines _how to measure the value_ of a contribution. This answers "how do we score candidates?"

*TINY* treats all output dimensions equally (Frobenius norm), asking: "how well can we approximate the gradient with low-rank structure?"

*SENN* incorporates curvature information via the Fisher matrix, asking: "how much will the loss decrease after a natural gradient step?" The $covgrad^(-1)$ downweights high-variance gradient directions, preferring directions where progress is more predictable.

*When do they coincide?* When $covgrad = I$ (isotropic gradient covariance), both methods become equivalent. This occurs approximately when gradients are whitened or the loss landscape is isotropic.
]
*/

