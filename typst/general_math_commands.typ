#import "@preview/mannot:0.2.2": markrect
#import "@preview/ouset:0.2.0": *
#import "@preview/equate:0.2.1": equate
#import "@preview/intextual:0.1.1": *
#import "@preview/lemmify:0.1.8": *
#let (
  theorem, lemma, corollary,
  remark, proposition, example,
  definition, proof, rules: thm-rules
) = default-theorems("thm-group", lang: "en")


#let boxed = markrect

#let ie = [_i.e._]

#let scalarp(x, y) = [$lr(chevron.l #x, #y chevron.r)$]
#let expectation(x) = [$op(EE)_#x$]
#let sign(x) = [sign(#x)]
#let frob(x) = [$norm(#x)_2$]
#let normop(x) = [$|||#x|||$]
#let argmin(x) = [$op("argmin", limits: #true)_#x$]
#let argmax(x) = [$op("argmax", limits: #true)_#x$]
#let trace(x) = [$op("Tr", limits: #false)(#x)$]
#let trans(x) = [$#x^top$]
#let pinv(x) = [$#x^+$]

#let transp(x) = [$(#x)^top$]
#let transpp = transp

#let pinvp(x) = [$(#x)^+$]

#let Alpha = [A]
#let oplus = [$plus.o$]
#let bbrack(x) = [$bracket.l.double #x bracket.r.double$]
#let rg = [$op("rg")$]

#let function(f: [f], X: [X], Y: [Y], x: [x], y: [f(x)]) = [$#f : 
cases(delim:"|", #X &--> #Y, #x & arrow.r.bar.long #y)$]

#let function(f: [f], X: [X], Y: [Y], x: [x], y: [f(x)]) = [
  $#f: quad$ #table(columns: 3,
  stroke: (x, y) => if x == 0 {
  (left: 0.5pt, right: 0pt, top: 0pt, bottom: 0pt)}
  else {
  (left: 0pt, right: 0pt, top: 0pt, bottom: 0pt)},
  [$#X$], [$-->$], align(left)[$#Y$],
  [$#x$], $arrow.r.bar.long$, align(left)[$#y$]
)]

#let longmapsto = $arrow.long.bar$
#let loss = math.cal([L])

#let otimes = [$times.o$]
