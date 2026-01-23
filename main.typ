#import "typst/commands.typ": *

#set page(
  margin: 3cm,
  paper: "a4", 
  numbering: "1",
  number-align: center)


#show: thm-rules


#set heading(numbering: "1.")
#set math.equation(numbering: "(1.1)")
#show: equate.with(breakable: true, sub-numbering: true)
#show: intertext-rule


#outline(indent: auto, depth: 2)


= Introduction

This document presents a unified framework for understanding several neuron addition methods in growing neural networks. We show that methods such as TINY, GradMax, SENN, and NeST can all be understood as special cases of a common optimization objective, differing only in their choice of metric and constraints.


= Preliminaries

#include "subtyp/properties.typ"

#include "subtyp/objective_methods.typ"

#bibliography("references.bib", style: "typst/title-only.csl")
