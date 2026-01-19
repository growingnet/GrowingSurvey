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

#include "subtyp/objective_methods.typ"

#bibliography("references.bib", style: "typst/title-only.csl")
