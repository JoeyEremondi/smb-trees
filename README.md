# An Agda Library for Strictly Monotone Brouwer Trees

This repository contains the code accompnaying the paper "Strictly Monotone Brouwer Trees for Well-founded Recursion Over Multiple Arguments".
It is implemented as a literate Agda file.

Basically, it gives a version of Brouwer tree ordinals that have max operator, where `a < b` and `c < d` implies `max a c < max b d`. This relation is well-founded, meaning that you can use it to prove termination for functions that aren't structurally recursive. The trees have a `Lim` operator
where you can take the ordinal that is the limit of some function's output, so it's particularly useful for assigning sizes
to higher order data.


The main library is in [SMBTree.lagda](/SMBTree.lagda), and a setoid-based algebraic interface is given in [TreeAlgebra.lagda](TreeAlgebra.lagda).
The library does not require axiom K or univalence.


Nicely rendered HTML and non-literate Agda files coming soon.

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.10204398.svg)](https://doi.org/10.5281/zenodo.10204398)

