% !TEX root =  main.tex
\begin{code}[hide]
module SmallTree where
open import Data.Nat
\end{code}


Brouwer trees \citep{bams1183500400,kleene1938}
are a simple but elegant tool for proving termination of higher-order procedures.
Traditionally, they are defined as follows:
\begin{code}
data SmallTree : Set where
    Z : SmallTree
    ↑ : SmallTree → SmallTree
    Lim : (ℕ → SmallTree) → SmallTree
\end{code}
