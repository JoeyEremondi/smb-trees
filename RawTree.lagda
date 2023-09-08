% !TEX root =  main.tex
\begin{code}[hide]
  open import Data.Nat hiding (_≤_ ; _<_)
  open import Relation.Binary.PropositionalEquality
  open import Data.Product
  open import Relation.Nullary
  open import Iso

\end{code}

Under this definition, a Brouwer tree is either zero, the successor of another Brouwer tree, or the limit of a countable sequence of Brouwer trees. However, these are quite weak, in that they can only take the limit of countable sequences.
To represent the limits of uncountable sequences, we can paramterize our definition over some Universe \ala Tarski:

\begin{code}
  module RawTree {ℓ}
    (ℂ : Set ℓ)
    (El : ℂ → Set ℓ)
    (Cℕ : ℂ) (CℕIso : Iso (El Cℕ) ℕ ) where
\end{code}


Our module is paramterized over a universe level, a type $\bC$ of \textit{codes}, and an ``elements-of'' interpretation
function $\mathit{El}$, which computes the type represented by each code.
We require that there be a code whose interpretation is isomorphic to the natural numbers,
as this is essential to our construction in \cref{sec:TODO}.
Increasingly larger trees can be obtained by setting $\bC := \AgdaPrimitive{Set} \ \ell$ and
$\mathit{El} := \mathit{id}$ for increasing $\ell$.
However, by defining an inductive-recursive universe,
one can still capture limits over some non-countable types, since
 $\AgdaDatatype{Tree}$ is in $\AgdaPrimitive{Set}$ whenever $\bC$ is.

We then generalize limits to any function whose domain is the interpretation of some code.
\begin{code}
    data Tree : Set ℓ where
      Z : Tree
      ↑ : Tree → Tree
      Lim : ∀  (c : ℂ ) → (f : El c → Tree) → Tree
\end{code}

The small limit constructor can be recovered from the natural-number code
\begin{code}
    ℕLim : (ℕ → Tree) → Tree
    ℕLim f = Lim Cℕ  (λ cn → f (Iso.fun CℕIso cn))
\end{code}

Brouwer trees are a the quintessential example of a higher-order inductive type.%
\footnote{Not to be confused with Higher Inductive Types (HITs) from Homotopy Type Theory~\citep{hottbook}}:
Each tree is built using smaller trees or functions producing smaller trees, which is essentially
a way of storing a possibly infinite number of smaller trees.

\subsection{Ordering Trees}

Our ultimate goal is to have a well-founded ordering%
\footnote{Technically, this is a well-founded quasi-ordering because there are pairs of
  trees which are related by both $\leq$ and $\geq$, but which are not propositionally equal.},
so we define a relation to order Brouwer trees.

\begin{code}
    data _≤_ : Tree → Tree → Set ℓ where
      ≤-Z : ∀ {t} → Z ≤ t
      ≤-sucMono : ∀ {t1 t2}
        → t1 ≤ t2
        → ↑ t1 ≤ ↑ t2
      ≤-cocone : ∀  {t} {c : ℂ} (f : El c  → Tree) (k : El c)
        → t ≤ f k
        → t ≤ Lim c f
      ≤-limiting : ∀   {t} {c : ℂ}
        → (f : El c → Tree)
        → (∀ k → f k ≤ t)
        → Lim c f ≤ t

      \end{code}

      This relation is reflexive:
\begin{code}
    ≤-refl : ∀ t → t ≤ t
    ≤-refl Z = ≤-Z
    ≤-refl (↑ t) = ≤-sucMono (≤-refl t)
    ≤-refl (Lim c f)
      = ≤-limiting f (λ k → ≤-cocone f k (≤-refl (f k)))
\end{code}
\begin{code}[hide]
    ≤-reflEq : ∀ {t1 t2} → t1 ≡ t2 → t1 ≤ t2
    ≤-reflEq refl = ≤-refl _
\end{code}

      Crucially, it is also transitive, making the relation a preorder.
We modify our the order relation from that of \citet{KRAUS2023113843}
so that transitivity can be proven constructively, rather than adding it as a constructor
for the relation. This allows us to prove well-foundedness of the relation without needing
quotient types or other advanced features.

\begin{code}
    ≤-trans : ∀ {t1 t2 t3} → t1 ≤ t2 → t2 ≤ t3 → t1 ≤ t3
    ≤-trans ≤-Z p23 = ≤-Z
    ≤-trans (≤-sucMono p12) (≤-sucMono p23)
      = ≤-sucMono (≤-trans p12 p23)
    ≤-trans p12 (≤-cocone f k p23)
      = ≤-cocone f k (≤-trans p12 p23)
    ≤-trans (≤-limiting f x) p23
      = ≤-limiting f (λ k → ≤-trans (x k) p23)
    ≤-trans (≤-cocone f k p12) (≤-limiting .f x)
      = ≤-trans p12 (x k)
\end{code}

\begin{code}[hide]
    extLim : ∀   {c : ℂ}
      →  (f1 f2 : El c → Tree)
      → (∀ k → f1 k ≤ f2 k)
      → Lim c f1 ≤ Lim c f2
    extLim {c = c} f1 f2 all
      = ≤-limiting f1 (λ k → ≤-cocone f2 k (all k))

    infixr 10 _≤⨟_
\end{code}

We create an infix version of transitivity for more readable construction of proofs:
\begin{code}
    _≤⨟_ :  ∀ {t1 t2 t3} → t1 ≤ t2 → t2 ≤ t3 → t1 ≤ t3
    lt1 ≤⨟ lt2 = ≤-trans lt1 lt2
\end{code}

\subsubsection{Strict Ordering}

We can define a strictly-less-than relation in terms of our less-than relation
and the successor constructor:
\begin{code}
    _<_ : Tree → Tree → Set ℓ
    t1 < t2 = ↑ t1 ≤ t2
  \end{code}

  That is, a $t_{1}$ is strictly smaller than $t_{2}$ if the tree one-size larger than $t_{1}$ is as small as $t_{2}$.
  This relation has the properties one expects of a strictly-less-than
  relation: it is a transitive  sub-relation of the less-than relation,
  every tree is strictly less than its successor,
  and no tree is strictly smaller than zero.
  \je{TODO more?}

\begin{code}
    ≤↑t : ∀ t → t ≤ ↑ t
    ≤↑t Z = ≤-Z
    ≤↑t (↑ t) = ≤-sucMono (≤↑t t)
    ≤↑t (Lim c f)
      = ≤-limiting f λ k →
        (≤↑t (f k))
        ≤⨟ (≤-sucMono (≤-cocone f k (≤-refl (f k))))
  \end{code}

\begin{code}
    <-in-≤ : ∀ {x y} → x < y → x ≤ y
    <-in-≤ pf = ≤-trans (≤↑t _) pf

    <∘≤-in-< : ∀ {x y z} → x < y → y ≤ z → x < z
    <∘≤-in-< x<y y≤z = ≤-trans x<y y≤z

    ≤∘<-in-< : ∀ {x y z} → x ≤ y → y < z → x < z
    ≤∘<-in-< {x} {y} {z} x≤y y<z = ≤-trans (≤-sucMono x≤y) y<z

    ¬<Z : ∀ t → ¬(t < Z)
    ¬<Z t ()
  \end{code}


  \begin{code}[hide]
  \end{code}





\begin{code}[hide]
    existsLim : ∀  {c1 : ℂ} {c2 : ℂ} →  (f1 : El c1  → Tree) (f2 : El  c2  → Tree) → (∀ k1 → Σ[ k2 ∈ El  c2 ] f1 k1 ≤ f2 k2) → Lim  c1 f1 ≤ Lim  c2 f2
    existsLim {æ1} {æ2} f1 f2 allex = ≤-limiting  f1 (λ k → ≤-cocone f2 (proj₁ (allex k)) (proj₂ (allex k)))

    open import Induction.WellFounded
\end{code}

\subsection{Well Founded Induction}

Recall the definition of a constructive well founded relation:

\input{WFTypeset}

Following the construction of \citet{KRAUS2023113843},
we can show that the strict ordering on Brouwer trees is
well founded.
First, we prove a helper lemma: if a value is accessible,
then all (not necessarily strictly) smaller terms
are are also accessible.
%
\begin{code}
    smaller-accessible : (x : Tree)
      → Acc _<_ x → ∀ y → y ≤ x → Acc _<_ y
    smaller-accessible x (acc r) y x<y
      = acc (λ y' y'<y → r y' (<∘≤-in-< y'<y x<y))
\end{code}
Then we use structural reduction to show that all terms are accesible.
The key observations are that zero is trivially accessible,
since no trees are strictly smaller than it,
and that the only way to derive
 $\up t \le \AgdaSymbol{(}\AgdaInductiveConstructor{Lim}\AgdaSpace{}\
\AgdaBound{c}\AgdaSpace{}\ 
\AgdaBound{f}\AgdaSymbol{)}$ is with $\AgdaInductiveConstructor{≤-cocone}$,
yielding a concrete index $k$ for which $\uparrow t \le f\ k$,
on which we can recur.
\begin{code}
    ordWF : WellFounded _<_
    ordWF Z = acc λ _ ()
    ordWF (↑ x)
      = acc (λ { y (≤-sucMono y≤x)
        → smaller-accessible x (ordWF x) y y≤x})
    ordWF (Lim c f) = acc helper
      where
        helper : (y : Tree) → (y < Lim c f)
          → Acc _<_ y
        helper y (≤-cocone .f k y<fk)
          = smaller-accessible (f k)
            (ordWF (f k)) y (<-in-≤ y<fk)

\end{code}

