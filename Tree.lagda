% !TEX root =  main.tex
\section{Brouwer Trees: An Introduction}
\begin{code}[hide]
  open import Data.Nat hiding (_≤_ ; _<_)
  open import Relation.Binary.PropositionalEquality
  open import Data.Product
  open import Relation.Nullary
  open import Iso
  module Tree where

\end{code}

Brouwer trees  are a simple but elegant tool for proving termination of higher-order procedures.
Traditionally, they are defined as follows:
\begin{code}
  data SmallTree : Set where
    Z' : SmallTree
    ↑' : SmallTree → SmallTree
    Lim' : (ℕ → SmallTree) → SmallTree
\end{code}
Under this definition, a Brouwer tree is either zero, the successor of another Brouwer tree, or the limit of a countable sequence of Brouwer trees. However, these are quite weak, in that they can only take the limit of countable sequences.
To represent the limits of uncountable sequences, we can paramterize our definition over some Universe \ala Tarski:

\begin{code}
  module CodeTree {ℓ}
    (ℂ : Set ℓ)
    (El : ℂ → Set ℓ)
    (Cℕ : ℂ) (CℕIso : Iso (El Cℕ) ℕ ) where
\end{code}

We then generalize limits to any function whose domain is the interpretation of some code.
\begin{code}
    data Tree : Set ℓ where
      Z : Tree
      ↑ : Tree → Tree
      Lim : ∀  (c : ℂ ) → (f : El c → Tree) → Tree
\end{code}

\begin{code}[hide]
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
\end{code}

\subsection{Well Founded Induction}

\begin{code}

    open import Induction.WellFounded
    access : ∀ {x} → Acc _<_ x → WfRec _<_ (Acc _<_) x
    access (acc r) = r

    smaller-accessible : (x : Tree)
      → Acc _<_ x → ∀ y → y ≤ x → Acc _<_ y
    smaller-accessible x isAcc y x<y
      = acc (λ y' y'<y → access isAcc y' (<∘≤-in-< y'<y x<y))

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


\section{First Attempts at a Join}

\subsection{Limit-based Maximum}

\begin{code}

    if0 : ℕ → Tree → Tree → Tree
    if0 zero z s = z
    if0 (suc n) z s = s

    limMax : Tree → Tree → Tree
    limMax t1 t2 = ℕLim λ n → if0 n t1 t2


\end{code}

This version of the maximum has several of the properties we want from a
maximum function: it is monotone, and is a true least-upper-bound of its inputs.

\begin{code}
    limMax≤L : ∀ {t1 t2} → t1 ≤ limMax t1 t2
    limMax≤L {t1} {t2}
        = ≤-cocone _ (Iso.inv CℕIso 0)
          (subst
            (λ x → t1 ≤ if0 x t1 t2)
            (sym (Iso.rightInv CℕIso 0))
            (≤-refl t1))

\end{code}

\begin{code}
    limMax≤R : ∀ {t1 t2} → t2 ≤ limMax t1 t2
    limMax≤R {t1} {t2}
        = ≤-cocone _ (Iso.inv CℕIso 1)
          (subst
            (λ x → t2 ≤ if0 x t1 t2)
            (sym (Iso.rightInv CℕIso 1))
            (≤-refl t2))

\end{code}

\begin{code}
    limMaxIdem : ∀ {t} → limMax t t ≤ t
    limMaxIdem {t} = ≤-limiting _ helper
      where
        helper : ∀ k → if0 (Iso.fun CℕIso k) t t ≤ t
        helper k with Iso.fun CℕIso k
        ... | zero = ≤-refl t
        ... | suc n = ≤-refl t
\end{code}

\begin{code}
    limMaxMono : ∀ {t1 t2 t1' t2'}
        → t1 ≤ t1' → t2 ≤ t2'
        → limMax t1 t2 ≤ limMax t1' t2'
    limMaxMono {t1} {t2} {t1'} {t2'} lt1 lt2 = extLim _ _ helper
      where
        helper : ∀ k → if0 (Iso.fun CℕIso k) t1 t2 ≤ if0 (Iso.fun CℕIso k) t1' t2'
        helper k with Iso.fun CℕIso k
        ... | zero = lt1
        ... | suc n = lt2


    limMaxLUB : ∀ {t1 t2 t} → t1 ≤ t → t2 ≤ t → limMax t1 t2 ≤ t
    limMaxLUB lt1 lt2 = limMaxMono lt1 lt2 ≤⨟ limMaxIdem
  \end{code}

  \begin{code}
    limMaxCommut : ∀ {t1 t2} → limMax t1 t2 ≤ limMax t2 t1
    limMaxCommut = limMaxLUB limMax≤R limMax≤L
    \end{code}

  \subsubsection{Limitation: Strict Monotonicity}


  \subsection{Recursive Maximum}

\begin{code}
    private
        data IndMaxView : Tree → Tree → Set ℓ where
          IndMaxZ-L : ∀ {t} → IndMaxView Z t
          IndMaxZ-R : ∀ {t} → IndMaxView t Z
          IndMaxLim-L : ∀ {t} {c : ℂ} {f : El c → Tree}
            → IndMaxView (Lim c f) t
          IndMaxLim-R : ∀ {t} {c : ℂ} {f : El c → Tree}
            → (∀   {c' : ℂ} {f' : El c' → Tree} → ¬ (t ≡ Lim  c' f'))
            → IndMaxView t (Lim c f)
          IndMaxLim-Suc : ∀  {t1 t2 } → IndMaxView (↑ t1) (↑ t2)
    opaque

        indMaxView : ∀ t1 t2 → IndMaxView t1 t2
        indMaxView Z t2 = IndMaxZ-L
        indMaxView (Lim c f) t2 = IndMaxLim-L
        indMaxView (↑ t1) Z = IndMaxZ-R
        indMaxView (↑ t1) (Lim c f) = IndMaxLim-R λ ()
        indMaxView (↑ t1) (↑ t2) = IndMaxLim-Suc


        indMax : Tree → Tree → Tree
        indMax' : ∀ {t1 t2} → IndMaxView t1 t2 → Tree

        indMax t1 t2 = indMax' (indMaxView t1 t2)

        indMax' {.Z} {t2} IndMaxZ-L = t2
        indMax' {t1} {.Z} IndMaxZ-R = t1
        indMax' {(Lim c f)} {t2} IndMaxLim-L
            = Lim c λ x → indMax (f x) t2
        indMax' {t1} {(Lim c f)} (IndMaxLim-R _)
            = Lim c (λ x → indMax t1 (f x))
        indMax' {(↑ t1)} {(↑ t2)} IndMaxLim-Suc = ↑ (indMax t1 t2)


  \end{code}

  \begin{code}

    module IndMaxInhab (default : (c : ℂ) → El c) where

      underLim : ∀   {c : ℂ}  {t} →  {f : El c → Tree} → (∀ k → t ≤ f k) → t ≤ Lim c f
      underLim {c = c}  {t} {f} all = ≤-trans (≤-cocone (λ _ → t) (default c) (≤-refl t)) (≤-limiting (λ _ → t) (λ k → ≤-cocone f k (all k)))

      opaque
        unfolding indMax indMax'

        indMax-≤L : ∀ {t1 t2} → t1 ≤ indMax t1 t2
        indMax-≤L {t1} {t2} with indMaxView t1 t2
        ... | IndMaxZ-L = ≤-Z
        ... | IndMaxZ-R = ≤-refl _
        ... | IndMaxLim-L {f = f} = extLim f (λ x → indMax (f x) t2) (λ k → indMax-≤L)
        ... | IndMaxLim-R {f = f} _ = underLim  λ k → indMax-≤L {t2 = f k}
        ... | IndMaxLim-Suc = ≤-sucMono indMax-≤L


        indMax-≤R : ∀ {t1 t2} → t2 ≤ indMax t1 t2
        indMax-≤R {t1} {t2} with indMaxView t1 t2
        ... | IndMaxZ-R = ≤-Z
        ... | IndMaxZ-L = ≤-refl _
        ... | IndMaxLim-R {f = f} _ = extLim f (λ x → indMax t1 (f x)) (λ k → indMax-≤R {t1 = t1} {f k})
        ... | IndMaxLim-L {f = f} = underLim  λ k → indMax-≤R
        ... | IndMaxLim-Suc {t1} {t2} = ≤-sucMono (indMax-≤R {t1 = t1} {t2 = t2})




        indMax-monoR : ∀ {t1 t2 t2'} → t2 ≤ t2' → indMax t1 t2 ≤ indMax t1 t2'
        indMax-monoR' : ∀ {t1 t2 t2'} → t2 < t2' → indMax t1 t2 < indMax (↑ t1) t2'

        indMax-monoR {t1} {t2} {t2'} lt with indMaxView t1 t2 in eq1 | indMaxView t1 t2' in eq2
        ... | IndMaxZ-L  | v2  = ≤-trans lt (≤-reflEq (cong indMax' eq2))
        ... | IndMaxZ-R  | v2  = ≤-trans indMax-≤L (≤-reflEq (cong indMax' eq2))
        ... | IndMaxLim-L {f = f1} |  IndMaxLim-L  = extLim _ _ λ k → indMax-monoR {t1 = f1 k} lt
        indMax-monoR {t1} {(Lim _ f')} {.(Lim _ f)} (≤-cocone f k lt) | IndMaxLim-R neq  | IndMaxLim-R neq'
            = ≤-limiting (λ x → indMax t1 (f' x)) (λ y → ≤-cocone (λ x → indMax t1 (f x)) k (indMax-monoR {t1 = t1} {t2 = f' y} (≤-trans (≤-cocone _ y (≤-refl _)) lt)))
        indMax-monoR {t1} {.(Lim _ _)} {t2'} (≤-limiting f x₁) | IndMaxLim-R x  | v2  =
            ≤-trans (≤-limiting (λ x₂ → indMax t1 (f x₂)) λ k → indMax-monoR {t1 = t1} (x₁ k)) (≤-reflEq (cong indMax' eq2))
        indMax-monoR {(↑ t1)} {.(↑ _)} {.(↑ _)} (≤-sucMono lt) | IndMaxLim-Suc  | IndMaxLim-Suc  = ≤-sucMono (indMax-monoR {t1 = t1} lt)
        indMax-monoR {(↑ t1)} {(↑ t2)} {(Lim _ f)} (≤-cocone f k lt) | IndMaxLim-Suc  | IndMaxLim-R x
            = ≤-trans (indMax-monoR' {t1 = t1} {t2 = t2} {t2' = f k} lt) (≤-cocone (λ x₁ → indMax (↑ t1) (f x₁)) k (≤-refl _)) --indMax-monoR' {!lt!}

        indMax-monoR' {t1} {t2} {t2'}  (≤-sucMono lt) = ≤-sucMono ( (indMax-monoR {t1 = t1} lt))
        indMax-monoR' {t1} {t2} {.(Lim _ f)} (≤-cocone f k lt)
            = ≤-cocone _ k (indMax-monoR' {t1 = t1} lt)


        indMax-monoL : ∀ {t1 t1' t2} → t1 ≤ t1' → indMax t1 t2 ≤ indMax t1' t2
        indMax-monoL' : ∀ {t1 t1' t2} → t1 < t1' → indMax t1 t2 < indMax t1' (↑ t2)
        indMax-monoL {t1} {t1'} {t2} lt with indMaxView t1 t2 in eq1 | indMaxView t1' t2 in eq2
        ... | IndMaxZ-L | v2 = ≤-trans (indMax-≤R {t1 = t1'}) (≤-reflEq (cong indMax' eq2))
        ... | IndMaxZ-R | v2 = ≤-trans lt (≤-trans (indMax-≤L {t1 = t1'}) (≤-reflEq (cong indMax' eq2)))
        indMax-monoL {.(Lim _ _)} {.(Lim _ f)} {t2} (≤-cocone f k lt) | IndMaxLim-L  | IndMaxLim-L
            = ≤-cocone (λ x → indMax (f x) t2) k (indMax-monoL lt)
        indMax-monoL {.(Lim _ _)} {t1'} {t2} (≤-limiting f lt) | IndMaxLim-L |  v2
            = ≤-limiting (λ x₁ → indMax (f x₁) t2) λ k → ≤-trans (indMax-monoL (lt k)) (≤-reflEq (cong indMax' eq2))
        indMax-monoL {.Z} {.Z} {.(Lim _ _)} ≤-Z | IndMaxLim-R neq  | IndMaxZ-L  = ≤-refl _
        indMax-monoL  {.(Lim _ f)} {.Z} {.(Lim _ _)} (≤-limiting f x) | IndMaxLim-R neq | IndMaxZ-L
            with () ← neq refl
        indMax-monoL {t1} {.(Lim _ _)} {.(Lim _ _)} (≤-cocone _ k lt) | IndMaxLim-R {f = f} neq | IndMaxLim-L {f = f'}
            = ≤-limiting (λ x → indMax t1 (f x)) (λ y → ≤-cocone (λ x → indMax (f' x) (Lim _ _)) k
            (≤-trans (indMax-monoL lt) (indMax-monoR {t1 = f' k} (≤-cocone f y (≤-refl _)))))
        ... | IndMaxLim-R neq | IndMaxLim-R {f = f} neq' = extLim (λ x → indMax t1 (f x)) (λ x → indMax t1' (f x)) (λ k → indMax-monoL lt)
        indMax-monoL {.(↑ _)} {.(↑ _)} {.(↑ _)} (≤-sucMono lt) | IndMaxLim-Suc  | IndMaxLim-Suc
            = ≤-sucMono (indMax-monoL lt)
        indMax-monoL {.(↑ _)} {.(Lim _ f)} {.(↑ _)} (≤-cocone f k lt) | IndMaxLim-Suc  | IndMaxLim-L
            = ≤-cocone (λ x → indMax (f x) (↑ _)) k (indMax-monoL' lt)

        indMax-monoL' {t1} {t1'} {t2} lt with indMaxView t1 t2 in eq1 | indMaxView t1' t2 in eq2
        indMax-monoL' {t1} {.(↑ _)} {t2} (≤-sucMono lt) | v1 | v2 = ≤-sucMono (≤-trans (≤-reflEq (cong indMax' (sym eq1))) (indMax-monoL lt))
        indMax-monoL' {t1} {.(Lim _ f)} {t2} (≤-cocone f k lt) | v1 | v2
            = ≤-cocone _ k (≤-trans (≤-sucMono (≤-reflEq (cong indMax' (sym eq1)))) (indMax-monoL' lt))
\end{code}


\subsubsection{Limitation: Idempotence}




\begin{code}

        indMax-mono : ∀ {t1 t2 t1' t2'} → t1 ≤ t1' → t2 ≤ t2' → indMax t1 t2 ≤ indMax t1' t2'
        indMax-mono {t1' = t1'} lt1 lt2 = ≤-trans (indMax-monoL lt1) (indMax-monoR {t1 = t1'} lt2)

        indMax-strictMono : ∀ {t1 t2 t1' t2'} → t1 < t1' → t2 < t2' → indMax t1 t2 < indMax t1' t2'
        indMax-strictMono lt1 lt2 = indMax-mono lt1 lt2


        indMax-sucMono : ∀ {t1 t2 t1' t2'} → indMax t1 t2 ≤ indMax t1' t2' → indMax t1 t2 < indMax (↑ t1') (↑ t2')
        indMax-sucMono lt = ≤-sucMono lt


      -- indMax-Z : ∀ t → indMax t Z ≡ o
      -- indMax-Z Z = refl
      -- indMax-Z (↑ t) = refl
      -- indMax-Z (Lim c f) = cong (Lim c) {!!} -- cong (Lim c) (funExt (λ x → indMax-Z (f x)))

        indMax-Z : ∀ t → indMax t Z ≤ t
        indMax-Z Z = ≤-Z
        indMax-Z (↑ t) = ≤-refl (indMax (↑ t) Z)
        indMax-Z (Lim c f) = extLim (λ x → indMax (f x) Z) f (λ k → indMax-Z (f k))

        indMax-↑ : ∀ {t1 t2} → indMax (↑ t1) (↑ t2) ≡ ↑ (indMax t1 t2)
        indMax-↑ = refl

        indMax-≤Z : ∀ t → indMax t Z ≤ t
        indMax-≤Z Z = ≤-refl _
        indMax-≤Z (↑ t) = ≤-refl _
        indMax-≤Z (Lim c f) = extLim _ _ (λ k → indMax-≤Z (f k))

      -- indMax-oneL : ∀ {t} → indMax T1 (↑ t) ≤ ↑ t
      -- indMax-oneL  = ≤-refl _

      -- indMax-oneR : ∀ {t} → indMax (↑ t) T1 ≤ ↑ t
      -- indMax-oneR {Z} = ≤-sucMono (≤-refl _)
      -- indMax-oneR {↑ t} = ≤-sucMono (≤-refl _)
      -- indMax-oneR {Lim c f} = ≤-sucMono (substPath (λ x → x ≤ Lim c f) (sym (indMax-Z (Lim c f))) (≤-refl (Lim c f))) -- rewrite ctop (indMax-Z (Lim c f))= ≤-refl _


        indMax-limR : ∀   {c : ℂ} (f : El  c  → Tree) t → indMax t (Lim c f) ≤ Lim c (λ k → indMax t (f k))
        indMax-limR f Z = ≤-refl _
        indMax-limR f (↑ t) = extLim _ _ λ k → ≤-refl _
        indMax-limR f (Lim c f₁) = ≤-limiting _ λ k → ≤-trans (indMax-limR f (f₁ k)) (extLim _ _ (λ k2 → indMax-monoL {t1 = f₁ k} {t1' = Lim c f₁} {t2 = f k2}  (≤-cocone _ k (≤-refl _))))


        indMax-commut : ∀ t1 t2 → indMax t1 t2 ≤ indMax t2 t1
        indMax-commut t1 t2 with indMaxView t1 t2
        ... | IndMaxZ-L = indMax-≤L
        ... | IndMaxZ-R = ≤-refl _
        ... | IndMaxLim-R {f = f} x = extLim _ _ (λ k → indMax-commut t1 (f k))
        ... | IndMaxLim-Suc {t1 = t1} {t2 = t2} = ≤-sucMono (indMax-commut t1 t2)
        ... | IndMaxLim-L {c = c} {f = f} with indMaxView t2 t1
        ... | IndMaxZ-L = extLim _ _ λ k → indMax-Z (f k)
        ... | IndMaxLim-R x = extLim _ _ (λ k → indMax-commut (f k) t2)
        ... | IndMaxLim-L {c = c2} {f = f2} =
            ≤-trans (extLim _ _ λ k → indMax-limR f2 (f k))
            (≤-trans (≤-limiting _ (λ k → ≤-limiting _ λ k2 → ≤-cocone _ k2 (≤-cocone _ k (≤-refl _))))
            (≤-trans (≤-refl (Lim c2 λ k2 → Lim c λ k → indMax (f k) (f2 k2)))
            (extLim _ _ (λ k2 → ≤-limiting _ λ k1 → ≤-trans (indMax-commut (f k1) (f2 k2)) (indMax-monoR {t1 = f2 k2} {t2 = f k1} {t2' = Lim c f} (≤-cocone _ k1 (≤-refl _)))))))


        indMax-assocL : ∀ t1 t2 t3 → indMax t1 (indMax t2 t3) ≤ indMax (indMax t1 t2) t3
        indMax-assocL t1 t2 t3 with indMaxView t2 t3 in eq23
        ... | IndMaxZ-L = indMax-monoL {t1 = t1} {t1' = indMax t1 Z} {t2 = t3} indMax-≤L
        ... | IndMaxZ-R = indMax-≤L
        ... | m with indMaxView t1 t2
        ... | IndMaxZ-L rewrite sym eq23 = ≤-refl _
        ... | IndMaxZ-R rewrite sym eq23 = ≤-refl _
        ... | IndMaxLim-R {f = f} x rewrite sym eq23 = ≤-trans (indMax-limR (λ x → indMax (f x) t3) t1) (extLim _ _ λ k → indMax-assocL t1 (f k) t3) -- f,indMax-limR f t1
        indMax-assocL .(↑ _) .(↑ _) .Z | IndMaxZ-R  | IndMaxLim-Suc = ≤-refl _
        indMax-assocL t1 t2 .(Lim _ _) | IndMaxLim-R {f = f} x   | IndMaxLim-Suc = extLim _ _ λ k → indMax-assocL t1 t2 (f k)
        indMax-assocL (↑ t1) (↑ t2) (↑ t3) | IndMaxLim-Suc  | IndMaxLim-Suc = ≤-sucMono (indMax-assocL t1 t2 t3)
        ... | IndMaxLim-L {f = f} rewrite sym eq23 = extLim _ _ λ k → indMax-assocL (f k) t2 t3



        indMax-assocR : ∀ t1 t2 t3 →  indMax (indMax t1 t2) t3 ≤ indMax t1 (indMax t2 t3)
        indMax-assocR t1 t2 t3 = ≤-trans (indMax-commut (indMax t1 t2) t3) (≤-trans (indMax-monoR {t1 = t3} (indMax-commut t1 t2))
            (≤-trans (indMax-assocL t3 t2 t1) (≤-trans (indMax-commut (indMax t3 t2) t1) (indMax-monoR {t1 = t1} (indMax-commut t3 t2)))))


        indMax-swap4 : ∀ {t1 t1' t2 t2'} → indMax (indMax t1 t1') (indMax t2 t2') ≤ indMax (indMax t1 t2) (indMax t1' t2')
        indMax-swap4 {t1}{t1'}{t2 }{t2'} =
            indMax-assocL (indMax t1 t1') t2 t2'
            ≤⨟ indMax-monoL {t1 = indMax (indMax t1 t1') t2} {t2 = t2'}
            (indMax-assocR t1 t1' t2 ≤⨟ indMax-monoR {t1 = t1} (indMax-commut t1' t2) ≤⨟ indMax-assocL t1 t2 t1')
            ≤⨟ indMax-assocR (indMax t1 t2) t1' t2'

        indMax-swap6 : ∀ {t1 t2 t3 t1' t2' t3'} → indMax (indMax t1 t1') (indMax (indMax t2 t2') (indMax t3 t3')) ≤ indMax (indMax t1 (indMax t2 t3)) (indMax t1' (indMax t2' t3'))
        indMax-swap6 {t1} {t2} {t3} {t1'} {t2'} {t3'} =
            indMax-monoR {t1 = indMax t1 t1'} (indMax-swap4 {t1 = t2} {t1' = t2'} {t2 = t3} {t2' = t3'})
            ≤⨟ indMax-swap4 {t1 = t1} {t1' = t1'}

        indMax-lim2L :
            ∀
            {c1 : ℂ}
            (f1 : El  c1 → Tree)
            {c2 : ℂ}
            (f2 : El  c2 → Tree)
            → Lim  c1 (λ k1 → Lim  c2 (λ k2 → indMax (f1 k1) (f2 k2))) ≤ indMax (Lim  c1 f1) (Lim  c2 f2)
        indMax-lim2L f1 f2 = ≤-limiting  _ (λ k1 → ≤-limiting  _ λ k2 → indMax-mono (≤-cocone  f1 k1 (≤-refl _)) (≤-cocone  f2 k2 (≤-refl _)))

        indMax-lim2R :
            ∀
            {c1 : ℂ}
            (f1 : El  c1 → Tree)
            {c2 : ℂ}
            (f2 : El  c2 → Tree)
            →  indMax (Lim  c1 f1) (Lim  c2 f2) ≤ Lim  c1 (λ k1 → Lim  c2 (λ k2 → indMax (f1 k1) (f2 k2)))
        indMax-lim2R f1 f2 = extLim  _ _ (λ k1 → indMax-limR  _ (f1 k1))

        --Attempt to have an idempotent version of indMax

        nindMax : Tree → ℕ → Tree
        nindMax t ℕ.zero = Z
        nindMax t (ℕ.suc n) = indMax (nindMax t n) t

        nindMax-mono : ∀ {t1 t2 } n → t1 ≤ t2 → nindMax t1 n ≤ nindMax t2 n
        nindMax-mono ℕ.zero lt = ≤-Z
        nindMax-mono {t1 = t1} {t2} (ℕ.suc n) lt = indMax-mono {t1 = nindMax t1 n} {t2 = t1} {t1' = nindMax t2 n} {t2' = t2} (nindMax-mono n lt) lt

        --
        indMax∞ : Tree → Tree
        indMax∞ t =  ℕLim (λ n → nindMax t n)


        indMax-∞lt1 : ∀ t → indMax (indMax∞ t) t ≤ indMax∞ t
        indMax-∞lt1 t = ≤-limiting  _ λ k → helper (Iso.fun CℕIso k)
            where
            helper : ∀ n → indMax (nindMax t n) t ≤ indMax∞ t
            helper n = ≤-cocone  _ (Iso.inv CℕIso (ℕ.suc n)) (subst (λ sn → nindMax t (ℕ.suc n) ≤ nindMax t sn) (sym (Iso.rightInv CℕIso (suc n))) (≤-refl _))

        indMax-∞ltn : ∀ n t → indMax (indMax∞ t) (nindMax t n) ≤ indMax∞ t
        indMax-∞ltn ℕ.zero t = indMax-≤Z (indMax∞ t)
        indMax-∞ltn (ℕ.suc n) t =
            ≤-trans (indMax-monoR {t1 = indMax∞ t} (indMax-commut (nindMax t n) t))
            (≤-trans (indMax-assocL (indMax∞ t) t (nindMax t n))
            (≤-trans (indMax-monoL {t1 = indMax (indMax∞ t) t} {t2 = nindMax t n} (indMax-∞lt1 t)) (indMax-∞ltn n t)))

        indMax∞-idem : ∀ t → indMax (indMax∞ t) (indMax∞ t) ≤ indMax∞ t
        indMax∞-idem t = ≤-limiting  _ λ k → ≤-trans (indMax-commut (nindMax t (Iso.fun CℕIso k)) (indMax∞ t)) (indMax-∞ltn (Iso.fun CℕIso k) t)


        indMax∞-self : ∀ t → t ≤ indMax∞ t
        indMax∞-self t = ≤-cocone  _ (Iso.inv CℕIso 1) (subst (λ x → t ≤ nindMax t x) (sym (Iso.rightInv CℕIso 1)) (≤-refl _))

        indMax∞-idem∞ : ∀ t → indMax t t ≤ indMax∞ t
        indMax∞-idem∞ t = ≤-trans (indMax-mono (indMax∞-self t) (indMax∞-self t)) (indMax∞-idem t)

        indMax∞-mono : ∀ {t1 t2} → t1 ≤ t2 → (indMax∞ t1) ≤ (indMax∞ t2)
        indMax∞-mono lt = extLim  _ _ λ k → nindMax-mono (Iso.fun CℕIso k) lt



        nindMax-≤ : ∀ {t} n → indMax t t ≤ t → nindMax t n ≤ t
        nindMax-≤ ℕ.zero lt = ≤-Z
        nindMax-≤ {t = t} (ℕ.suc n) lt = ≤-trans (indMax-monoL {t1 = nindMax t n} {t2 = t} (nindMax-≤ n lt)) lt

        indMax∞-≤ : ∀ {t} → indMax t t ≤ t → indMax∞ t ≤ t
        indMax∞-≤ lt = ≤-limiting  _ λ k → nindMax-≤ (Iso.fun CℕIso k) lt

        -- Convenient helper for turing < with indMax∞ into < without
        indMax<-∞ : ∀ {t1 t2 t} → indMax (indMax∞ (t1)) (indMax∞ t2) < t → indMax t1 t2 < t
        indMax<-∞ lt = ≤∘<-in-< (indMax-mono (indMax∞-self _) (indMax∞-self _)) lt

        indMax-<Ls : ∀ {t1 t2 t1' t2'} → indMax t1 t2 < indMax (↑ (indMax t1 t1')) (↑ (indMax t2 t2'))
        indMax-<Ls {t1} {t2} {t1'} {t2'} = indMax-sucMono {t1 = t1} {t2 = t2} {t1' = indMax t1 t1'} {t2' = indMax t2 t2'}
            (indMax-mono {t1 = t1} {t2 = t2} (indMax-≤L) (indMax-≤L))

        indMax∞-<Ls : ∀ {t1 t2 t1' t2'} → indMax t1 t2 < indMax (↑ (indMax (indMax∞ t1) t1')) (↑ (indMax (indMax∞ t2) t2'))
        indMax∞-<Ls {t1} {t2} {t1'} {t2'} =  <∘≤-in-< (indMax-<Ls {t1} {t2} {t1'} {t2'})
            (indMax-mono {t1 = ↑ (indMax t1 t1')} {t2 = ↑ (indMax t2 t2')}
            (≤-sucMono (indMax-monoL (indMax∞-self t1)))
            (≤-sucMono (indMax-monoL (indMax∞-self t2))))


        indMax∞-lub : ∀ {t1 t2 t} → t1 ≤ indMax∞ t → t2 ≤ indMax∞  t → indMax t1 t2 ≤ (indMax∞ t)
        indMax∞-lub {t1 = t1} {t2 = t2} lt1 lt2 = indMax-mono {t1 = t1} {t2 = t2} lt1 lt2 ≤⨟ indMax∞-idem _

        indMax∞-absorbL : ∀ {t1 t2 t} → t2 ≤ t1 → t1 ≤ indMax∞ t → indMax t1 t2 ≤ indMax∞ t
        indMax∞-absorbL lt12 lt1 = indMax∞-lub lt1 (lt12 ≤⨟ lt1)

        indMax∞-distL : ∀ {t1 t2} → indMax (indMax∞ t1) (indMax∞ t2) ≤ indMax∞ (indMax t1 t2)
        indMax∞-distL {t1} {t2} =
            indMax∞-lub {t1 = indMax∞ t1} {t2 = indMax∞ t2} (indMax∞-mono indMax-≤L) (indMax∞-mono (indMax-≤R {t1 = t1}))


        indMax∞-distR : ∀ {t1 t2} → indMax∞ (indMax t1 t2) ≤ indMax (indMax∞ t1) (indMax∞ t2)
        indMax∞-distR {t1} {t2} = ≤-limiting  _ λ k → helper {n = Iso.fun CℕIso k}
            where
            helper : ∀ {t1 t2 n} → nindMax (indMax t1 t2) n ≤ indMax (indMax∞ t1) (indMax∞ t2)
            helper {t1} {t2} {ℕ.zero} = ≤-Z
            helper {t1} {t2} {ℕ.suc n} =
              indMax-monoL {t1 = nindMax (indMax t1 t2) n} (helper {t1 = t1} {t2} {n})
              ≤⨟ indMax-swap4 {indMax∞ t1} {indMax∞ t2} {t1} {t2}
              ≤⨟ indMax-mono {t1 = indMax (indMax∞ t1) t1} {t2 = indMax (indMax∞ t2) t2} {t1' = indMax∞ t1} {t2' = indMax∞ t2}
                (indMax∞-lub {t1 = indMax∞ t1} (≤-refl _) (indMax∞-self _))
                (indMax∞-lub {t1 = indMax∞ t2} (≤-refl _) (indMax∞-self _))


      indMax∞-cocone : ∀  {c : ℂ} (f : El c → Tree) k →
        f k ≤ indMax∞ (Lim  c f)
      indMax∞-cocone f k =  indMax∞-self _ ≤⨟ indMax∞-mono (≤-cocone  _ k (≤-refl _))

 \end{code}
