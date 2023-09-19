% !TEX root =  main.tex

\subsection{Strictly Monotone Brouwer Trees}
\label{subsec:smb}

Now that we have identified a substantial class of well behaved Brouwer trees,
we want to define a new type containing only those trees.
In this section, we will define strictly monotone Brouwer trees (SMB-trees), and show how
they can be given a similar interface to Brouwer trees.

\begin{code}[hide]
open import Data.Nat hiding (_≤_ ; _<_)
open import Relation.Binary.PropositionalEquality
open import Data.Product
open import Data.Maybe
open import Relation.Nullary
open import Iso
  \end{code}

To begin, we declare a new Agda module, with the same parameters
we have been working with thus far: a type of codes, interpretations of those codes into types,
and a code whose interpretation is isomorphic to $\bN$.
\begin{code}
module SMBTree {ℓ}
    (ℂ : Set ℓ)
    (El : ℂ → Set ℓ)
    (Cℕ : ℂ) (CℕIso : Iso (El Cℕ) ℕ ) where
\end{code}

Next we import all of our definitions so far, using the ``Brouwer" prefix to distinguish
them from the trees and ordering we are about to define.
Critically, we do not instantiate these with the same interpretation function.
Instead, we interpret each code wrapped in $\AgdaDatatype{Maybe}$.
Note that if a type $T$ is isomorphic to $\bN$, then $\AgdaDatatype{Maybe}\ T$ is as well.
Wrapping in $\AgdaDatatype{Maybe}$ ensures that we always take Brouwer limits over non-empty sets,
an assumption that was critical for the definitions of \cref{subsec:indmax}.
Essentially, we are adding an explicit zero to every sequence whose limit we take,
so that the sequences are never empty, but the upper bound doe snot change.
This detail is hidden in the interface for SMB-trees: the assumption of non-emptiness
is only used in the Brouwer trees underlying SMB-trees.
\begin{code}
import Brouwer
    ℂ
    (λ c → Maybe (El c))
    Cℕ (maybeNatIso CℕIso)
  as Brouwer
  \end{code}


\begin{code}[hide]
open import IndMax ℂ (λ c → Maybe (El c)) Cℕ (maybeNatIso CℕIso) (λ c → nothing)
open import InfinityMax ℂ (λ c → Maybe (El c)) Cℕ (maybeNatIso CℕIso) (λ c → nothing)
infixr 10 _≤⨟_
infixr 10 _≤_
\end{code}


\subsubsection{Refining Brouwer Trees}

We define SMB-trees as a dependent record,
containing an underlying Brouwer tree, and a proof
that $\indMax$ is idempotent on this tree.

\begin{code}
record SMBTree : Set ℓ where
  constructor MkTree
  field
    rawTree : Brouwer.Tree
    isIdem : (indMax rawTree rawTree) Brouwer.≤ rawTree
open SMBTree
\end{code}
%

We can then define so-called ``smart-constructors'' corresponding to each of the constructors
for Brouwer-trees: zero, successor, and limit.
Zero and successor directly correspond to the Brouwer tree zero and successor.
Their proofs of idempotence are trivial from the properties of Brouwer $\le$.
\begin{code}
opaque
  unfolding indMax

  Z : SMBTree
  Z = MkTree Brouwer.Z Brouwer.≤-Z

  ↑ : SMBTree → SMBTree
  ↑ (MkTree t pf)
    = MkTree (Brouwer.↑ t) (Brouwer.≤-sucMono pf)
\end{code}

However, constructing the limit of a sequence of SMB-trees is not so easy.
Since we instantiated $\AgdaBound{El}$ to wrap its result in $\AgdaDatatype{Maybe}$,
we need to handle $\AgdaInductiveConstructor{nothing}$ for each limit,
but we can use $\AgdaFunction{Z}$ as a default value, since adding it to any sequence
does not change the least upper bound.
More challenging is how, as we saw in \cref{subsec:indmax}, Brouwer trees do not have $\indMax\ (\Lim\ c\ f)\ (\Lim\ c\ f) \le \Lim\ c\ f$, so we cannot directly produce a proof of idempotence.

Our key insight is to define limits of SMB-trees using $\maxInf$ on the underlying trees:
for any function producing SMB-trees, we take the limit of the underlying trees,
then $\indMax$ that result with itself an infinite numer of times.
The idempotence proof is then the property of $\maxInf$ that we proved in \cref{subsec:infinity}.
\begin{code}
  Lim : ∀   (c : ℂ) → (f : El c → SMBTree) → SMBTree
  Lim c f =
    MkTree
    (indMax∞
      (Brouwer.Lim c
        (maybe′ (λ x → rawTree (f x)) Brouwer.Z)))
    (indMax∞-idem _)
\end{code}



\subsubsection{Ordering SMB-trees}

SMB-trees are ordered by the order on their underlying Brouwer trees:
%
\begin{code}
record _≤_ (t1 t2 : SMBTree) : Set ℓ where
  constructor mk≤
  inductive
  field
    get≤ : (rawTree t1) Brouwer.≤ (rawTree t2)
open _≤_

\end{code}
%
The successor function allows us to define a strict ording on SMB-trees.
\begin{code}
_<_ : SMBTree → SMBTree → Set ℓ
_<_ t1 t2 = (↑ t1) ≤ t2
\end{code}

The next step is to prove that our SMB-tree constructors satisfy the same
inequalities as Brouwer trees. Since SMB-trees are ordered by their underlying
Brouwer trees, most properties can be directly lifted from  Brouwer trees
to SMB-trees.

\begin{code}
opaque
  unfolding Z ↑
  ≤↑ : ∀ t → t ≤ ↑ t
  ≤↑ t =  mk≤ (Brouwer.≤↑t _)

  _≤⨟_ : ∀ {t1 t2 t3} → t1 ≤ t2 → t2 ≤ t3 → t1 ≤ t3
  _≤⨟_ (mk≤ lt1) (mk≤ lt2) = mk≤ (Brouwer.≤-trans lt1 lt2)

  ≤-refl : ∀ {t} → t ≤ t
  ≤-refl =  mk≤ (Brouwer.≤-refl _)
\end{code}

The constructors for $\le$ each have a counterpart for SMB-trees.
For zero and successor, these are trivially lifted.
\begin{code}
  ≤-Z : ∀ {t} → Z ≤ t
  ≤-Z =  mk≤ Brouwer.≤-Z

  ≤-sucMono : ∀ {t1 t2} → t1 ≤ t2 → ↑ t1 ≤ ↑ t2
  ≤-sucMono (mk≤ lt) = mk≤ (Brouwer.≤-sucMono lt)
\end{code}
  The constructors for ordering limits require more attention.
  To show that an SMB-tree limit is an upper bound, we use the fact
  that the underlying limit was an upper bound, and the fact that $\maxInf$ is as large as its argument,
  since the SMB-tree $\AgdaFunction{Lim}$ wraps its result in $\maxInf$.
  Note that, since we already have transitivity for our new $\le$,
  we can simply show that $f\ k$ is less than the limit of $f$,
  avoiding the more complicated form of $\cocone$.
\begin{code}
  ≤-limUpperBound : ∀   {c : ℂ} → {f : El c → SMBTree}
    → ∀ k → f k ≤ Lim c f
  ≤-limUpperBound {c = c} {f = f} k
    = mk≤ (Brouwer.≤-cocone _ (just k) (Brouwer.≤-refl _)
           Brouwer.≤⨟ indMax∞-self (Brouwer.Lim c _))
\end{code}

Finally, we need to show that the SMT-tree limit is less than all other upper bounds.
Suppose $t : \AgdaDatatype{SMBTree}$ is an upper bound for $f$,
and $t_u$ is the underlying tree for $t$, and $f_u$ computes the underlying trees for $f$.
Then $\limiting$ gives that the underlying tree for $t$ is an upper bound for the trees underlying the image of $f$.
However, the SMB-tree limit wraps its result in $\maxInf$, so we need to show that $\maxInf$ of the limit
is also less than $t'$.
The monotonicity of $\maxInf$ then gives that $\indMax (\Lim\ c\ f_u)$ is less than $\maxInf\ t'$.
In \cref{subsec:infinity}, we showed that $\maxInf$ had no effect on Brouwer trees that $\indMax$ was idempotent on.
This is exactly what the  $\AgdaField{isIdem}$ field of SMB-trees contains! So we have $\maxInf\ t' \le\ t'$,
and transitivity gives our result.
\begin{code}
  ≤-limLeast : ∀   {c : ℂ} → {f : El c → SMBTree}
    → {t : SMBTree}
    → (∀ k → f k ≤ t) → Lim c f ≤ t
  ≤-limLeast {f = f} {t = MkTree t idem} lt
    = mk≤ (
      indMax∞-mono
        (Brouwer.≤-limiting _
          (maybe (λ k → get≤ (lt k)) Brouwer.≤-Z))
      Brouwer.≤⨟ (indMax∞-≤ idem) )
\end{code}


\subsubsection{The Join for SMB-trees}
Our whole reason for defining SMB-trees was to define a well-behaved maximum operator,
and we finally have the tools to do so.
We can define the join in terms of $\indMax$ on the underlying trees.
The proof that the $\indMax$ is idempotent on the result follows from
associativity, commutativity, and monotonicity of $\indMax$.
\begin{code}
opaque
  unfolding indMax Z ↑ indMaxView
  max : SMBTree → SMBTree → SMBTree
  max t1 t2 =
    MkTree
      (indMax (rawTree t1) (rawTree t2))
      (indMax-swap4 {t1 = rawTree t1} {t1' = rawTree t2}
                    {t2 = rawTree t1} {t2' = rawTree t2}
        Brouwer.≤⨟ indMax-mono (isIdem t1) (isIdem t2))
\end{code}

For Brouwer trees, $\indMax$ had all the properties we wanted
except for idempotence. All of these can be lifted directly to
SMB-trees:

\begin{code}
  max-≤L : ∀ {t1 t2} → t1 ≤ max t1 t2

  max-≤R : ∀ {t1 t2} → t2 ≤ max t1 t2

  max-mono : ∀ {t1 t1' t2 t2'} → t1 ≤ t1' → t2 ≤ t2' →
    max t1 t2 ≤ max t1' t2'

  max-idem≤ : ∀ {t} → t ≤ max t t

  max-commut : ∀ t1 t2 → max t1 t2 ≤ max t2 t1

  max-assocL : ∀ t1 t2 t3
    → max t1 (max t2 t3) ≤ max (max t1 t2) t3

  max-assocR : ∀ t1 t2 t3
    →  max (max t1 t2) t3 ≤ max t1 (max t2 t3)
\end{code}

In particular, $\AgdaFunction{max}$ is strictly monotone, and distributes over
the successor:

\begin{code}
  max-strictMono : ∀ {t1 t1' t2 t2' : SMBTree}
    → t1 < t1' → t2 < t2' → max t1 t2 < max t1' t2'

  max-sucMono : ∀ {t1 t2 t1' t2' : SMBTree}
    → max t1 t2 ≤ max t1' t2' → max t1 t2 < max (↑ t1') (↑ t2')
\end{code}

However, because we restricted SMB-trees to only contain Brouwer trees that
$\indMax$ is idempotent on, we can prove that $\AgdaFunction{Max}$ is
idempotent for SMB-trees:

\begin{code}
  max-idem : ∀ {t : SMBTree} → max t t ≤ t
  max-idem {t = MkTree t pf} = mk≤ pf
\end{code}

\begin{code}[hide]

  ≤-extLim : ∀  {c : ℂ} → {f1 f2 : El c → SMBTree}
    → (∀ k → f1 k ≤ f2 k)
    → Lim c f1 ≤ Lim c f2
  ≤-extLim {f1 = f1} {f2 = f2} lt = ≤-limLeast (λ k → lt k ≤⨟ ≤-limUpperBound {f = λ v → f2 v} k)

  ≤-extExists : ∀  {c1 c2 : ℂ} → {f1 : El c1 → SMBTree} {f2 : El c2 → SMBTree}
    → (∀ k1 → Σ[ k2 ∈ El c2 ] f1 k1 ≤ f2 k2)
    → Lim c1 f1 ≤ Lim c2 f2
  ≤-extExists {f1 = f1} {f2} lt = ≤-limLeast (λ k1 → proj₂ (lt k1) ≤⨟ ≤-limUpperBound {f = f2} (proj₁ (lt k1)))

  ¬Z<↑ : ∀  t → ¬ ((↑ t) ≤ Z)
  ¬Z<↑ t pf = Brouwer.¬<Z (rawTree t) (get≤ pf)

  max-≤L = mk≤ indMax-≤L

  max-≤R {t1 = t1} {t2 = t2} =  mk≤ (indMax-≤R {t1 = rawTree t1} )

  max-mono lt1 lt2 = mk≤ (indMax-mono (get≤ lt1) (get≤ lt2))

  max-monoR : ∀ {t1 t2 t2'} → t2 ≤ t2' → max t1 t2 ≤ max t1 t2'
  max-monoR {t1} {t2} {t2'} lt = max-mono {t1 = t1} {t1' = t1} {t2 = t2} {t2' = t2'} (≤-refl {t1}) lt

  max-monoL : ∀ {t1 t1' t2} → t1 ≤ t1' → max t1 t2 ≤ max t1' t2
  max-monoL {t1} {t1'} {t2} lt = max-mono {t1} {t1'} {t2} {t2} lt (≤-refl {t2})


  max-idem≤ {t = MkTree t pf} = max-≤L


  max-commut t1 t2 =  mk≤ (indMax-commut (rawTree t1) (rawTree t2))

  max-assocL t1 t2 t3 = mk≤ (indMax-assocL (rawTree t1) (rawTree t2) (rawTree t3))

  max-assocR t1 t2 t3 = mk≤ (indMax-assocR (rawTree t1) (rawTree t2) (rawTree t3))

  max-swap4 : ∀ {t1 t1' t2 t2'} → max (max t1 t1') (max t2 t2') ≤ max (max t1 t2) (max t1' t2')
  max-swap4 {t1 = t1} {t1' = t1'} {t2 = t2} {t2' = t2'} =  mk≤ (indMax-swap4 {t1 = rawTree t1} {t1' = rawTree t1'} {t2 = rawTree t2} {t2' = rawTree t2'})

  max-strictMono lt1 lt2 = mk≤ (indMax-strictMono (get≤ lt1) (get≤ lt2))

  max-sucMono {t1 = t1} {t2 = t2} {t1' = t1'}  {t2' = t2'} lt =  mk≤ (indMax-sucMono {t1 = rawTree t1} {t2 = rawTree t2} {t1' = rawTree t1'} {t2' = rawTree t2'} (get≤ lt))

\end{code}

These together are enough to prove that our maximum is
the least of all upper bounds.
\begin{code}
  max-LUB : ∀ {t1 t2 t} → t1 ≤ t → t2 ≤ t → max t1 t2 ≤ t
  max-LUB lt1 lt2 = max-mono lt1 lt2 ≤⨟ max-idem
  \end{code}

  Perhaps surprisingly, this means that an SMB-tree version of $\limMax$
  is equivalent to $\AgdaFunction{max}$, since they are both the least upper bound.
  This in turn means that the limit based maximum is strictly monotone for SMB-trees.
  \begin{code}

ℕLim : (ℕ → SMBTree) → SMBTree
ℕLim f = Lim Cℕ  (λ cn → f (Iso.fun CℕIso cn))

max' : SMBTree → SMBTree → SMBTree
max' t1 t2 = ℕLim (λ n → if0 n t1 t2)

max'-≤L : ∀ {t1 t2} → t1 ≤ max' t1 t2

max'-≤R : ∀ {t1 t2} → t2 ≤ max' t1 t2

max'-LUB : ∀ {t1 t2 t} → t1 ≤ t → t2 ≤ t → max' t1 t2 ≤ t

max≤max' : ∀ {t1 t2} → max t1 t2 ≤ max' t1 t2
max≤max' = max-LUB max'-≤L max'-≤R

max'≤max : ∀ {t1 t2} → max' t1 t2 ≤ max t1 t2
max'≤max = max'-LUB max-≤L max-≤R
\end{code}


\begin{code}[hide]




max'-≤L {t1} {t2}
    = subst (λ x → t1 ≤ if0 x t1 t2) (sym (Iso.rightInv CℕIso 0)) ≤-refl ≤⨟
      ≤-limUpperBound  (Iso.inv CℕIso 0)

max'-≤R {t1} {t2}
    = subst (λ x → t2 ≤ if0 x t1 t2) (sym (Iso.rightInv CℕIso 1)) ≤-refl ≤⨟
      ≤-limUpperBound  (Iso.inv CℕIso 1)


max'-Idem : ∀ {t} → max' t t ≤ t
max'-Idem {t} = ≤-limLeast  helper
    where
    helper : ∀ k → if0 (Iso.fun CℕIso k) t t ≤ t
    helper k with Iso.fun CℕIso k
    ... | zero = ≤-refl
    ... | suc n = ≤-refl

max'-Mono : ∀ {t1 t2 t1' t2'}
    → t1 ≤ t1' → t2 ≤ t2'
    → max' t1 t2 ≤ max' t1' t2'
max'-Mono {t1} {t2} {t1'} {t2'} lt1 lt2 = ≤-extLim  helper
    where
    helper : ∀ k → if0 (Iso.fun CℕIso k) t1 t2 ≤ if0 (Iso.fun CℕIso k) t1' t2'
    helper k with Iso.fun CℕIso k
    ... | zero = lt1
    ... | suc n = lt2


max'-LUB lt1 lt2 = max'-Mono lt1 lt2 ≤⨟ max'-Idem





limSwap : ∀ {c1 c2 } {f : El c1 → El c2 → SMBTree} → (Lim c1 λ x → Lim c2 λ y → f x y) ≤ Lim c2 λ y → Lim c1 λ x → f x y
limSwap = ≤-limLeast (λ x → ≤-limLeast λ y → ≤-limUpperBound x ≤⨟ ≤-limUpperBound y   )

max-swapL : ∀ {c} {f g : El c → SMBTree} →  Lim c (λ k → max (f k) (g k)) ≤ max (Lim c f) (Lim c g)
max-swapL {c} {f} {g} = ≤-limLeast λ k1 → max-mono (≤-limUpperBound _) (≤-limUpperBound _)


max-swap2L : ∀ {c1 c2} {f : El c1 → SMBTree} {g : El c2 → SMBTree } →  Lim c1 (λ k1 → Lim c2  λ k2 → max (f k1) (g k2)) ≤ max (Lim c1 f) (Lim c2 g)
max-swap2L {c1} {c2} {f} {g} = ≤-limLeast λ k1 → ≤-limLeast λ k2 → max-mono (≤-limUpperBound k1) (≤-limUpperBound k2)

max-swapR : ∀ {c} {f g : El c → SMBTree} → max (Lim c f) (Lim c g) ≤ Lim c (λ k → max (f k) (g k))
max-swapR {c} {f} {g} = max-LUB (≤-extLim λ k → max-≤L) (≤-extLim λ k → max-≤R)


max-swap2R : ∀ {c1 c2} {f : El c1 → SMBTree} {g : El c2 → SMBTree } → El c1 → El c2 → max (Lim c1 f) (Lim c2 g) ≤ Lim c1 (λ k1 → Lim c2  λ k2 → max (f k1) (g k2))
max-swap2R k1 k2 =
  max-LUB
    (≤-extLim (λ k → ≤-limUpperBound k2 ≤⨟ ≤-extLim λ _ → max-≤L))
    (≤-limUpperBound k1 ≤⨟ ≤-extLim λ _ → ≤-extLim (λ _ → max-≤R))


open import Induction.WellFounded
opaque
  unfolding ↑


  invertSuc : ∀ {t1 t2} → ↑ t1 ≤ ↑ t2 → t1 ≤ t2
  invertSuc {MkTree t1 _} {MkTree t2 _} (mk≤ (Brouwer._≤_.≤-sucMono lt)) = mk≤ lt
\end{code}


\subsubsection{Well Founded Ordering on SMB-trees}
Our motivation for defining SMB-trees was defining well founded recursion,
so the final piece of our definition is a proof that the strict ordering of
SMB-trees is well founded.
Intuitively this should hold: there are no infinite descending chains
of Brouwer trees, and there are fewer SMB-trees than Brouwer trees, so
there can be no infinite descending chains of SMB-trees.
The key lemma is that an SMB-tree is accessible if its underlying Brouwer tree is.
\begin{code}
  sizeWF : WellFounded _<_
  sizeWF t = sizeAcc (Brouwer.ordWF (rawTree t))
    where
      sizeAcc : ∀ {t}
        → Acc Brouwer._<_ (rawTree t)
        → Acc _<_ t
      sizeAcc {t} (acc x)
        = acc ((λ y lt → sizeAcc (x (rawTree y) (get≤ lt))))
\end{code}

Thus, we have an ordinal type with limits, a strictly monotone join,
and well founded recursion.


