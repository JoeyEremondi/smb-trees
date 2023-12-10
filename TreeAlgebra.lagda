
\section{An Algebraic Perspective}
\label{sec:algebra}

\begin{code}[hide]
open import Iso
open import Data.Nat hiding (_≤_ ; _<_)
open import Data.Product
open import Relation.Binary.Lattice
open import Relation.Binary
open import Relation.Nullary
open import Relation.Nullary.Negation
open import Function.Equivalence
module TreeAlgebra {ℓ}
    (ℂ : Set ℓ)
    (El : ℂ → Set ℓ)
    (Cℕ : ℂ) (CℕIso : Iso (El Cℕ) ℕ ) where

open import SMBTree ℂ El Cℕ CℕIso as SMBTree hiding (_≤_)


module SemiLatMod where
    open BoundedJoinSemilattice
    open IsJoinSemilattice
    open IsPartialOrder
    open IsPreorder

    treeIsSemiLat : IsJoinSemilattice (λ t1 t2 → t1 SMBTree.≤ t2 × t2 SMBTree.≤ t1) SMBTree._≤_  max
    IsEquivalence.refl (isEquivalence (isPreorder (isPartialOrder treeIsSemiLat)))
        = ≤-refl , ≤-refl
    IsEquivalence.sym (isEquivalence (isPreorder (isPartialOrder treeIsSemiLat)))
        (lt1 , lt2 )
        = (lt2 , lt1)
    IsEquivalence.trans (isEquivalence (isPreorder (isPartialOrder treeIsSemiLat)))
        (lt1 , lt1') (lt2 , lt2')
        = lt1 ≤⨟ lt2 , lt2' ≤⨟ lt1'
    reflexive (isPreorder (isPartialOrder treeIsSemiLat)) (lt , _) = lt
    trans (isPreorder (isPartialOrder treeIsSemiLat)) = _≤⨟_
    antisym (isPartialOrder treeIsSemiLat) lt1 lt2 = lt1 , lt2
    supremum treeIsSemiLat t1 t2
        = max-≤L , max-≤R , λ z → max-LUB

    treeBoundedSemi : IsBoundedJoinSemilattice (λ t1 t2 → t1 SMBTree.≤ t2 × t2 SMBTree.≤ t1) SMBTree._≤_  max Z
    IsBoundedJoinSemilattice.isJoinSemilattice treeBoundedSemi = treeIsSemiLat
    IsBoundedJoinSemilattice.minimum treeBoundedSemi _ = ≤-Z

\end{code}

As a final contribution, we give an algebraic viewpoint of SMBTrees,
in terms of equivalences rather than orderings.
There are no new results in this section, but the equational view
highlights the ways in which a strictly monotone join is useful
in reasoning.

SMB-trees cannot be completely characterized using first order equations,
since $\Lim$ is an infinitary operator. Nevertheless, we anticipate
that many of the equations here could be useful in developing
automated rewriting tools or tactics for reasoning about SMBTrees.
The constraint of $t_{1} < t_{2}$ can be translated into the equation
$\uparrow\ t_{1} \vee t_{2} \approx t_{2}$, which can then be mechanically
simplified according to the equations in the following sections.

\subsection{Semilattices and Setoids}

Unfortunately, SMB-trees are only a preorder, not a partial order.
Because we are working in vanilla Agda, we have no function extensionality,
so applying $\Lim$ to definitionally distinct but extensionally equal functions
produces trees that are equivalent but not equal.
Postulating that equivalent terms are equal would be inconsistent:
inductive and limit-based joins are
equivalent for SMB-trees, so $\uparrow\ (t_{1} \vee t_{2})$ is equivalent to
$\limMax\ (\uparrow\ t_{1})\ (\uparrow\ t_{2})$,
even though their heads are distinct datatype constructors.
Likewise, $\Lim\ c\ f$ is equivalent to $\AgdaInductiveConstructor{Z}$
any time $\AgdaBound{El}\ c$ is uninhabited.

As such, we present our equations in the setoid style \ie up to an equivalence relation,
but the results in this section could be adapted to quotient types in
a system like Cubical Agda~\citep{10.1145/3341691}.
First, we establish that SMB-trees are a bounded join-semilattice.
\begin{code}
    TreeSemiLat : BoundedJoinSemilattice ℓ ℓ ℓ
    Carrier TreeSemiLat = SMBTree
    _≈_ TreeSemiLat t1 t2 = t1 SMBTree.≤ t2 × t2 SMBTree.≤ t1
    _≤_ TreeSemiLat = SMBTree._≤_
    _∨_ TreeSemiLat = SMBTree.max
    ⊥ TreeSemiLat = SMBTree.Z
    -- ...
\end{code}

\begin{code}[hide]
    isBoundedJoinSemilattice TreeSemiLat = treeBoundedSemi
open BoundedJoinSemilattice SemiLatMod.TreeSemiLat
\end{code}

Orderings between trees can then be expressed equationally
using the join: $t_{1}$ is smaller than $t_{2}$ iff their join is $t_{2}$.
\begin{code}
ord→equiv : ∀ {t1 t2} → t1 ≤ t2 → t1 ∨ t2 ≈ t2
equiv→ord : ∀ {t1 t2} → t1 ∨ t2 ≈ t2 → t1 ≤ t2
\end{code}

This means that our ordering respects equivalence.
Additionally, the successor, join and limit constructors are congruences for our equivalence: equivalent inputs produce equivalent outputs.
These can be combined with the proof irrelevance
of well-founded recursion to rewrite ordering goals
according to algebraic laws.

\begin{code}
≤≈ : ∀ {t1 t2 s1 s2}
  → s1 ≤ t1 → s1 ≈ s2 → t1 ≈ t2 → s2 ≤ t2
<≈ : ∀ {t1 t2 s1 s2}
  → s1 < t1 → s1 ≈ s2 → t1 ≈ t2 → s2 < t2
↑-cong : ∀ {t1 t2}
  → t1 ≈ t2 → ↑ t1 ≈ ↑ t2
Lim-cong : ∀ {c} {f1 f2}
  → (∀ x → f1 x ≈ f2 x) → Lim c f1 ≈ Lim c f2
max-cong : ∀ {s1 s2 t1 t2}
  → s1 ≈ s2 → t1 ≈ t2 → s1 ∨ t1 ≈ s2 ∨ t2
\end{code}

This gives us a framework
to present the properties of SMB-trees equationally.
For instance,
the semilattice properties of the join can be given algebraically:
a semilattice is a commutative, idempotent semigroup.
\begin{code}
assoc : ∀ {t1 t2 t3} → t1 ∨ (t2 ∨ t3) ≈ (t1 ∨ t2) ∨ t3
commut : ∀ {t1 t2} → t1 ∨ t2 ≈ t2 ∨ t1
idem : ∀ {t} → t ∨ t ≈ t
\end{code}

\subsection{Successor: The Inflationary Endomorphism}

The algebraic version of strict monotonicity is that
the successor function is what \citet{BEZEM20221} call
an \textit{inflationary endomorphism}, \ie a unary operator
whose interactions with the join behave like the successor on natural numbers.
To our knowledge, SMB-trees are the first ordinal notation
in type theory for which the successor is inflationary
and arbitrary limits are supported.

There are two laws to inflationary endomorphisms.
First, the maximum of $\uparrow\ t$ and $t$ must be $\uparrow\ t$,
which captures the idea that $t$ is less that $\uparrow\ t$.
\begin{code}
↑absorb : ∀ {t} → t ∨ (↑ t) ≈ ↑ t
↑absorb =
  max-mono (≤↑ _) ≤-refl ≤⨟ max-idem
  , max-≤R
\end{code}
Second, the successor must distribute over the join. Recall that
this was precisely the condition we used to establish strict monotonicity.
\begin{code}
↑dist : ∀ {t1 t2} → ↑ (t1  ∨ t2) ≈ ↑ t1 ∨ ↑ t2
↑dist {t1} {t2} =
  max-sucMono ≤-refl
  , max-LUB (≤-sucMono max-≤L) (≤-sucMono max-≤R)
\end{code}

\subsection{Characterizing Limits}
Finally, we present some equations regarding joins and limits.
Since limits are essentially (possibly-)infinitary joins, we write
them using $\bigvee$.
\begin{code}
⋁ : ∀ {c} → (El c → SMBTree) → SMBTree
⋁ f = Lim _ f
\end{code}
Limits are an upper bound, so joining any element from a sequence with the limit of that sequence
has no effect:
\begin{code}
⋁-Bound : ∀ {c : ℂ} {f : El c → SMBTree} {k}
  → f k ∨ (⋁ f) ≈ ⋁ f
⋁-Bound = ord→equiv (≤-limUpperBound _)
\end{code}
Moreover, a limit is an actual supremum: the limit of a function
is absorbed by any upper bound of the function's image.
\begin{code}
⋁-Supremum : ∀ {c : ℂ} {f : El c → SMBTree} {t}
    → (∀ k → f k ∨ t ≈  t) → (⋁ f) ∨ t ≈ t
⋁-Supremum {f = f} lt
  =  ord→equiv (≤-limLeast (λ k → equiv→ord (lt k)))
\end{code}

The join of a constant, non-empty sequence is
the singular element of that sequence:
\begin{code}
⋁-const : ∀ {c t}
  → El c
  → Lim c (λ _ → t) ≈ t
⋁-const k = ≤-limLeast (λ _ → ≤-refl) , ≤-limUpperBound k
\end{code}

The join of an empty sequence is zero:
\begin{code}
⋁-empty : ∀ {c f}
  → ¬ (El c)
  → Lim c f ≈ Z
⋁-empty empty
  = (≤-limLeast (λ k → contradiction k empty)) , ≤-Z
\end{code}

More interesting is the interaction between limits and joins.
For two limits over the same index set, the join of those two limits
is the same as the limit of joining the sequences together.
\begin{code}
⋁-distHomo : ∀ {c : ℂ} {f g : El c → SMBTree}
  → (Lim c f) ∨ (Lim c g) ≈ Lim c (λ x → f x ∨ g x)
⋁-distHomo
  = max-LUB
      (≤-extLim (λ _ → max-≤L))
      (≤-extLim (λ _ → max-≤R))
      , ≤-limLeast
        (λ k → max-mono
          (≤-limUpperBound _)
          (≤-limUpperBound _))
\end{code}

We can obtain a more general result, distributing a limit over a join,
so long as the limit is over a non-empty sequence.
The join of a non-zero tree with an empty limit will be non-zero, but pushing
the join under a limit will produce zero, so the following result
only applies to non-empty limits.
\begin{code}
⋁-distHet : ∀ {c : ℂ} {f : El c → SMBTree} {t}
  → El c
  → (⋁ f) ∨ t ≈ ⋁ (λ x → f x ∨ t)
⋁-distHet k
  = max-LUB
     (≤-extLim (λ _ → max-≤L))
     (≤-limUpperBound k ≤⨟ (≤-extLim λ _ → max-≤R))
    , ≤-limLeast (λ k → max-monoL (≤-limUpperBound _) )
\end{code}

\begin{code}[hide]
commut = max-commut _ _ , max-commut _ _

assoc = max-assocL _ _ _ , max-assocR _ _ _

idem = max-idem , max-idem≤


ord→equiv lt = max-LUB lt ≤-refl , max-≤R
equiv→ord (lt , _) = max-≤L ≤⨟ lt

-- ⋁-distHomo = max-swapR , max-swapL
-- ↑ is an inflationary endomorphism

≤-extensional : ∀ {t1 t2} → (∀ x → x ≤ t1 → x ≤ t2) → (∀ x → x ≤ t2 → x ≤ t1) → t1 ≈ t2
≤-extensional {t1} {t2} to from = to t1 ≤-refl , from t2 ≤-refl


≤≈ s1≤t1 (_ , s2≤s1) (t1≤t2 , _) = s2≤s1 ≤⨟ s1≤t1 ≤⨟ t1≤t2
<≈ pf (_ , s2≤s1) (t1≤t2 , _) = ≤-sucMono s2≤s1 ≤⨟ pf ≤⨟ t1≤t2
↑-cong (pf1 , pf2) = (≤-sucMono pf1 , ≤-sucMono pf2)
Lim-cong pf = (≤-extLim (λ k → proj₁ (pf k)) , ≤-extLim λ k → proj₂ (pf k))
max-cong (pfs1 , pfs2) (pft1 , pft2) = max-mono pfs1 pft1 , max-mono pfs2 pft2

\end{code}
