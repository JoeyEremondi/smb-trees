
\section{An Algebraic Perspective}

\begin{code}[hide]
open import Iso
open import Data.Nat hiding (_≤_)
open import Data.Product
open import Relation.Binary.Lattice
open import Relation.Binary
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

\begin{code}
    TreeSemiLat : BoundedJoinSemilattice ℓ ℓ ℓ
    Carrier TreeSemiLat = SMBTree
    _≈_ TreeSemiLat t1 t2 = t1 SMBTree.≤ t2 × t2 SMBTree.≤ t1
    _≤_ TreeSemiLat = SMBTree._≤_
    _∨_ TreeSemiLat = max
    ⊥ TreeSemiLat = Z
\end{code}

\begin{code}[hide]
    isBoundedJoinSemilattice TreeSemiLat = treeBoundedSemi


open BoundedJoinSemilattice SemiLatMod.TreeSemiLat
\end{code}

\begin{code}
ord→equiv : ∀ {t1 t2} → t1 ≤ t2 → t1 ∨ t2 ≈ t2
equiv→ord : ∀ {t1 t2} → t1 ∨ t2 ≈ t2 → t1 ≤ t2
\end{code}

\begin{code}
--A semilattice is commutative, associative and idempotent
assoc : ∀ {t1 t2 t3} → t1 ∨ (t2 ∨ t3) ≈ (t1 ∨ t2) ∨ t3
commut : ∀ {t1 t2} → t1 ∨ t2 ≈ t2 ∨ t1
idem : ∀ {t} → t ∨ t ≈ t
\end{code}

\begin{code}
↑absorb : ∀ {t} → t ∨ (↑ t) ≈ ↑ t
↑absorb =
  max-mono (≤↑ _) ≤-refl ≤⨟ max-idem
  , max-≤R

↑dist : ∀ {t1 t2} → ↑ (t1  ∨ t2) ≈ ↑ t1 ∨ ↑ t2
↑dist {t1} {t2} =
  max-sucMono ≤-refl
  , max-LUB (≤-sucMono max-≤L) (≤-sucMono max-≤R)
\end{code}

\begin{code}

-- We can take infinite joins over any code-indexed set
⋁ : ∀ {c} → (El c → SMBTree) → SMBTree
⋁ f = Lim _ f

⋁-Supremum : ∀ {c : ℂ} {f : El c → SMBTree}
  → (∀ {k} → f k ∨ (⋁ f) ≈ ⋁ f )
    × (∀ {t} → (∀ k → f k ∨ t ≈  t) → (⋁ f) ∨ t ≈ t  )
⋁-Supremum {f = f}
  = ord→equiv (≤-limUpperBound _)
    , λ lt → ord→equiv (≤-limLeast (λ k → equiv→ord (lt k)))

-- Infinite joins distribute with finite ones over the same index set
⋁-dist : ∀ {c : ℂ} {f g : El c → SMBTree} →
  (Lim c f) ∨ (Lim c g) ≈ Lim c (λ x → f x ∨ g x)
⋁-dist = max-swapR , max-swapL
\end{code}

\begin{code}[hide]
commut = max-commut _ _ , max-commut _ _

assoc = max-assocL _ _ _ , max-assocR _ _ _

idem = max-idem , max-idem≤


ord→equiv lt = max-LUB lt ≤-refl , max-≤R
equiv→ord (lt , _) = max-≤L ≤⨟ lt

-- ↑ is an inflationary endomorphism







\end{code}
