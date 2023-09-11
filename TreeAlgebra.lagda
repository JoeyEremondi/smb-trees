
\begin{code}[hide]
open import Iso
open import Data.Nat hiding (_≤_)
open import Data.Product
open import Relation.Binary.Lattice
open import Relation.Binary
\end{code}

\begin{code}
module TreeAlgebra {ℓ}
    (ℂ : Set ℓ)
    (El : ℂ → Set ℓ)
    (Cℕ : ℂ) (CℕIso : Iso (El Cℕ) ℕ ) where

open import Idem ℂ El Cℕ CℕIso renaming (_≤_ to _≤'_)



module SemiLatMod where
    open BoundedJoinSemilattice
    open IsJoinSemilattice
    open IsPartialOrder
    open IsPreorder

    treeIsSemiLat : IsJoinSemilattice (λ t1 t2 → t1 ≤' t2 × t2 ≤' t1) _≤'_ max
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

    treeBoundedSemi : IsBoundedJoinSemilattice (λ t1 t2 → t1 ≤' t2 × t2 ≤' t1) _≤'_ max Z
    IsBoundedJoinSemilattice.isJoinSemilattice treeBoundedSemi = treeIsSemiLat
    IsBoundedJoinSemilattice.minimum treeBoundedSemi _ = ≤-Z

    TreeSemiLat : BoundedJoinSemilattice ℓ ℓ ℓ
    Carrier TreeSemiLat = Tree
    _≈_ TreeSemiLat t1 t2 = t1 ≤' t2 × t2 ≤' t1
    _≤_ TreeSemiLat = _≤'_
    _∨_ TreeSemiLat = max
    ⊥ TreeSemiLat = Z
    isBoundedJoinSemilattice TreeSemiLat = treeBoundedSemi

open BoundedJoinSemilattice SemiLatMod.TreeSemiLat

-- ↑ is an inflationary endomorphism

↑absorb : ∀ {t} → t ∨ (↑ t) ≈ ↑ t
↑absorb =
  max-mono (≤↑ _) ≤-refl ≤⨟ max-idem
  , max-≤R

↑dist : ∀ {t1 t2} → ↑ (t1  ∨ t2) ≈ ↑ t1 ∨ ↑ t2
↑dist {t1} {t2} =
  max-sucMono ≤-refl
  , max-LUB (≤-sucMono max-≤L) (≤-sucMono max-≤R)

-- We can take infinite joins over any code-indexed set
⋁-Supremum : ∀ {c : ℂ} {f : El c → Tree}
  → Σ[ sup ∈ Tree ]
    (∀ k → f k ≤ sup )
    × (∀ t → (∀ k → f k ≤ t) → sup ≤ t )
⋁-Supremum {f = f}
  = Lim _ f
    , ≤-limUpperBound
    , λ t → ≤-limLeast

-- Infinite joins distribute with finite ones over the same index set
⋁-dist : ∀ {c : ℂ} {f g : El c → Tree} →
  (Lim c f) ∨ (Lim c g) ≈ Lim c (λ x → f x ∨ g x)
⋁-dist = max-swapR , max-swapL



\end{code}
