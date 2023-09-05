% !TEX root =  main.tex

\section{A Strictly-Monotone, Idempotent Join}

\begin{code}[hide]
open import Data.Nat hiding (_≤_ ; _<_)
open import Relation.Binary.PropositionalEquality
open import Data.Product
open import Data.Maybe
open import Relation.Nullary
open import Iso
  \end{code}

\begin{code}
module Idem {ℓ}
    (ℂ : Set ℓ)
    (El : ℂ → Set ℓ)
    (Cℕ : ℂ) (CℕIso : Iso (El Cℕ) ℕ ) where

module Raw where
  open import RawTree ℂ (λ c → Maybe (El c)) Cℕ (maybeNatIso CℕIso) public
  \end{code}

\begin{code}[hide]
open import IndMax ℂ (λ c → Maybe (El c)) Cℕ (maybeNatIso CℕIso) (λ c → nothing)
open import InfinityMax ℂ (λ c → Maybe (El c)) Cℕ (maybeNatIso CℕIso) (λ c → nothing)
\end{code}

\begin{code}



record Tree : Set ℓ where
  constructor MkTree
  field
    sTree : Raw.Tree
    sIdem : (indMax sTree sTree) Raw.≤ sTree
open Tree


record _≤_ (s1 s2 : Tree) : Set ℓ where
  constructor mk≤
  inductive
  field
    get≤ : (sTree s1) Raw.≤ (sTree s2)
open _≤_

opaque
  unfolding indMax

  Z : Tree
  Z = MkTree Raw.Z Raw.≤-Z


  ↑ : Tree → Tree
  ↑ (MkTree o pf) = MkTree (Raw.↑ o) ( subst (λ x → x Raw.≤ Raw.↑ o) (sym indMax-↑) (Raw.≤-sucMono pf) )

  ≤↑ : ∀ s → s ≤ ↑ s
  ≤↑ s =  mk≤ (Raw.≤↑t _)


_<_ : Tree → Tree → Set ℓ
_<_ s1 s2 = (↑ s1) ≤ s2

opaque
  unfolding indMax Z ↑
  max : Tree → Tree → Tree
  max s1 s2 = MkTree (indMax (sTree s1) (sTree s2)) (indMax-swap4 Raw.≤⨟ indMax-mono (sIdem s1) (sIdem s2))

  Lim : ∀   (c : ℂ) → (f : El c → Tree) → Tree
  Lim c f =
    MkTree
    (indMax∞ (Raw.Lim c (maybe′ (λ x → sTree (f x)) Raw.Z)))
    (indMax∞-idem _)
--MkTree (indMax∞ (Lim c (λ x → sTree (f x)))) ( indMax∞-idem (Lim c (λ x → sTree (f x))) )


  ≤-Z : ∀ {s} → Z ≤ s
  ≤-Z =  mk≤ Raw.≤-Z

  ≤-sucMono : ∀ {s1 s2} → s1 ≤ s2 → ↑ s1 ≤ ↑ s2
  ≤-sucMono (mk≤ lt) = mk≤ (Raw.≤-sucMono lt)

  infixr 10 _≤⨟_
  _≤⨟_ : ∀ {s1 s2 s3} → s1 ≤ s2 → s2 ≤ s3 → s1 ≤ s3
  _≤⨟_ (mk≤ lt1) (mk≤ lt2) = mk≤ (Raw.≤-trans lt1 lt2)


  ≤-refl : ∀ {s} → s ≤ s
  ≤-refl =  mk≤ (Raw.≤-refl _)

  ≤-cocone : ∀   {c : ℂ} → {f : El c → Tree}
    → ∀ k → f k ≤ Lim c f
  ≤-cocone {c = c} {f = f} k = mk≤ (Raw.≤-cocone _ (just k) (Raw.≤-refl _) Raw.≤⨟ indMax∞-self (Raw.Lim c _))

  ≤-limiting : ∀   {c : ℂ} → {f : El c → Tree}
    → {s : Tree}
    → (∀ k → f k ≤ s) → Lim c f ≤ s
  ≤-limiting {f = f} {s = MkTree o idem} lt
    = mk≤ (
        indMax∞-mono (Raw.≤-limiting _ (maybe (λ k → get≤ (lt k)) Raw.≤-Z))
        Raw.≤⨟ (indMax∞-≤ idem) )

  ≤-extLim : ∀  {c : ℂ} → {f1 f2 : El c → Tree}
    → (∀ k → f1 k ≤ f2 k)
    → Lim c f1 ≤ Lim c f2
  ≤-extLim lt = ≤-limiting (λ k → lt k ≤⨟ ≤-cocone k)

  ≤-extExists : ∀  {c : ℂ} → {f1 f2 : El c → Tree}
    → (∀ k1 → Σ[ k2 ∈ El c ] f1 k1 ≤ f2 k2)
    → Lim c f1 ≤ Lim c f2
  ≤-extExists {f1 = f1} {f2} lt = ≤-limiting (λ k1 → proj₂ (lt k1) ≤⨟ ≤-cocone (proj₁ (lt k1)))

  ¬Z<↑ : ∀  s → ¬ ((↑ s) ≤ Z)
  ¬Z<↑ s pf = Raw.¬<Z (sTree s) (get≤ pf)

  max-≤L : ∀ {s1 s2} → s1 ≤ max s1 s2
  max-≤L = mk≤ indMax-≤L

  max-≤R : ∀ {s1 s2} → s2 ≤ max s1 s2
  max-≤R =  mk≤ indMax-≤R

  max-mono : ∀ {s1 s1' s2 s2'} → s1 ≤ s1' → s2 ≤ s2' →
    max s1 s2 ≤ max s1' s2'
  max-mono lt1 lt2 = mk≤ (indMax-mono (get≤ lt1) (get≤ lt2))

  max-monoR : ∀ {s1 s2 s2'} → s2 ≤ s2' → max s1 s2 ≤ max s1 s2'
  max-monoR {s1} {s2} {s2'} lt = max-mono {s1 = s1} {s1' = s1} {s2 = s2} {s2' = s2'} (≤-refl {s1}) lt

  max-monoL : ∀ {s1 s1' s2} → s1 ≤ s1' → max s1 s2 ≤ max s1' s2
  max-monoL {s1} {s1'} {s2} lt = max-mono {s1} {s1'} {s2} {s2} lt (≤-refl {s2})

  max-idem : ∀ {s} → max s s ≤ s
  max-idem {s = MkTree o pf} = mk≤ pf

  max-LUB : ∀ {t1 t2 t} → t1 ≤ t → t2 ≤ t → max t1 t2 ≤ t
  max-LUB lt1 lt2 = max-mono lt1 lt2 ≤⨟ max-idem

  max-commut : ∀ s1 s2 → max s1 s2 ≤ max s2 s1
  max-commut s1 s2 =  mk≤ (indMax-commut (sTree s1) (sTree s2))

  max-assocL : ∀ s1 s2 s3 → max s1 (max s2 s3) ≤ max (max s1 s2) s3
  max-assocL s1 s2 s3 = mk≤ (indMax-assocL _ _ _)

  max-assocR : ∀ s1 s2 s3 →  max (max s1 s2) s3 ≤ max s1 (max s2 s3)
  max-assocR s1 s2 s3 = mk≤ (indMax-assocR _ _ _)

  max-swap4 : ∀ {s1 s1' s2 s2'} → max (max s1 s1') (max s2 s2') ≤ max (max s1 s2) (max s1' s2')
  max-swap4 =  mk≤ indMax-swap4

  max-strictMono : ∀ {s1 s1' s2 s2'} → s1 < s1' → s2 < s2' → max s1 s2 < max s1' s2'
  max-strictMono lt1 lt2 = mk≤ (indMax-strictMono (get≤ lt1) (get≤ lt2))

  max-sucMono : ∀ {s1 s2 s1' s2'} → max s1 s2 ≤ max s1' s2' → max s1 s2 < max (↑ s1') (↑ s2')
  max-sucMono lt =  mk≤ (indMax-sucMono (get≤ lt))
\end{code}
