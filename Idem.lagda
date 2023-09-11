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


record _≤_ (t1 t2 : Tree) : Set ℓ where
  constructor mk≤
  inductive
  field
    get≤ : (sTree t1) Raw.≤ (sTree t2)
open _≤_

opaque
  unfolding indMax

  Z : Tree
  Z = MkTree Raw.Z Raw.≤-Z


  ↑ : Tree → Tree
  ↑ (MkTree o pf) = MkTree (Raw.↑ o) ( subst (λ x → x Raw.≤ Raw.↑ o) (sym indMax-↑) (Raw.≤-sucMono pf) )

  ≤↑ : ∀ t → t ≤ ↑ t
  ≤↑ t =  mk≤ (Raw.≤↑t _)


_<_ : Tree → Tree → Set ℓ
_<_ t1 t2 = (↑ t1) ≤ t2

opaque
  unfolding indMax Z ↑ indMaxView
  max : Tree → Tree → Tree
  max t1 t2 = MkTree (indMax (sTree t1) (sTree t2)) (indMax-swap4 Raw.≤⨟ indMax-mono (sIdem t1) (sIdem t2))

  Lim : ∀   (c : ℂ) → (f : El c → Tree) → Tree
  Lim c f =
    MkTree
    (indMax∞ (Raw.Lim c (maybe′ (λ x → sTree (f x)) Raw.Z)))
    (indMax∞-idem _)

--MkTree (indMax∞ (Lim c (λ x → sTree (f x)))) ( indMax∞-idem (Lim c (λ x → sTree (f x))) )


  ≤-Z : ∀ {t} → Z ≤ t
  ≤-Z =  mk≤ Raw.≤-Z

  ≤-sucMono : ∀ {t1 t2} → t1 ≤ t2 → ↑ t1 ≤ ↑ t2
  ≤-sucMono (mk≤ lt) = mk≤ (Raw.≤-sucMono lt)

  infixr 10 _≤⨟_
  _≤⨟_ : ∀ {t1 t2 t3} → t1 ≤ t2 → t2 ≤ t3 → t1 ≤ t3
  _≤⨟_ (mk≤ lt1) (mk≤ lt2) = mk≤ (Raw.≤-trans lt1 lt2)


  ≤-refl : ∀ {t} → t ≤ t
  ≤-refl =  mk≤ (Raw.≤-refl _)

  ≤-limUpperBound : ∀   {c : ℂ} → {f : El c → Tree}
    → ∀ k → f k ≤ Lim c f
  ≤-limUpperBound {c = c} {f = f} k = mk≤ (Raw.≤-cocone _ (just k) (Raw.≤-refl _) Raw.≤⨟ indMax∞-self (Raw.Lim c _))

  ≤-limLeast : ∀   {c : ℂ} → {f : El c → Tree}
    → {t : Tree}
    → (∀ k → f k ≤ t) → Lim c f ≤ t
  ≤-limLeast {f = f} {t = MkTree o idem} lt
    = mk≤ (
        indMax∞-mono (Raw.≤-limiting _ (maybe (λ k → get≤ (lt k)) Raw.≤-Z))
        Raw.≤⨟ (indMax∞-≤ idem) )

  ≤-extLim : ∀  {c : ℂ} → {f1 f2 : El c → Tree}
    → (∀ k → f1 k ≤ f2 k)
    → Lim c f1 ≤ Lim c f2
  ≤-extLim lt = ≤-limLeast (λ k → lt k ≤⨟ ≤-limUpperBound k)

  ≤-extExists : ∀  {c1 c2 : ℂ} → {f1 : El c1 → Tree} {f2 : El c2 → Tree}
    → (∀ k1 → Σ[ k2 ∈ El c2 ] f1 k1 ≤ f2 k2)
    → Lim c1 f1 ≤ Lim c2 f2
  ≤-extExists {f1 = f1} {f2} lt = ≤-limLeast (λ k1 → proj₂ (lt k1) ≤⨟ ≤-limUpperBound (proj₁ (lt k1)))

  --≤-limLeast (λ k1 → proj₂ (lt k1) ≤⨟ ≤-limUpperBound (proj₁ (lt k1)))

  ¬Z<↑ : ∀  t → ¬ ((↑ t) ≤ Z)
  ¬Z<↑ t pf = Raw.¬<Z (sTree t) (get≤ pf)

  max-≤L : ∀ {t1 t2} → t1 ≤ max t1 t2
  max-≤L = mk≤ indMax-≤L

  max-≤R : ∀ {t1 t2} → t2 ≤ max t1 t2
  max-≤R =  mk≤ indMax-≤R

  max-mono : ∀ {t1 t1' t2 t2'} → t1 ≤ t1' → t2 ≤ t2' →
    max t1 t2 ≤ max t1' t2'
  max-mono lt1 lt2 = mk≤ (indMax-mono (get≤ lt1) (get≤ lt2))

  max-monoR : ∀ {t1 t2 t2'} → t2 ≤ t2' → max t1 t2 ≤ max t1 t2'
  max-monoR {t1} {t2} {t2'} lt = max-mono {t1 = t1} {t1' = t1} {t2 = t2} {t2' = t2'} (≤-refl {t1}) lt

  max-monoL : ∀ {t1 t1' t2} → t1 ≤ t1' → max t1 t2 ≤ max t1' t2
  max-monoL {t1} {t1'} {t2} lt = max-mono {t1} {t1'} {t2} {t2} lt (≤-refl {t2})

  max-idem : ∀ {t} → max t t ≤ t
  max-idem {t = MkTree o pf} = mk≤ pf

  max-idem≤ : ∀ {t} → t ≤ max t t
  max-idem≤ {t = MkTree o pf} = max-≤L

  max-LUB : ∀ {t1 t2 t} → t1 ≤ t → t2 ≤ t → max t1 t2 ≤ t
  max-LUB lt1 lt2 = max-mono lt1 lt2 ≤⨟ max-idem

  max-commut : ∀ t1 t2 → max t1 t2 ≤ max t2 t1
  max-commut t1 t2 =  mk≤ (indMax-commut (sTree t1) (sTree t2))

  max-assocL : ∀ t1 t2 t3 → max t1 (max t2 t3) ≤ max (max t1 t2) t3
  max-assocL t1 t2 t3 = mk≤ (indMax-assocL _ _ _)

  max-assocR : ∀ t1 t2 t3 →  max (max t1 t2) t3 ≤ max t1 (max t2 t3)
  max-assocR t1 t2 t3 = mk≤ (indMax-assocR _ _ _)

  max-swap4 : ∀ {t1 t1' t2 t2'} → max (max t1 t1') (max t2 t2') ≤ max (max t1 t2) (max t1' t2')
  max-swap4 =  mk≤ indMax-swap4

  max-strictMono : ∀ {t1 t1' t2 t2'} → t1 < t1' → t2 < t2' → max t1 t2 < max t1' t2'
  max-strictMono lt1 lt2 = mk≤ (indMax-strictMono (get≤ lt1) (get≤ lt2))

  max-sucMono : ∀ {t1 t2 t1' t2'} → max t1 t2 ≤ max t1' t2' → max t1 t2 < max (↑ t1') (↑ t2')
  max-sucMono lt =  mk≤ (indMax-sucMono (get≤ lt))



ℕLim : (ℕ → Tree) → Tree
ℕLim f = Lim Cℕ  (λ cn → f (Iso.fun CℕIso cn))

max' : Tree → Tree → Tree
max' t1 t2 = ℕLim (λ n → if0 n t1 t2)

max'-≤L : ∀ {t1 t2} → t1 ≤ max' t1 t2
max'-≤L {t1} {t2}
    = subst (λ x → t1 ≤ if0 x t1 t2) (sym (Iso.rightInv CℕIso 0)) ≤-refl ≤⨟
      ≤-limUpperBound  (Iso.inv CℕIso 0)

max'-≤R : ∀ {t1 t2} → t2 ≤ max' t1 t2
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


max'-LUB : ∀ {t1 t2 t} → t1 ≤ t → t2 ≤ t → max' t1 t2 ≤ t
max'-LUB lt1 lt2 = max'-Mono lt1 lt2 ≤⨟ max'-Idem



max≤max' : ∀ {t1 t2} → max t1 t2 ≤ max' t1 t2
max≤max' = max-LUB max'-≤L max'-≤R


max'≤max : ∀ {t1 t2} → max' t1 t2 ≤ max t1 t2
max'≤max = max'-LUB max-≤L max-≤R


limSwap : ∀ {c1 c2 } {f : El c1 → El c2 → Tree} → (Lim c1 λ x → Lim c2 λ y → f x y) ≤ Lim c2 λ y → Lim c1 λ x → f x y
limSwap = ≤-limLeast (λ x → ≤-limLeast λ y → ≤-limUpperBound x ≤⨟ ≤-limUpperBound y   )

max-swapL : ∀ {c} {f g : El c → Tree} →  Lim c (λ k → max (f k) (g k)) ≤ max (Lim c f) (Lim c g)
max-swapL {c} {f} {g} = ≤-extLim (λ k → max≤max') ≤⨟ limSwap ≤⨟ ≤-extLim helper ≤⨟ max'≤max
  where
    helper : (k : El Cℕ) →
      Lim c (λ x → if0 (Iso.fun CℕIso k) (f x) (g x)) ≤
      if0 (Iso.fun CℕIso k) (Lim c f) (Lim c g)
    helper kn with Iso.fun CℕIso kn
    ... | zero = ≤-refl
    ... | suc n = ≤-refl


max-swapR : ∀ {c} {f g : El c → Tree} → max (Lim c f) (Lim c g) ≤ Lim c (λ k → max (f k) (g k))
max-swapR {c} {f} {g} = max≤max' ≤⨟ ≤-extLim helper ≤⨟ limSwap ≤⨟ ≤-extLim (λ k → max'≤max) 
  where
    helper : (k : El Cℕ) →
      if0 (Iso.fun CℕIso k) (Lim c f) (Lim c g) ≤
      Lim c (λ z → if0 (Iso.fun CℕIso k) (f z) (g z))
    helper kn with Iso.fun CℕIso kn
    ... | zero = ≤-refl
    ... | suc n = ≤-refl

\end{code}
