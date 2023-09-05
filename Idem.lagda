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
  open import RawTree ℂ (λ c → Maybe (El c)) Cℕ (maybeNatIso CℕIso)
-- open IndMaxInhab (λ _ → nothing)



-- record Tree : Set ℓ where
--   constructor MkJIB
--   field
--     sTree : Tree
--     sIdem : indMax sTree sTree ≤ sTree
-- open Tree


-- record _≤'_ (s1 s2 : Tree) : Set ℓ where
--   constructor mk≤
--   inductive
--   field
--     get≤ : sTree s1 ≤ sTree s2
-- open _≤'_

-- opaque
--   unfolding indMax
--   max : Tree → Tree → Tree
--   max s1 s2 = MkJIB (indMax (sTree s1) (sTree s2)) (indMax-swap4 ≤⨟ indMax-mono (sIdem s1) (sIdem s2))


-- --   SZ : Tree
-- --   SZ = MkJIB Z Raw.≤-Z


-- --   S↑ : Tree → Tree
-- --   S↑ (MkJIB o pf) = MkJIB (↑ o) ( subst (λ x → x ≤ ↑ o) (sym indMax-↑) (≤-sucMono pf) )

-- --   ≤↑' : ∀ s → s ≤' S↑ s
-- --   ≤↑' s =  mk≤ (≤↑t _)

-- --   _<'_ : Tree → Tree → Set ℓ
-- --   _<'_ s1 s2 = (S↑ s1) ≤' s2




-- --   SLim : ∀   (c : ℂ) → (f : El c → Tree) → Tree
-- --   SLim c f =
-- --     MkJIB
-- --     (indMax∞ (Lim c (maybe′ (λ x → sTree (f x)) Z)))
-- --     (indMax∞-idem _)
-- -- --MkJIB (indMax∞ (Lim c (λ x → sTree (f x)))) ( indMax∞-idem (Lim c (λ x → sTree (f x))) )


-- --   ≤'-Z : ∀ {s} → SZ ≤' s
-- --   ≤'-Z =  mk≤ ≤-Z

-- --   ≤'-sucMono : ∀ {s1 s2} → s1 ≤' s2 → S↑ s1 ≤' S↑ s2
-- --   ≤'-sucMono (mk≤ lt) = mk≤ (≤-sucMono lt)

-- --   infixr 10 _≤⨟'_
-- --   _≤⨟'_ : ∀ {s1 s2 s3} → s1 ≤' s2 → s2 ≤' s3 → s1 ≤' s3
-- --   _≤⨟'_ (mk≤ lt1) (mk≤ lt2) = mk≤ (≤-trans lt1 lt2)


-- --   ≤'-refl : ∀ {s} → s ≤' s
-- --   ≤'-refl =  mk≤ (≤-refl _)

-- --   ≤'-cocone : ∀   {c : ℂ} → {f : El c → Tree}
-- --     → ∀ k → f k ≤' SLim c f
-- --   ≤'-cocone {c = c} {f = f} k = mk≤ (≤-cocone _ (just k) (≤-refl _) ≤⨟ indMax∞-self (Lim c _))

-- --   ≤'-limiting : ∀   {c : ℂ} → {f : El c → Tree}
-- --     → {s : Tree}
-- --     → (∀ k → f k ≤' s) → SLim c f ≤' s
-- --   ≤'-limiting {f = f} {s = MkJIB o idem} lt = mk≤ (≤-trans (indMax∞-mono (≤-limiting _ λ k → get≤ (lt k)))  (indMax∞-≤ idem))

-- -- --   ≤'-extLim : ∀  {c : ℂ} → {f1 f2 : El c → Tree}
-- -- --     → (∀ k → f1 k ≤' f2 k)
-- -- --     → SLim c f1 ≤' SLim c f2
-- -- --   ≤'-extLim {f1 = f1} {f2} lt = mk≤ ( indMax∞-mono (extLim (λ x → sTree (f1 x)) (λ x → sTree (f2 x)) λ k → get≤ (lt k)))

-- -- --   ≤'-extExists : ∀  {c : ℂ} → {f1 f2 : El c → Tree}
-- -- --     → (∀ k1 → Σ[ k2 ∈ El c ] f1 k1 ≤' f2 k2)
-- -- --     → SLim c f1 ≤' SLim c f2
-- -- --   ≤'-extExists {f1 = f1} {f2} lt = ≤'-limiting (λ k1 → proj₂ (lt k1) ≤⨟ ≤'-cocone (proj₁ (lt k1)))

-- -- --   ¬Z<↑ : ∀  s → ¬ ((S↑ s) ≤' SZ)
-- -- --   ¬Z<↑ s pf = ¬<Z (sTree s) (get≤ pf)

-- -- --   max-≤L : ∀ {s1 s2} → s1 ≤' max s1 s2
-- -- --   max-≤L = mk≤ indMax-≤L

-- -- --   max-≤R : ∀ {s1 s2} → s2 ≤' max s1 s2
-- -- --   max-≤R =  mk≤ indMax-≤R

-- -- --   max-mono : ∀ {s1 s1' s2 s2'} → s1 ≤' s1' → s2 ≤' s2' →
-- -- --     max s1 s2 ≤' max s1' s2'
-- -- --   max-mono lt1 lt2 = mk≤ (indMax-mono (get≤ lt1) (get≤ lt2))

-- -- --   max-monoR : ∀ {s1 s2 s2'} → s2 ≤' s2' → max s1 s2 ≤' max s1 s2'
-- -- --   max-monoR {s1} {s2} {s2'} lt = max-mono {s1 = s1} {s1' = s1} {s2 = s2} {s2' = s2'} (≤'-refl {s1}) lt

-- -- --   max-monoL : ∀ {s1 s1' s2} → s1 ≤' s1' → max s1 s2 ≤' max s1' s2
-- -- --   max-monoL {s1} {s1'} {s2} lt = max-mono {s1} {s1'} {s2} {s2} lt (≤'-refl {s2})

-- -- --   max-idem : ∀ {s} → max s s ≤' s
-- -- --   max-idem {s = MkJIB o pf} = mk≤ pf

-- -- --   max-commut : ∀ s1 s2 → max s1 s2 ≤' max s2 s1
-- -- --   max-commut s1 s2 =  mk≤ (indMax-commut (sTree s1) (sTree s2))

-- -- --   max-assocL : ∀ s1 s2 s3 → max s1 (max s2 s3) ≤' max (max s1 s2) s3
-- -- --   max-assocL s1 s2 s3 = mk≤ (indMax-assocL _ _ _)

-- -- --   max-assocR : ∀ s1 s2 s3 →  max (max s1 s2) s3 ≤' max s1 (max s2 s3)
-- -- --   max-assocR s1 s2 s3 = mk≤ (indMax-assocR _ _ _)

-- -- --   max-swap4 : ∀ {s1 s1' s2 s2'} → max (max s1 s1') (max s2 s2') ≤' max (max s1 s2) (max s1' s2')
-- -- --   max-swap4 =  mk≤ indMax-swap4

-- -- --   max-strictMono : ∀ {s1 s1' s2 s2'} → s1 <' s1' → s2 <' s2' → max s1 s2 <' max s1' s2'
-- -- --   max-strictMono lt1 lt2 = mk≤ (indMax-strictMono (get≤ lt1) (get≤ lt2))

-- -- --   max-sucMono : ∀ {s1 s2 s1' s2'} → max s1 s2 ≤' max s1' s2' → max s1 s2 <' max (S↑ s1') (S↑ s2')
-- -- --   max-sucMono lt =  mk≤ (indMax-sucMono (get≤ lt))
-- -- -- \end{code}
