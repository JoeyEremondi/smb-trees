
% !TEX root =  main.tex



\subsection{Well-Behaved Trees}


\begin{code}[hide]
  open import Data.Nat hiding (_≤_ ; _<_)
  open import Relation.Binary.PropositionalEquality
  open import Data.Product
  open import Relation.Nullary
  open import Iso
  module InfinityMax {ℓ}
    (ℂ : Set ℓ)
    (El : ℂ → Set ℓ)
    (Cℕ : ℂ) (CℕIso : Iso (El Cℕ) ℕ )
    (default : (c : ℂ) → El c) where
  open import RawTree ℂ El Cℕ CℕIso
  open import IndMax ℂ El Cℕ CℕIso default
\end{code}

\begin{code}

  opaque
    unfolding indMax indMax'
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
