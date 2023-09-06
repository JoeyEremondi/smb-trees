

\subsection{Limit-based Maximum}

\begin{code}[hide]
  open import Data.Nat hiding (_≤_ ; _<_)
  open import Relation.Binary.PropositionalEquality
  open import Data.Product
  open import Relation.Nullary
  open import Iso
  module LimMax {ℓ}
    (ℂ : Set ℓ)
    (El : ℂ → Set ℓ)
    (Cℕ : ℂ) (CℕIso : Iso (El Cℕ) ℕ ) where
    open import RawTree ℂ El Cℕ CℕIso
\end{code}

\begin{code}


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
