

\subsection{Limit-based Maximum}

Since the limit constructor finds the least upper bound
of the image of a function, it should be possible to define
the maximum of two trees as a special case of general limits.
Indeed, we can compute the maximum of $t_1$ and $t_2$ as the limit
of the function that produces $t_1$ when given $0$ and $t_2$ otherwise.

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
maximum function: it is monotone, idempotent,
commutative, and is a true least-upper-bound of its inputs.

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

The one crucial property that this formulation lacks is that it is not
strictly monotone: we cannot deduce $\max\ t_1\ t_1 < \max\ t'_1 \ t'_2 $
from $t_1 < t'_1$ and $t_2 < t'_2$. This is because the only way to construct a
proof that $\up t \le \Lim\ c\ f$
is using the $\cocone$ constructor. So we would need to prove that
$\up (\max\ t_{1} \ t_{2}) \le t'_{1}$ or that
$\up (\max\ t_{1} \ t_{2}) \le t'_{2}$, which cannot be deduced from the
premises alone.
%
What we want is to have $\up \max\ (t_{1}) \ t_{2} \le \max (\up t_{1})\ (\up t_{2})$, so that strict monotonicity is a direct consequence of ordinary
monotonicity of the maximum. This is not possible when defining the constructor as a limit.
