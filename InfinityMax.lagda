
% !TEX root =  main.tex



\subsection{Well-Behaved Trees}
\label{subsec:infinity}

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
  open import Brouwer ℂ El Cℕ CℕIso
  open import IndMax ℂ El Cℕ CℕIso default
  opaque
    unfolding indMax indMax'
\end{code}

Our first step in defining an ordinal notation with a well behaved maximum
is to identify a class of Brouwer trees which are well behaved with
respect to the inductive maximum. As we saw in the previous section, neither
the limit based nor the inductive definition of the maximum was satisfactory.

The solution, it turns out, is more limits:
if we $\indMax$ a term with itself an infinite number of times,
the result will be idempotent with respect to $\indMax$.
First, we define a function to $\indMax$ a term with itself $n$
times or a given number $n$:
\begin{code}
    nindMax : Tree → ℕ → Tree
    nindMax t ℕ.zero = Z
    nindMax t (ℕ.suc n) = indMax (nindMax t n) t
\end{code}

To compute
a tree equivalent to the infinite
chain of applications $\indMax\ t\ (\indMax\ t\ (\indMax\ t\ \ldots))$,
we take the limit of $n$ applications over all $n$:
\begin{code}
    indMax∞ : Tree → Tree
    indMax∞ t =  ℕLim (λ n → nindMax t n)
  \end{code}

This operator has useful basic properties: it is monotone, and it computes
an upper bound on is argument.

\begin{code}
    indMax∞-self : ∀ t → t ≤ indMax∞ t

    indMax∞-mono : ∀ {t1 t2}
      → t1 ≤ t2
      → (indMax∞ t1) ≤ (indMax∞ t2)
    \end{code}

    However, the most important property that we want from $\maxInf$ is that $\indMax$ is idempotent
    with respect to it.
  The first step to showing this is realizing that we can take the maximum of $t$
  and $\maxInf\ t$ and we have a tree that is no larger than $\maxInf\ t$:
  because it is already an infinite chain of applications, adding one more
  makes no difference.
%
\begin{code}
    indMax-∞lt1 : ∀ t → indMax (indMax∞ t) t ≤ indMax∞ t
    indMax-∞lt1 t = ≤-limiting  _ λ k → helper (Iso.fun CℕIso k)
        where
        helper : ∀ n → indMax (nindMax t n) t ≤ indMax∞ t
        helper n =
          ≤-cocone  _ (Iso.inv CℕIso (ℕ.suc n))
          (subst (λ sn → nindMax t (ℕ.suc n) ≤ nindMax t sn)
            (sym (Iso.rightInv CℕIso (suc n)))
            (≤-refl _))
      \end{code}
%
      If adding one more $\indMax\ t$ has no effect, then adding $n$ more will also have no effect:
\begin{code}
    indMax-∞ltn : ∀ n t
      → indMax (indMax∞ t) (nindMax t n) ≤ indMax∞ t
    indMax-∞ltn ℕ.zero t = indMax-≤Z (indMax∞ t)
    indMax-∞ltn (ℕ.suc n) t =
      indMax-monoR
        {t1 = indMax∞ t} (indMax-commut (nindMax t n) t)
      ≤⨟ indMax-assocL (indMax∞ t) t (nindMax t n)
      ≤⨟ indMax-monoL (indMax-∞lt1 t)
      ≤⨟ indMax-∞ltn n t
      \end{code}

      It remains to show that taking $\indMax$ of $\maxInf\ t$ with itself does not make it larger.
      By our inductive definition of $\indMax$, we have that
      \begin{displaymath}
      \indMax\ (\maxInf\ t) (\maxInf\ t)
    \end{displaymath}
    is equal to
    \begin{displaymath}
      \nLim\ (\lambda n \to \indMax\ (\AgdaFunction{nIndMax}\ n\ t)\ (\maxInf\ t) )
    \end{displaymath}
    Our previous lemma gives that, for any $n$, $\maxInf\ t$ is an upper bound for $\indMax\ (\AgdaFunction{nIndMax}\ n\ t)\ (\maxInf\ t) )$.
      So $\limiting$ gives that the limit over all $n$ is also bounded by $\maxInf\ t$, \ie $\Lim$ constructs the least of all upper bounds.
      This gives us our key result: up to $\le$, $\indMax$ is idempotent on values constructed with $\maxInf$.
      \begin{code}
    indMax∞-idem : ∀ t
      → indMax (indMax∞ t) (indMax∞ t) ≤ indMax∞ t
    indMax∞-idem t =
      ≤-limiting  _ λ k →
        (indMax-commut
          (nindMax t (Iso.fun CℕIso k)) (indMax∞ t))
      ≤⨟ indMax-∞ltn (Iso.fun CℕIso k) t
    \end{code}

    There is one last property to prove that will be useful in the next section:
    $\maxInf\ t$  is a lower bound on $t$, and hence equivalent to it,
    whenever $\indMax$ is idempotent on $t$.
    If taking $\indMax$ of $t$ with itself does not increase it size, doing so $n$
    times will not increase it size, so again the result follows from $\Lim$ being
    the least upper bound.
   \begin{code}
    indMax∞-≤ : ∀ {t} → indMax t t ≤ t → indMax∞ t ≤ t
    indMax∞-≤ lt
      = ≤-limiting  _
        λ k → nindMax-≤ (Iso.fun CℕIso k) lt
      where
        nindMax-≤ : ∀ {t} n → indMax t t ≤ t → nindMax t n ≤ t
        nindMax-≤ ℕ.zero lt = ≤-Z
        nindMax-≤ {t = t} (ℕ.suc n) lt
          = indMax-monoL (nindMax-≤ n lt)
            ≤⨟ lt
      \end{code}

      An immediate corollary of this is that $\maxInf\ (\maxInf\ t)$ is equivalent to $\maxInf\ t$.
\begin{code}[hide]

    indMax∞-self t = ≤-cocone  _ (Iso.inv CℕIso 1) (subst (λ x → t ≤ nindMax t x) (sym (Iso.rightInv CℕIso 1)) (≤-refl _))

    indMax∞-mono lt = extLim  _ _ λ k → nindMax-mono (Iso.fun CℕIso k) lt
      where
        nindMax-mono : ∀ {t1 t2 } n → t1 ≤ t2 → nindMax t1 n ≤ nindMax t2 n
        nindMax-mono ℕ.zero lt = ≤-Z
        nindMax-mono {t1 = t1} {t2} (ℕ.suc n) lt = indMax-mono {t1 = nindMax t1 n} {t2 = t1} {t1' = nindMax t2 n} {t2' = t2} (nindMax-mono n lt) lt



    indMax∞-idem∞ : ∀ t → indMax t t ≤ indMax∞ t
    indMax∞-idem∞ t =
      (indMax-mono (indMax∞-self t) (indMax∞-self t))
      ≤⨟ (indMax∞-idem t)

    --Convenient helper for turning < with indMax∞ into < without
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
