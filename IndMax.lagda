
% !TEX root =  main.tex



\subsection{Recursive Maximum}
\label{subsec:indmax}


In our next attempt at defining a maximum operator, we
obtain strict monotonicity by making $\indMax\ (\up t_1) \ (\up t_2) = \up (\indMax\ t_1\ t_2)$
hold definitionally. Then, provided $\indMax$ is monotone, it will also be
strictly monotone.

To do this, we compute the maximum of two trees recursively,
pattern matching on the operands. We use a \textit{view} \citep{mcbridemckinna2004}
datatype to identify the cases we are matching on: we are matching on two arguments,
which each have three possible constructors, but several cases overlap.
Using a view type lets us avoid enumerating all nine possibilities when defining
the maximum and proving its properties.

\begin{code}[hide]
  open import Data.Nat hiding (_≤_ ; _<_ ; _+_)
  open import Relation.Binary.PropositionalEquality
  open import Data.Product
  open import Relation.Nullary
  open import Iso
\end{code}

To begin, we parameterize our definition over a function
yielding some element for any code's type.
Having a representative of every code will be useful in computing
the maximum of a limit and some other tree, since we do not need to handle
the special case where the limit of an empty sequence is zero.
\begin{code}
  module IndMax {ℓ}
    (ℂ : Set ℓ)
    (El : ℂ → Set ℓ)
    (Cℕ : ℂ) (CℕIso : Iso (El Cℕ) ℕ )
    (default : (c : ℂ) → El c) where
\end{code}
\begin{code}[hide]
    open import Brouwer ℂ El Cℕ CℕIso
    underLim : ∀   {c : ℂ}  {t} →  {f : El c → Tree} → (∀ k → t ≤ f k) → t ≤ Lim c f
    underLim {c = c}  {t} {f} all = ≤-trans (≤-cocone (λ _ → t) (default c) (≤-refl t)) (≤-limiting (λ _ → t) (λ k → ≤-cocone f k (all k)))
\end{code}

We then define our view type:
\begin{code}
    private
        data IndMaxView : Tree → Tree → Set ℓ where
          IndMaxZ-L : ∀ {t} → IndMaxView Z t
          IndMaxZ-R : ∀ {t} → IndMaxView t Z
          IndMaxLim-L : ∀ {t} {c : ℂ} {f : El c → Tree}
            → IndMaxView (Lim c f) t
          IndMaxLim-R : ∀ {t} {c : ℂ} {f : El c → Tree}
            → (∀   {c' : ℂ} {f' : El c' → Tree} → ¬ (t ≡ Lim  c' f'))
            → IndMaxView t (Lim c f)
          IndMaxLim-Suc : ∀  {t1 t2 } → IndMaxView (↑ t1) (↑ t2)
    opaque

        indMaxView : ∀ t1 t2 → IndMaxView t1 t2
\end{code}
Our view type has five cases. The first two cases handle when either input
is zero, and the next two cases handle when either input is a limit.
The final case is when both inputs are successors.
The helper $\AgdaFunction{indMaxView}$ computes the view for any pair of trees.

\begin{code}[hide]
        indMaxView Z t2 = IndMaxZ-L
        indMaxView (Lim c f) t2 = IndMaxLim-L
        indMaxView (↑ t1) Z = IndMaxZ-R
        indMaxView (↑ t1) (Lim c f) = IndMaxLim-R λ ()
        indMaxView (↑ t1) (↑ t2) = IndMaxLim-Suc
\end{code}

The maximum is then defined by pattern matching on the view for its arguments:
\begin{code}
        indMax : Tree → Tree → Tree
        indMax' : ∀ {t1 t2} → IndMaxView t1 t2 → Tree

        indMax t1 t2 = indMax' (indMaxView t1 t2)
        indMax' {.Z} {t2} IndMaxZ-L = t2
        indMax' {t1} {.Z} IndMaxZ-R = t1
        indMax' {Lim c f} {t2} IndMaxLim-L
            = Lim c λ x → indMax (f x) t2
        indMax' {t1} {Lim c f} (IndMaxLim-R _)
            = Lim c (λ x → indMax t1 (f x))
        indMax' {↑ t1} {↑ t2} IndMaxLim-Suc = ↑ (indMax t1 t2)
  \end{code}
The maximum of zero and $t$ is always $t$, and the maximum of $t$ and the limit of $f$
is the limit of the function computing the maximum between $t$ and $f\ x$.
Finally, the maximum of two successors is the successor of the two maxima,
giving the definitional equality we need for strict monotonicity.

This definition only works when limits of all codes are inhabited.
The $\limiting$ constructor means that
$\Lim\ c\ f \le \AgdaInductiveConstructor{Z}$ whenever $\AgdaBound{El}\ c$
is uninhabited. So $\indMax\ \up\AgdaInductiveConstructor{Z}\ \Lim\ c\ f$
will not actually be an upper bound for  $\up\AgdaInductiveConstructor{Z}$
if $c$ has no inhabitants.
In \cref{subsec:smb} we show how to circumvent this restriction.

Under the assumption that all code are inhabited, we obtain several
of our desired properties for a maximum: it is an upper bound,
it is monotone and strictly monotone, and it is associative and commutative.
The proof bodies are omitted: they are straightforward reasoning by cases, but they are long and tedious.
  \begin{code}

    opaque
        unfolding indMax indMax'

        indMax-≤L : ∀ {t1 t2} → t1 ≤ indMax t1 t2
        indMax-≤L {t1} {t2} with indMaxView t1 t2
        ... | IndMaxZ-L = ≤-Z
        ... | IndMaxZ-R = ≤-refl _
        ... | IndMaxLim-L {f = f}
          = extLim f (λ x → indMax (f x) t2) (λ k → indMax-≤L)
        ... | IndMaxLim-R {f = f} _
          = underLim  λ k → indMax-≤L {t2 = f k}
        ... | IndMaxLim-Suc
          = ≤-sucMono indMax-≤L

        indMax-≤R : ∀ {t1 t2} → t2 ≤ indMax t1 t2
        -- Symmetric

        indMax-monoL : ∀ {t1 t1' t2}
          → t1 ≤ t1' → indMax t1 t2 ≤ indMax t1' t2
        indMax-monoR : ∀ {t1 t2 t2'}
          → t2 ≤ t2' → indMax t1 t2 ≤ indMax t1 t2'

        indMax-mono : ∀ {t1 t2 t1' t2'}
          → t1 ≤ t1' → t2 ≤ t2' → indMax t1 t2 ≤ indMax t1' t2'

        --Holds definitionally
        indMax-strictMono : ∀ {t1 t2 t1' t2'}
          → t1 < t1' → t2 < t2' → indMax t1 t2 < indMax t1' t2'
        indMax-strictMono lt1 lt2 = indMax-mono lt1 lt2


        indMax-assocL : ∀ t1 t2 t3
          → indMax t1 (indMax t2 t3) ≤ indMax (indMax t1 t2) t3
        indMax-assocR : ∀ t1 t2 t3
          → indMax (indMax t1 t2) t3 ≤ indMax t1 (indMax t2 t3)
        indMax-commut : ∀ t1 t2
          → indMax t1 t2 ≤ indMax t2 t1
\end{code}






\begin{code}[hide]



        indMax-≤R {t1} {t2} with indMaxView t1 t2
        ... | IndMaxZ-R = ≤-Z
        ... | IndMaxZ-L = ≤-refl _
        ... | IndMaxLim-R {f = f} _ = extLim f (λ x → indMax t1 (f x)) (λ k → indMax-≤R {t1 = t1} {f k})
        ... | IndMaxLim-L {f = f} = underLim  λ k → indMax-≤R {t1 = f k}
        ... | IndMaxLim-Suc {t1} {t2} = ≤-sucMono (indMax-≤R {t1 = t1} {t2 = t2})




        indMax-monoR' : ∀ {t1 t2 t2'} → t2 < t2' → indMax t1 t2 < indMax (↑ t1) t2'

        indMax-monoR {t1} {t2} {t2'} lt with indMaxView t1 t2 in eq1 | indMaxView t1 t2' in eq2
        ... | IndMaxZ-L  | v2  =
          lt
          ≤⨟ (≤-reflEq (cong indMax' eq2))
        ... | IndMaxZ-R  | v2  =
          indMax-≤L
          ≤⨟ ≤-reflEq (cong indMax' eq2)
        ... | IndMaxLim-L {f = f1} |  IndMaxLim-L  = extLim _ _ λ k → indMax-monoR {t1 = f1 k} lt
        indMax-monoR {t1} {(Lim _ f')} {.(Lim _ f)} (≤-cocone f k lt) | IndMaxLim-R neq  | IndMaxLim-R neq'
            = ≤-limiting (λ x → indMax t1 (f' x)) (λ y → ≤-cocone (λ x → indMax t1 (f x)) k (indMax-monoR {t1 = t1} {t2 = f' y} ((≤-cocone _ y (≤-refl _)) ≤⨟ lt)))
        indMax-monoR {t1} {.(Lim _ _)} {t2'} (≤-limiting f x₁) | IndMaxLim-R x  | v2
          = ≤-limiting (λ x₂ →
            indMax t1 (f x₂)) λ k → indMax-monoR {t1 = t1} (x₁ k)
          ≤⨟ ≤-reflEq (cong indMax' eq2)
        indMax-monoR {(↑ t1)} {.(↑ _)} {.(↑ _)} (≤-sucMono lt) | IndMaxLim-Suc  | IndMaxLim-Suc  = ≤-sucMono (indMax-monoR {t1 = t1} lt)
        indMax-monoR {(↑ t1)} {(↑ t2)} {(Lim _ f)} (≤-cocone f k lt) | IndMaxLim-Suc  | IndMaxLim-R x
            = indMax-monoR' {t1 = t1} {t2 = t2} {t2' = f k} lt
            ≤⨟ ≤-cocone (λ x₁ → indMax (↑ t1) (f x₁)) k (≤-refl _)

        indMax-monoR' {t1} {t2} {t2'}  (≤-sucMono lt) = ≤-sucMono ( (indMax-monoR {t1 = t1} lt))
        indMax-monoR' {t1} {t2} {.(Lim _ f)} (≤-cocone f k lt)
            = ≤-cocone _ k (indMax-monoR' {t1 = t1} lt)


        indMax-monoL' : ∀ {t1 t1' t2} → t1 < t1' → indMax t1 t2 < indMax t1' (↑ t2)
        indMax-monoL {t1} {t1'} {t2} lt with indMaxView t1 t2 in eq1 | indMaxView t1' t2 in eq2
        ... | IndMaxZ-L | v2 = ≤-trans (indMax-≤R {t1 = t1'}) (≤-reflEq (cong indMax' eq2))
        ... | IndMaxZ-R | v2 = ≤-trans lt (≤-trans (indMax-≤L {t1 = t1'}) (≤-reflEq (cong indMax' eq2)))
        indMax-monoL {.(Lim _ _)} {.(Lim _ f)} {t2} (≤-cocone f k lt) | IndMaxLim-L  | IndMaxLim-L
            = ≤-cocone (λ x → indMax (f x) t2) k (indMax-monoL lt)
        indMax-monoL {.(Lim _ _)} {t1'} {t2} (≤-limiting f lt) | IndMaxLim-L |  v2
            = ≤-limiting (λ x₁ → indMax (f x₁) t2) λ k → ≤-trans (indMax-monoL (lt k)) (≤-reflEq (cong indMax' eq2))
        indMax-monoL {.Z} {.Z} {.(Lim _ _)} ≤-Z | IndMaxLim-R neq  | IndMaxZ-L  = ≤-refl _
        indMax-monoL  {.(Lim _ f)} {.Z} {.(Lim _ _)} (≤-limiting f x) | IndMaxLim-R neq | IndMaxZ-L
            with () ← neq refl
        indMax-monoL {t1} {.(Lim _ _)} {.(Lim _ _)} (≤-cocone _ k lt) | IndMaxLim-R {f = f} neq | IndMaxLim-L {f = f'}
            = ≤-limiting (λ x → indMax t1 (f x)) (λ y → ≤-cocone (λ x → indMax (f' x) (Lim _ _)) k
            (≤-trans (indMax-monoL lt) (indMax-monoR {t1 = f' k} (≤-cocone f y (≤-refl _)))))
        ... | IndMaxLim-R neq | IndMaxLim-R {f = f} neq' = extLim (λ x → indMax t1 (f x)) (λ x → indMax t1' (f x)) (λ k → indMax-monoL lt)
        indMax-monoL {.(↑ _)} {.(↑ _)} {.(↑ _)} (≤-sucMono lt) | IndMaxLim-Suc  | IndMaxLim-Suc
            = ≤-sucMono (indMax-monoL lt)
        indMax-monoL {.(↑ _)} {.(Lim _ f)} {.(↑ _)} (≤-cocone f k lt) | IndMaxLim-Suc  | IndMaxLim-L
            = ≤-cocone (λ x → indMax (f x) (↑ _)) k (indMax-monoL' lt)

        indMax-monoL' {t1} {t1'} {t2} lt with indMaxView t1 t2 in eq1 | indMaxView t1' t2 in eq2
        indMax-monoL' {t1} {.(↑ _)} {t2} (≤-sucMono lt) | v1 | v2 = ≤-sucMono (≤-trans (≤-reflEq (cong indMax' (sym eq1))) (indMax-monoL lt))
        indMax-monoL' {t1} {.(Lim _ f)} {t2} (≤-cocone f k lt) | v1 | v2
            = ≤-cocone _ k (≤-trans (≤-sucMono (≤-reflEq (cong indMax' (sym eq1)))) (indMax-monoL' lt))


        indMax-mono {t1' = t1'} lt1 lt2 = ≤-trans (indMax-monoL lt1) (indMax-monoR {t1 = t1'} lt2)



        indMax-sucMono : ∀ {t1 t2 t1' t2'} → indMax t1 t2 ≤ indMax t1' t2' → indMax t1 t2 < indMax (↑ t1') (↑ t2')
        indMax-sucMono lt = ≤-sucMono lt


        indMax-Z : ∀ t → indMax t Z ≤ t
        indMax-Z Z = ≤-Z
        indMax-Z (↑ t) = ≤-refl (indMax (↑ t) Z)
        indMax-Z (Lim c f) = extLim (λ x → indMax (f x) Z) f (λ k → indMax-Z (f k))

        indMax-≤Z : ∀ t → indMax t Z ≤ t
        indMax-≤Z Z = ≤-refl _
        indMax-≤Z (↑ t) = ≤-refl _
        indMax-≤Z (Lim c f) = extLim _ _ (λ k → indMax-≤Z (f k))



        indMax-limR : ∀   {c : ℂ} (f : El  c  → Tree) t → indMax t (Lim c f) ≤ Lim c (λ k → indMax t (f k))
        indMax-limR f Z = ≤-refl _
        indMax-limR f (↑ t) = extLim _ _ λ k → ≤-refl _
        indMax-limR f (Lim c f₁) = ≤-limiting _ λ k → ≤-trans (indMax-limR f (f₁ k)) (extLim _ _ (λ k2 → indMax-monoL {t1 = f₁ k} {t1' = Lim c f₁} {t2 = f k2}  (≤-cocone _ k (≤-refl _))))


        indMax-commut t1 t2 with indMaxView t1 t2
        ... | IndMaxZ-L = indMax-≤L
        ... | IndMaxZ-R = ≤-refl _
        ... | IndMaxLim-R {f = f} x = extLim _ _ (λ k → indMax-commut t1 (f k))
        ... | IndMaxLim-Suc {t1 = t1} {t2 = t2} = ≤-sucMono (indMax-commut t1 t2)
        ... | IndMaxLim-L {c = c} {f = f} with indMaxView t2 t1
        ... | IndMaxZ-L = extLim _ _ λ k → indMax-Z (f k)
        ... | IndMaxLim-R x = extLim _ _ (λ k → indMax-commut (f k) t2)
        ... | IndMaxLim-L {c = c2} {f = f2} =
            ≤-trans (extLim _ _ λ k → indMax-limR f2 (f k))
            (≤-trans (≤-limiting _ (λ k → ≤-limiting _ λ k2 → ≤-cocone _ k2 (≤-cocone _ k (≤-refl _))))
            (≤-trans (≤-refl (Lim c2 λ k2 → Lim c λ k → indMax (f k) (f2 k2)))
            (extLim _ _ (λ k2 → ≤-limiting _ λ k1 → ≤-trans (indMax-commut (f k1) (f2 k2)) (indMax-monoR {t1 = f2 k2} {t2 = f k1} {t2' = Lim c f} (≤-cocone _ k1 (≤-refl _)))))))


        indMax-assocL t1 t2 t3 with indMaxView t2 t3 in eq23
        ... | IndMaxZ-L = indMax-monoL {t1 = t1} {t1' = indMax t1 Z} {t2 = t3} indMax-≤L
        ... | IndMaxZ-R = indMax-≤L
        ... | m with indMaxView t1 t2
        ... | IndMaxZ-L rewrite sym eq23 = ≤-refl _
        ... | IndMaxZ-R rewrite sym eq23 = ≤-refl _
        ... | IndMaxLim-R {f = f} x rewrite sym eq23 = ≤-trans (indMax-limR (λ x → indMax (f x) t3) t1) (extLim _ _ λ k → indMax-assocL t1 (f k) t3) -- f,indMax-limR f t1
        indMax-assocL .(↑ _) .(↑ _) .Z | IndMaxZ-R  | IndMaxLim-Suc = ≤-refl _
        indMax-assocL t1 t2 .(Lim _ _) | IndMaxLim-R {f = f} x   | IndMaxLim-Suc = extLim _ _ λ k → indMax-assocL t1 t2 (f k)
        indMax-assocL (↑ t1) (↑ t2) (↑ t3) | IndMaxLim-Suc  | IndMaxLim-Suc = ≤-sucMono (indMax-assocL t1 t2 t3)
        ... | IndMaxLim-L {f = f} rewrite sym eq23 = extLim _ _ λ k → indMax-assocL (f k) t2 t3



        indMax-assocR t1 t2 t3 = ≤-trans (indMax-commut (indMax t1 t2) t3) (≤-trans (indMax-monoR {t1 = t3} (indMax-commut t1 t2))
            (≤-trans (indMax-assocL t3 t2 t1) (≤-trans (indMax-commut (indMax t3 t2) t1) (indMax-monoR {t1 = t1} (indMax-commut t3 t2)))))


        indMax-swap4 : ∀ {t1 t1' t2 t2'} → indMax (indMax t1 t1') (indMax t2 t2') ≤ indMax (indMax t1 t2) (indMax t1' t2')
        indMax-swap4 {t1}{t1'}{t2 }{t2'} =
            indMax-assocL (indMax t1 t1') t2 t2'
            ≤⨟ indMax-monoL {t1 = indMax (indMax t1 t1') t2} {t2 = t2'}
            (indMax-assocR t1 t1' t2 ≤⨟ indMax-monoR {t1 = t1} (indMax-commut t1' t2) ≤⨟ indMax-assocL t1 t2 t1')
            ≤⨟ indMax-assocR (indMax t1 t2) t1' t2'

        indMax-swap6 : ∀ {t1 t2 t3 t1' t2' t3'} → indMax (indMax t1 t1') (indMax (indMax t2 t2') (indMax t3 t3')) ≤ indMax (indMax t1 (indMax t2 t3)) (indMax t1' (indMax t2' t3'))
        indMax-swap6 {t1} {t2} {t3} {t1'} {t2'} {t3'} =
            indMax-monoR {t1 = indMax t1 t1'} (indMax-swap4 {t1 = t2} {t1' = t2'} {t2 = t3} {t2' = t3'})
            ≤⨟ indMax-swap4 {t1 = t1} {t1' = t1'}

        indMax-lim2L :
            ∀
            {c1 : ℂ}
            (f1 : El  c1 → Tree)
            {c2 : ℂ}
            (f2 : El  c2 → Tree)
            → Lim  c1 (λ k1 → Lim  c2 (λ k2 → indMax (f1 k1) (f2 k2))) ≤ indMax (Lim  c1 f1) (Lim  c2 f2)
        indMax-lim2L f1 f2 = ≤-limiting  _ (λ k1 → ≤-limiting  _ λ k2 → indMax-mono (≤-cocone  f1 k1 (≤-refl _)) (≤-cocone  f2 k2 (≤-refl _)))

        indMax-lim2R :
            ∀
            {c1 : ℂ}
            (f1 : El  c1 → Tree)
            {c2 : ℂ}
            (f2 : El  c2 → Tree)
            →  indMax (Lim  c1 f1) (Lim  c2 f2)
              ≤ Lim  c1 (λ k1 → Lim  c2 (λ k2 → indMax (f1 k1) (f2 k2)))
        indMax-lim2R f1 f2 = extLim  _ _ (λ k1 → indMax-limR  _ (f1 k1))

\end{code}


\subsubsection{Limitation: Idempotence}

The problem with an inductive definition of the maximum
is that we cannot prove that it is idempotent. Since $\indMax$ is associative
and commutative, proving idempotence is equivalent to proving that it computes
a true least-upper-bound.

The difficulty lies in showing that
$\indMax\ (\Lim\ c\ f)\ (\Lim\ c\ f)\le (\Lim\ c\ f)$.
By our definition, $\indMax\ (\Lim\ c\ f)\ (\Lim\ c\ f)$
reduces to:
\begin{displaymath}
(\Lim\ c\ \lambda x \to (\Lim\ c\ (\lambda y \to \indMax\ (f\ x)\ (f\ y)))) \le \Lim\ c\ f
\end{displaymath}
We cannot use $\cocone$ to prove this, since  the left-hand side
is not necessarily equal to $f\ k$ for any $ k : \AgdaBound{El} \ c$.
So the only possibility is to use $\limiting$. Applying it twice,
along with a use of commutativity of $\indMax$, we are left with the following goal:
\begin{displaymath}
 \forall x \to \forall  y \to (\indMax\ (f\ x)\ (f\ y) \le \Lim\ c\ f)
\end{displaymath}
There is no a priori way to prove this goal without already
having a proof that $\AgdaFunction{indMax}$ is a least upper bound.
But proving that was the whole point of proving idempotence!
An inductive hypothesis would give that $\indMax\ (f\ x)\ (f\ x) \le f\ x \le Lim\ c\ f$,
but it does not apply when the arguments to $\indMax$ are not equal.
Because we are working with constructive ordinals, we have no trichotomy property~\citep{KRAUS2023113843}, and hence no guarantee
that $\indMax\ (f\ x)\ (f\ y)$ will be one of $f\ x$ and $f\ y$.

We now have two competing definitions for the maximum: the limit version,
which is not strictly monotone, and the inductive version, which is not actually
a least upper bound. In the next section, we describe a large class of trees for
which $\indMax$ is idempotent, and hence does compute a true upper bound.
We then use that in \cref{subsec:smb} to create a version of ordinals whose join
has the best properties of both $\limMax$ and $\indMax$.
