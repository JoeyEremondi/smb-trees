% !TEX root =  main.tex
\section{Brouwer Trees: An Introduction}
\begin{code}[hide]
  open import Data.Nat hiding (_≤_)
  open import Relation.Binary.PropositionalEquality
  open import Data.Product
  open import Relation.Nullary
  open import Iso
  module Tree where

\end{code}

Brouwer trees  are a simple but elegant tool for proving termination of higher-order procedures.
Traditionally, they are defined as follows:
\begin{code}
  data SmallTree : Set where
    Z' : SmallTree
    ↑' : SmallTree → SmallTree
    Lim' : (ℕ → SmallTree) → SmallTree
\end{code}
Under this definition, a Brouwer tree is either zero, the successor of another Brouwer tree, or the limit of a countable sequence of Brouwer trees. However, these are quite weak, in that they can only take the limit of countable sequences.
To represent the limits of uncountable sequences, we can paramterize our definition over some Universe \ala Tarski:

\begin{code}
  module _ {ℓ}
    (ℂ : Set ℓ)
    (El : ℂ → Set ℓ)
    (Cℕ : ℂ) (CℕIso : Iso (El Cℕ) ℕ ) where
\end{code}

We then generalize limits to any function whose domain is the interpretation of some code.
\begin{code}
    data Tree : Set ℓ where
      Z : Tree
      ↑ : Tree → Tree
      Lim : ∀  (c : ℂ ) → (f : El c → Tree) → Tree
\end{code}

\begin{code}[hiding]
\end{code}


Our module is paramterized over a universe level, a type $\bC$ of \textit{codes}, and an ``elements-of'' interpretation
function $\mathit{El}$, which computes the type represented by each code.
We require that there be a code whose interpretation is isomorphic to the natural numbers,
as this is essential to our construction in \cref{sec:TODO}.
Increasingly larger trees can be obtained by setting $\bC := \AgdaPrimitive{Set} \ \ell$ and
$\mathit{El} := \mathit{id}$ for increasing $\ell$.
However, by defining an inductive-recursive universe,
one can still capture limits over some non-countable types, since
 $\AgdaDatatype{Tree}$ is in $\AgdaPrimitive{Set}$ whenever $\bC$ is.

The small limit constructor can be recovered from the natural-number code
\begin{code}

    ℕLim : (ℕ → Tree) → Tree
    ℕLim f = Lim Cℕ  (λ cn → f (Iso.fun CℕIso cn))
\end{code}

Brouwer trees are a the quintessential example of a higher-order inductive type.%
\footnote{Not to be confused with Higher Inductive Types (HITs) from Homotopy Type Theory~\citep{hottbook}}:
Each tree is built using smaller trees or functions producing smaller trees, which is essentially
a way of storing a possibly infinite number of smaller trees.

\subsection{Ordering Trees}

Our ultimate goal is to have a well-founded ordering%
\footnote{Technically, this is a well-founded quasi-ordering because there are pairs of
  trees which are related by both $\leq$ and $\qeq$, but which are not propositionally equal.},
so we define a relation to order Brouwer trees.

\begin{code}
    data _≤_ : Tree → Tree → Set ℓ where
      ≤-Z : ∀ {o} → Z ≤ o
      ≤-sucMono : ∀ {o1 o2}
        → o1 ≤ o2
        → ↑ o1 ≤ ↑ o2
      ≤-cocone : ∀  {o } {c : ℂ} (f : El c  → Tree) (k : El c)
        → o ≤ f k
        → o ≤ Lim c f
      ≤-limiting : ∀   {o } {c : ℂ}
        → (f : El c → Tree)
        → (∀ k → f k ≤ o)
        → Lim c f ≤ o

\end{code}
The ordering is based on the one presented by \citet{KRAUS2023113843}, but we modify it
so that transitivity can be proven constructively, rather than adding it as a constructor
for the relation. This allows us to prove well-foundedness of the relation without needing
quotient types or other advanced features.

\begin{code}

    ≤-refl : ∀ o → o ≤ o
    ≤-refl Z = ≤-Z
    ≤-refl (↑ o) = ≤-sucMono (≤-refl o)
    ≤-refl (Lim c f) = ≤-limiting f (λ k → ≤-cocone f k (≤-refl (f k)))

\end{code}

\begin{code}


    ≤-reflEq : ∀ {o1 o2} → o1 ≡ o2 → o1 ≤ o2
    ≤-reflEq refl = ≤-refl _

\end{code}

\begin{code}


    ≤-trans : ∀ {o1 o2 o3} → o1 ≤ o2 → o2 ≤ o3 → o1 ≤ o3
    ≤-trans ≤-Z p23 = ≤-Z
    ≤-trans (≤-sucMono p12) (≤-sucMono p23) = ≤-sucMono (≤-trans p12 p23)
    ≤-trans p12 (≤-cocone f k p23) = ≤-cocone f k (≤-trans p12 p23)
    ≤-trans (≤-limiting f x) p23 = ≤-limiting f (λ k → ≤-trans (x k) p23)
    ≤-trans (≤-cocone f k p12) (≤-limiting .f x) = ≤-trans p12 (x k)

\end{code}

\begin{code}


    infixr 10 _≤⨟o_

\end{code}

\begin{code}


    _≤⨟o_ :  ∀ {o1 o2 o3} → o1 ≤ o2 → o2 ≤ o3 → o1 ≤ o3
    lt1 ≤⨟o lt2 = ≤-trans lt1 lt2

\end{code}

\begin{code}


    _<o_ : Tree → Tree → Set ℓ
    o1 <o o2 = ↑ o1 ≤ o2

    ≤↑o : ∀ o → o ≤ ↑ o
    ≤↑o Z = ≤-Z
    ≤↑o (↑ o) = ≤-sucMono (≤↑o o)
    ≤↑o (Lim c f) = ≤-limiting f λ k → ≤-trans (≤↑o (f k)) (≤-sucMono (≤-cocone f k (≤-refl (f k))))


    <-in-≤ : ∀ {x y} → x <o y → x ≤ y
    <-in-≤ pf = ≤-trans (≤↑o _) pf


    -- https://cj-xu.github.io/agda/constructive-ordinals-in-hott/BrouwerTree.Code.Results.html#3168
    -- TODO: proper credit
    <∘≤-in-< : ∀ {x y z} → x <o y → y ≤ z → x <o z
    <∘≤-in-< x<y y≤z = ≤-trans x<y y≤z

    -- https://cj-xu.github.io/agda/constructive-ordinals-in-hott/BrouwerTree.Code.Results.html#3168
    -- TODO: proper credit
    ≤∘<-in-< : ∀ {x y z} → x ≤ y → y <o z → x <o z
    ≤∘<-in-< {x} {y} {z} x≤y y<z = ≤-trans (≤-sucMono x≤y) y<z

    underLim : ∀   {c : ℂ} (k : ℂ) o →  (f : El c → Tree) → (∀ k → o ≤ f k) → o ≤ Lim c f
    underLim {c = c} k o f all = ≤-trans (≤-cocone (λ _ → o) {!!} (≤-refl o)) (≤-limiting (λ _ → o) (λ k → ≤-cocone f k (all k)))

    extLim : ∀   {c : ℂ} →  (f1 f2 : El c → Tree) → (∀ k → f1 k ≤ f2 k) → Lim c f1 ≤ Lim c f2
    extLim {c = c} f1 f2 all = ≤-limiting f1 (λ k → ≤-cocone f2 k (all k))


    existsLim : ∀  {c1 : ℂ} {c2 : ℂ} →  (f1 : El c1  → Tree) (f2 : El  c2  → Tree) → (∀ k1 → Σ[ k2 ∈ El  c2 ] f1 k1 ≤ f2 k2) → Lim  c1 f1 ≤ Lim  c2 f2
    existsLim {æ1} {æ2} f1 f2 allex = ≤-limiting  f1 (λ k → ≤-cocone f2 (proj₁ (allex k)) (proj₂ (allex k)))


    ¬Z<↑o : ∀  o → ¬ ((↑ o) ≤ Z)
    ¬Z<↑o o ()


    open import Induction.WellFounded
    access : ∀ {x} → Acc _<o_ x → WfRec _<o_ (Acc _<o_) x
    access (acc r) = r

    -- https://cj-xu.github.io/agda/constructive-ordinals-in-hott/BrouwerTree.Code.Results.html#3168
    -- TODO: proper credit
    smaller-accessible : (x : Tree) → Acc _<o_ x → ∀ y → y ≤ x → Acc _<o_ y
    smaller-accessible x isAcc y x<y = acc (λ y' y'<y → access isAcc y' (<∘≤-in-< y'<y x<y))

    -- https://cj-xu.github.io/agda/constructive-ordinals-in-hott/BrouwerTree.Code.Results.html#3168
    -- TODO: proper credit
    ordWF : WellFounded _<o_
    ordWF Z = acc λ _ ()
    ordWF (↑ x) = acc (λ { y (≤-sucMono y≤x) → smaller-accessible x (ordWF x) y y≤x})
    ordWF (Lim c f) = acc helper
      where
        helper : (y : Tree) → (y <o Lim c f) → Acc _<o_ y
        helper y (≤-cocone .f k y<fk) = smaller-accessible (f k) (ordWF (f k)) y (<-in-≤ y<fk)



\end{code}

% \begin{code}


%     private
%       data MaxView : Tree → Tree → Set ℓ where
%         MaxZ-L : ∀ {o} → MaxView Z o
%         MaxZ-R : ∀ {o} → MaxView o Z
%         MaxLim-L : ∀ {o } {c : ℂ} {f : El c → Tree} → MaxView (Lim c f) o
%         MaxLim-R : ∀ {o } {c : ℂ} {f : El c → Tree}
%           → (∀   {c' : ℂ} {f' : El c' → Tree} → ¬ (o ≡ Lim  c' f'))
%           → MaxView o (Lim c f)
%         MaxLim-Suc : ∀  {o1 o2 } → MaxView (↑ o1) (↑ o2)

%       maxView : ∀ o1 o2 → MaxView o1 o2
%       maxView Z o2 = MaxZ-L
%       maxView (Lim c f) o2 = MaxLim-L
%       maxView (↑ o1) Z = MaxZ-R
%       maxView (↑ o1) (Lim c f) = MaxLim-R λ ()
%       maxView (↑ o1) (↑ o2) = MaxLim-Suc

%     abstract
%       max : Tree → Tree → Tree
%       max' : ∀ {o1 o2} → MaxView o1 o2 → Tree

%       max o1 o2 = max' (maxView o1 o2)

%       max' {.Z} {o2} MaxZ-L = o2
%       max' {o1} {.Z} MaxZ-R = o1
%       max' {(Lim c f)} {o2} MaxLim-L = Lim c λ x → max (f x) o2
%       max' {o1} {(Lim c f)} (MaxLim-R _) = Lim c (λ x → max o1 (f x))
%       max' {(↑ o1)} {(↑ o2)} MaxLim-Suc = ↑ (max o1 o2)

%       max-≤L : ∀ {o1 o2} → o1 ≤ max o1 o2
%       max-≤L {o1} {o2} with maxView o1 o2
%       ... | MaxZ-L = ≤-Z
%       ... | MaxZ-R = ≤-refl _
%       ... | MaxLim-L {f = f} = extLim f (λ x → max (f x) o2) (λ k → max-≤L)
%       ... | MaxLim-R {f = f} _ = underLim {!!} o1 (λ x → max o1 (f x)) (λ k → max-≤L)
%       ... | MaxLim-Suc = ≤-sucMono max-≤L


%       max-≤R : ∀ {o1 o2} → o2 ≤ max o1 o2
%       max-≤R {o1} {o2} with maxView o1 o2
%       ... | MaxZ-R = ≤-Z
%       ... | MaxZ-L = ≤-refl _
%       ... | MaxLim-R {f = f} _ = extLim f (λ x → max o1 (f x)) (λ k → max-≤R {o1 = o1} {f k})
%       ... | MaxLim-L {f = f} = underLim {!!} o2 (λ x → max (f x) o2) (λ k → max-≤R {o1 = f k} {o2 = o2})
%       ... | MaxLim-Suc {o1} {o2} = ≤-sucMono (max-≤R {o1 = o1} {o2 = o2})




%       max-monoR : ∀ {o1 o2 o2'} → o2 ≤ o2' → max o1 o2 ≤ max o1 o2'
%       max-monoR' : ∀ {o1 o2 o2'} → o2 <o o2' → max o1 o2 <o max (↑ o1) o2'

%       max-monoR {o1} {o2} {o2'} lt with maxView o1 o2 in eq1 | maxView o1 o2' in eq2
%       ... | MaxZ-L  | v2  = ≤-trans lt (≤-reflEq (cong max' eq2))
%       ... | MaxZ-R  | v2  = ≤-trans max-≤L (≤-reflEq (cong max' eq2))
%       ... | MaxLim-L {f = f1} |  MaxLim-L  = extLim _ _ λ k → max-monoR {o1 = f1 k} lt
%       max-monoR {o1} {(Lim _ f')} {.(Lim _ f)} (≤-cocone f k lt) | MaxLim-R neq  | MaxLim-R neq'
%         = ≤-limiting (λ x → max o1 (f' x)) (λ y → ≤-cocone (λ x → max o1 (f x)) k (max-monoR {o1 = o1} {o2 = f' y} (≤-trans (≤-cocone _ y (≤-refl _)) lt)))
%       max-monoR {o1} {.(Lim _ _)} {o2'} (≤-limiting f x₁) | MaxLim-R x  | v2  =
%         ≤-trans (≤-limiting (λ x₂ → max o1 (f x₂)) λ k → max-monoR {o1 = o1} (x₁ k)) (≤-reflEq (cong max' eq2))
%       max-monoR {(↑ o1)} {.(↑ _)} {.(↑ _)} (≤-sucMono lt) | MaxLim-Suc  | MaxLim-Suc  = ≤-sucMono (max-monoR {o1 = o1} lt)
%       max-monoR {(↑ o1)} {(↑ o2)} {(Lim _ f)} (≤-cocone f k lt) | MaxLim-Suc  | MaxLim-R x
%         = ≤-trans (max-monoR' {o1 = o1} {o2 = o2} {o2' = f k} lt) (≤-cocone (λ x₁ → max (↑ o1) (f x₁)) k (≤-refl _)) --max-monoR' {!lt!}

%       max-monoR' {o1} {o2} {o2'}  (≤-sucMono lt) = ≤-sucMono ( (max-monoR {o1 = o1} lt))
%       max-monoR' {o1} {o2} {.(Lim _ f)} (≤-cocone f k lt)
%         = ≤-cocone _ k (max-monoR' {o1 = o1} lt)


%       max-monoL : ∀ {o1 o1' o2} → o1 ≤ o1' → max o1 o2 ≤ max o1' o2
%       max-monoL' : ∀ {o1 o1' o2} → o1 <o o1' → max o1 o2 <o max o1' (↑ o2)
%       max-monoL {o1} {o1'} {o2} lt with maxView o1 o2 in eq1 | maxView o1' o2 in eq2
%       ... | MaxZ-L | v2 = ≤-trans (max-≤R {o1 = o1'}) (≤-reflEq (cong max' eq2))
%       ... | MaxZ-R | v2 = ≤-trans lt (≤-trans (max-≤L {o1 = o1'}) (≤-reflEq (cong max' eq2)))
%       max-monoL {.(Lim _ _)} {.(Lim _ f)} {o2} (≤-cocone f k lt) | MaxLim-L  | MaxLim-L
%         = ≤-cocone (λ x → max (f x) o2) k (max-monoL lt)
%       max-monoL {.(Lim _ _)} {o1'} {o2} (≤-limiting f lt) | MaxLim-L |  v2
%         = ≤-limiting (λ x₁ → max (f x₁) o2) λ k → ≤-trans (max-monoL (lt k)) (≤-reflEq (cong max' eq2))
%       max-monoL {.Z} {.Z} {.(Lim _ _)} ≤-Z | MaxLim-R neq  | MaxZ-L  = ≤-refl _
%       max-monoL  {.(Lim _ f)} {.Z} {.(Lim _ _)} (≤-limiting f x) | MaxLim-R neq | MaxZ-L
%         with () ← neq refl
%       max-monoL {o1} {.(Lim _ _)} {.(Lim _ _)} (≤-cocone _ k lt) | MaxLim-R {f = f} neq | MaxLim-L {f = f'}
%         = ≤-limiting (λ x → max o1 (f x)) (λ y → ≤-cocone (λ x → max (f' x) (Lim _ _)) k
%           (≤-trans (max-monoL lt) (max-monoR {o1 = f' k} (≤-cocone f y (≤-refl _)))))
%       ... | MaxLim-R neq | MaxLim-R {f = f} neq' = extLim (λ x → max o1 (f x)) (λ x → max o1' (f x)) (λ k → max-monoL lt)
%       max-monoL {.(↑ _)} {.(↑ _)} {.(↑ _)} (≤-sucMono lt) | MaxLim-Suc  | MaxLim-Suc
%         = ≤-sucMono (max-monoL lt)
%       max-monoL {.(↑ _)} {.(Lim _ f)} {.(↑ _)} (≤-cocone f k lt) | MaxLim-Suc  | MaxLim-L
%         = ≤-cocone (λ x → max (f x) (↑ _)) k (max-monoL' lt)

%       max-monoL' {o1} {o1'} {o2} lt with maxView o1 o2 in eq1 | maxView o1' o2 in eq2
%       max-monoL' {o1} {.(↑ _)} {o2} (≤-sucMono lt) | v1 | v2 = ≤-sucMono (≤-trans (≤-reflEq (cong max' (sym eq1))) (max-monoL lt))
%       max-monoL' {o1} {.(Lim _ f)} {o2} (≤-cocone f k lt) | v1 | v2
%         = ≤-cocone _ k (≤-trans (≤-sucMono (≤-reflEq (cong max' (sym eq1)))) (max-monoL' lt))


%       max-mono : ∀ {o1 o2 o1' o2'} → o1 ≤ o1' → o2 ≤ o2' → max o1 o2 ≤ max o1' o2'
%       max-mono {o1' = o1'} lt1 lt2 = ≤-trans (max-monoL lt1) (max-monoR {o1 = o1'} lt2)

%       max-strictMono : ∀ {o1 o2 o1' o2'} → o1 <o o1' → o2 <o o2' → max o1 o2 <o max o1' o2'
%       max-strictMono lt1 lt2 = max-mono lt1 lt2


%       max-sucMono : ∀ {o1 o2 o1' o2'} → max o1 o2 ≤ max o1' o2' → max o1 o2 <o max (↑ o1') (↑ o2')
%       max-sucMono lt = ≤-sucMono lt


%       -- max-Z : ∀ o → max o Z ≡ o
%       -- max-Z Z = refl
%       -- max-Z (↑ o) = refl
%       -- max-Z (Lim c f) = cong (Lim c) {!!} -- cong (Lim c) (funExt (λ x → max-Z (f x)))

%       max-Z : ∀ o → max o Z ≤ o
%       max-Z Z = ≤-Z
%       max-Z (↑ o) = ≤-refl (max (↑ o) Z)
%       max-Z (Lim c f) = extLim (λ x → max (f x) Z) f (λ k → max-Z (f k))

%       max-↑ : ∀ {o1 o2} → max (↑ o1) (↑ o2) ≡ ↑ (max o1 o2)
%       max-↑ = refl

%       max-≤Z : ∀ o → max o Z ≤ o
%       max-≤Z Z = ≤-refl _
%       max-≤Z (↑ o) = ≤-refl _
%       max-≤Z (Lim c f) = extLim _ _ (λ k → max-≤Z (f k))

%       -- max-oneL : ∀ {o} → max O1 (↑ o) ≤ ↑ o
%       -- max-oneL  = ≤-refl _

%       -- max-oneR : ∀ {o} → max (↑ o) O1 ≤ ↑ o
%       -- max-oneR {Z} = ≤-sucMono (≤-refl _)
%       -- max-oneR {↑ o} = ≤-sucMono (≤-refl _)
%       -- max-oneR {Lim c f} = ≤-sucMono (substPath (λ x → x ≤ Lim c f) (sym (max-Z (Lim c f))) (≤-refl (Lim c f))) -- rewrite ctop (max-Z (Lim c f))= ≤-refl _


%       max-limR : ∀   {c : ℂ} (f : El  c  → Tree) o → max o (Lim c f) ≤ Lim c (λ k → max o (f k))
%       max-limR f Z = ≤-refl _
%       max-limR f (↑ o) = extLim _ _ λ k → ≤-refl _
%       max-limR f (Lim c f₁) = ≤-limiting _ λ k → ≤-trans (max-limR f (f₁ k)) (extLim _ _ (λ k2 → max-monoL {o1 = f₁ k} {o1' = Lim c f₁} {o2 = f k2}  (≤-cocone _ k (≤-refl _))))


%       max-commut : ∀ o1 o2 → max o1 o2 ≤ max o2 o1
%       max-commut o1 o2 with maxView o1 o2
%       ... | MaxZ-L = max-≤L
%       ... | MaxZ-R = ≤-refl _
%       ... | MaxLim-R {f = f} x = extLim _ _ (λ k → max-commut o1 (f k))
%       ... | MaxLim-Suc {o1 = o1} {o2 = o2} = ≤-sucMono (max-commut o1 o2)
%       ... | MaxLim-L {c = c} {f = f} with maxView o2 o1
%       ... | MaxZ-L = extLim _ _ λ k → max-Z (f k)
%       ... | MaxLim-R x = extLim _ _ (λ k → max-commut (f k) o2)
%       ... | MaxLim-L {c = c2} {f = f2} =
%         ≤-trans (extLim _ _ λ k → max-limR f2 (f k))
%         (≤-trans (≤-limiting _ (λ k → ≤-limiting _ λ k2 → ≤-cocone _ k2 (≤-cocone _ k (≤-refl _))))
%         (≤-trans (≤-refl (Lim c2 λ k2 → Lim c λ k → max (f k) (f2 k2)))
%         (extLim _ _ (λ k2 → ≤-limiting _ λ k1 → ≤-trans (max-commut (f k1) (f2 k2)) (max-monoR {o1 = f2 k2} {o2 = f k1} {o2' = Lim c f} (≤-cocone _ k1 (≤-refl _)))))))


%       max-assocL : ∀ o1 o2 o3 → max o1 (max o2 o3) ≤ max (max o1 o2) o3
%       max-assocL o1 o2 o3 with maxView o2 o3 in eq23
%       ... | MaxZ-L = max-monoL {o1 = o1} {o1' = max o1 Z} {o2 = o3} max-≤L
%       ... | MaxZ-R = max-≤L
%       ... | m with maxView o1 o2
%       ... | MaxZ-L rewrite sym eq23 = ≤-refl _
%       ... | MaxZ-R rewrite sym eq23 = ≤-refl _
%       ... | MaxLim-R {f = f} x rewrite sym eq23 = ≤-trans (max-limR (λ x → max (f x) o3) o1) (extLim _ _ λ k → max-assocL o1 (f k) o3) -- f,max-limR f o1
%       max-assocL .(↑ _) .(↑ _) .Z | MaxZ-R  | MaxLim-Suc = ≤-refl _
%       max-assocL o1 o2 .(Lim _ _) | MaxLim-R {f = f} x   | MaxLim-Suc = extLim _ _ λ k → max-assocL o1 o2 (f k)
%       max-assocL (↑ o1) (↑ o2) (↑ o3) | MaxLim-Suc  | MaxLim-Suc = ≤-sucMono (max-assocL o1 o2 o3)
%       ... | MaxLim-L {f = f} rewrite sym eq23 = extLim _ _ λ k → max-assocL (f k) o2 o3



%       max-assocR : ∀ o1 o2 o3 →  max (max o1 o2) o3 ≤ max o1 (max o2 o3)
%       max-assocR o1 o2 o3 = ≤-trans (max-commut (max o1 o2) o3) (≤-trans (max-monoR {o1 = o3} (max-commut o1 o2))
%         (≤-trans (max-assocL o3 o2 o1) (≤-trans (max-commut (max o3 o2) o1) (max-monoR {o1 = o1} (max-commut o3 o2)))))


%       max-swap4 : ∀ {o1 o1' o2 o2'} → max (max o1 o1') (max o2 o2') ≤ max (max o1 o2) (max o1' o2')
%       max-swap4 {o1}{o1'}{o2 }{o2'} =
%         max-assocL (max o1 o1') o2 o2'
%         ≤⨟o max-monoL {o1 = max (max o1 o1') o2} {o2 = o2'}
%           (max-assocR o1 o1' o2 ≤⨟o max-monoR {o1 = o1} (max-commut o1' o2) ≤⨟o max-assocL o1 o2 o1')
%         ≤⨟o max-assocR (max o1 o2) o1' o2'

%       max-swap6 : ∀ {o1 o2 o3 o1' o2' o3'} → max (max o1 o1') (max (max o2 o2') (max o3 o3')) ≤ max (max o1 (max o2 o3)) (max o1' (max o2' o3'))
%       max-swap6 {o1} {o2} {o3} {o1'} {o2'} {o3'} =
%         max-monoR {o1 = max o1 o1'} (max-swap4 {o1 = o2} {o1' = o2'} {o2 = o3} {o2' = o3'})
%         ≤⨟o max-swap4 {o1 = o1} {o1' = o1'}

%       max-lim2L :
%         ∀
%         {c1 : ℂ}
%         (f1 : El  c1 → Tree)
%         {c2 : ℂ}
%         (f2 : El  c2 → Tree)
%         → Lim  c1 (λ k1 → Lim  c2 (λ k2 → max (f1 k1) (f2 k2))) ≤ max (Lim  c1 f1) (Lim  c2 f2)
%       max-lim2L f1 f2 = ≤-limiting  _ (λ k1 → ≤-limiting  _ λ k2 → max-mono (≤-cocone  f1 k1 (≤-refl _)) (≤-cocone  f2 k2 (≤-refl _)))

%       max-lim2R :
%         ∀
%         {c1 : ℂ}
%         (f1 : El  c1 → Tree)
%         {c2 : ℂ}
%         (f2 : El  c2 → Tree)
%         →  max (Lim  c1 f1) (Lim  c2 f2) ≤ Lim  c1 (λ k1 → Lim  c2 (λ k2 → max (f1 k1) (f2 k2)))
%       max-lim2R f1 f2 = extLim  _ _ (λ k1 → max-limR  _ (f1 k1))

%     --Attempt to have an idempotent version of max

%       nmax : Tree → ℕ → Tree
%       nmax o ℕ.zero = Z
%       nmax o (ℕ.suc n) = max (nmax o n) o

%       nmax-mono : ∀ {o1 o2 } n → o1 ≤ o2 → nmax o1 n ≤ nmax o2 n
%       nmax-mono ℕ.zero lt = ≤-Z
%       nmax-mono {o1 = o1} {o2} (ℕ.suc n) lt = max-mono {o1 = nmax o1 n} {o2 = o1} {o1' = nmax o2 n} {o2' = o2} (nmax-mono n lt) lt

%     --
%       max∞ : Tree → Tree
%       max∞ o = OℕLim (λ n → nmax o n)


%       max-∞lt1 : ∀ o → max (max∞ o) o ≤ max∞ o
%       max-∞lt1 o = ≤-limiting  _ λ k → helper (Iso.fun CℕIso k)
%         where
%           helper : ∀ n → max (nmax o n) o ≤ max∞ o
%           helper n = ≤-cocone  _ (Iso.inv CℕIso (ℕ.suc n)) (subst (λ sn → nmax o (ℕ.suc n) ≤ nmax o sn) (sym (Iso.rightInv CℕIso (suc n))) (≤-refl _))
%         -- helper (ℕ.suc n) = ≤-cocone  _ (CℕfromNat (ℕ.suc (ℕ.suc n))) (subst (λ sn → max (max (nmax o n) o) o ≤ nmax o sn) (sym (Cℕembed (ℕ.suc n)))
%         --   {!!})
%         --

%       -- nmax-idem-absorb : ∀ o n → max o o ≤ o → nmax o n ≤ o
%       -- nmax-idem-absorb o ℕ.zero lt = ≤-Z
%       -- nmax-idem-absorb o (ℕ.suc n) lt = max-monoL (nmax-idem-absorb o n lt) ≤⨟o lt
%       -- max∞-idem-absorb : ∀ {o} → max o o ≤ o → max∞ o ≤ o
%       -- max∞-idem-absorb lt = ≤-limiting  (λ x → nmax _ (CℕtoNat x)) (λ k → nmax-idem-absorb _ (CℕtoNat k) lt)

%       max-∞ltn : ∀ n o → max (max∞ o) (nmax o n) ≤ max∞ o
%       max-∞ltn ℕ.zero o = max-≤Z (max∞ o)
%       max-∞ltn (ℕ.suc n) o =
%         ≤-trans (max-monoR {o1 = max∞ o} (max-commut (nmax o n) o))
%         (≤-trans (max-assocL (max∞ o) o (nmax o n))
%         (≤-trans (max-monoL {o1 = max (max∞ o) o} {o2 = nmax o n} (max-∞lt1 o)) (max-∞ltn n o)))

%       max∞-idem : ∀ o → max (max∞ o) (max∞ o) ≤ max∞ o
%       max∞-idem o = ≤-limiting  _ λ k → ≤-trans (max-commut (nmax o (Iso.fun CℕIso k)) (max∞ o)) (max-∞ltn (Iso.fun CℕIso k) o)


%       max∞-self : ∀ o → o ≤ max∞ o
%       max∞-self o = ≤-cocone  _ (Iso.inv CℕIso 1) (subst (λ x → o ≤ nmax o x) (sym (Iso.rightInv CℕIso 1)) (≤-refl _))

%       max∞-idem∞ : ∀ o → max o o ≤ max∞ o
%       max∞-idem∞ o = ≤-trans (max-mono (max∞-self o) (max∞-self o)) (max∞-idem o)

%       max∞-mono : ∀ {o1 o2} → o1 ≤ o2 → (max∞ o1) ≤ (max∞ o2)
%       max∞-mono lt = extLim  _ _ λ k → nmax-mono (Iso.fun CℕIso k) lt



%       nmax-≤ : ∀ {o} n → max o o ≤ o → nmax o n ≤ o
%       nmax-≤ ℕ.zero lt = ≤-Z
%       nmax-≤ {o = o} (ℕ.suc n) lt = ≤-trans (max-monoL {o1 = nmax o n} {o2 = o} (nmax-≤ n lt)) lt

%       max∞-≤ : ∀ {o} → max o o ≤ o → max∞ o ≤ o
%       max∞-≤ lt = ≤-limiting  _ λ k → nmax-≤ (Iso.fun CℕIso k) lt

%       -- Convenient helper for turing < with max∞ into < without
%       max<-∞ : ∀ {o1 o2 o} → max (max∞ (o1)) (max∞ o2) <o o → max o1 o2 <o o
%       max<-∞ lt = ≤∘<-in-< (max-mono (max∞-self _) (max∞-self _)) lt

%       max-<Ls : ∀ {o1 o2 o1' o2'} → max o1 o2 <o max (↑ (max o1 o1')) (↑ (max o2 o2'))
%       max-<Ls {o1} {o2} {o1'} {o2'} = max-sucMono {o1 = o1} {o2 = o2} {o1' = max o1 o1'} {o2' = max o2 o2'}
%         (max-mono {o1 = o1} {o2 = o2} (max-≤L) (max-≤L))

%       max∞-<Ls : ∀ {o1 o2 o1' o2'} → max o1 o2 <o max (↑ (max (max∞ o1) o1')) (↑ (max (max∞ o2) o2'))
%       max∞-<Ls {o1} {o2} {o1'} {o2'} =  <∘≤-in-< (max-<Ls {o1} {o2} {o1'} {o2'})
%         (max-mono {o1 = ↑ (max o1 o1')} {o2 = ↑ (max o2 o2')}
%           (≤-sucMono (max-monoL (max∞-self o1)))
%           (≤-sucMono (max-monoL (max∞-self o2))))


%       max∞-lub : ∀ {o1 o2 o} → o1 ≤ max∞ o → o2 ≤ max∞  o → max o1 o2 ≤ (max∞ o)
%       max∞-lub {o1 = o1} {o2 = o2} lt1 lt2 = max-mono {o1 = o1} {o2 = o2} lt1 lt2 ≤⨟o max∞-idem _

%       max∞-absorbL : ∀ {o1 o2 o} → o2 ≤ o1 → o1 ≤ max∞ o → max o1 o2 ≤ max∞ o
%       max∞-absorbL lt12 lt1 = max∞-lub lt1 (lt12 ≤⨟o lt1)

%       max∞-distL : ∀ {o1 o2} → max (max∞ o1) (max∞ o2) ≤ max∞ (max o1 o2)
%       max∞-distL {o1} {o2} =
%         max∞-lub {o1 = max∞ o1} {o2 = max∞ o2} (max∞-mono max-≤L) (max∞-mono (max-≤R {o1 = o1}))


%       max∞-distR : ∀ {o1 o2} → max∞ (max o1 o2) ≤ max (max∞ o1) (max∞ o2)
%       max∞-distR {o1} {o2} = ≤-limiting  _ λ k → helper {n = Iso.fun CℕIso k}
%         where
%         helper : ∀ {o1 o2 n} → nmax (max o1 o2) n ≤ max (max∞ o1) (max∞ o2)
%         helper {o1} {o2} {ℕ.zero} = ≤-Z
%         helper {o1} {o2} {ℕ.suc n} =
%           max-monoL {o1 = nmax (max o1 o2) n} (helper {o1 = o1} {o2} {n})
%           ≤⨟o max-swap4 {max∞ o1} {max∞ o2} {o1} {o2}
%           ≤⨟o max-mono {o1 = max (max∞ o1) o1} {o2 = max (max∞ o2) o2} {o1' = max∞ o1} {o2' = max∞ o2}
%             (max∞-lub {o1 = max∞ o1} (≤-refl _) (max∞-self _))
%             (max∞-lub {o1 = max∞ o2} (≤-refl _) (max∞-self _))


%       max∞-cocone : ∀  {c : ℂ} (f : El c → Tree) k →
%         f k ≤ max∞ (Lim  c f)
%       max∞-cocone f k =  max∞-self _ ≤⨟o max∞-mono (≤-cocone  _ k (≤-refl _))

%       -- max* : ∀ {n} → Vec Tree n → Tree
%       -- max* [] = Z
%       -- max* (x ∷ os) = max x (max* os)

%       -- max*-≤L : ∀ {n o} {os : Vec Tree n} → o ≤ max* (o ∷ os)
%       -- max*-≤L = max-≤L

%       -- max*-≤R : ∀ {n o} {os : Vec Tree n} → max* os ≤ max* (o ∷ os)
%       -- max*-≤R {o = o} = max-≤R {o1 = o}

%       -- max*-≤-n : ∀ {n} {os : Vec Tree n} (f : Fin n) → lookup f os ≤ max* os
%       -- max*-≤-n {os = o ∷ os} Fin.zero = max*-≤L {o = o} {os = os}
%       -- max*-≤-n {os = o ∷ os} (Fin.suc f) = max*-≤-n f ≤⨟o (max*-≤R {o = o} {os = os})

%       -- max*-swap : ∀ {n} {os1 os2 : Vec Tree n} → max* (zipWith max os1 os2) ≤ max (max* os1) (max* os2)
%       -- max*-swap {n = ℕ.zero} {[]} {[]} = ≤-Z
%       -- max*-swap {n = ℕ.suc n} {o1 ∷ os1} {o2 ∷ os2} = max-monoR {o1 = max o1 o2} (max*-swap {n = n}) ≤⨟o max-swap4 {o1 = o1} {o1' = o2} {o2 = max* os1} {o2' = max* os2}

%       -- max*-mono : ∀ {n} {os1 os2 : Vec Tree n} → foldr (λ (o1 , o2) rest → (o1 ≤ o2) × rest) Unit (zipWith _,_ os1 os2) → max* os1 ≤ max* os2
%       -- max*-mono {ℕ.zero} {[]} {[]} lt = ≤-Z
%       -- max*-mono {ℕ.suc n} {o1 ∷ os1} {o2 ∷ os2} (lt , rest) = max-mono {o1 = o1} {o1' = o2} lt (max*-mono {os1 = os1} {os2 = os2} rest)

%     -- orec : ∀  (P : Tree → Set ℓ)
%     --   → ((x : Tree) → (rec : (y : Tree) → (_ : ∥ y <o x ∥₁) → P y ) → P x)
%     --   → ∀ {o} → P o
%     -- orec P f = induction (λ x rec → f x rec) _
%     --   where open WFI (ordWFProp)


%     -- oPairRec : ∀  (P : Tree → Tree → Set ℓ)
%     --   → ((x1 x2 : Tree) → (rec : (y1 y2 : Tree) → (_ : (y1 , y2) <oPair (x1 , x2)) → P y1 y2 ) → P x1 x2)
%     --   → ∀ {o1 o2} → P o1 o2
%     -- oPairRec P f = induction (λ (x1 , x2) rec → f x1 x2 λ y1 y2 → rec (y1 , y2)) _
%     --   where open WFI (oPairWF)

% \end{code}
