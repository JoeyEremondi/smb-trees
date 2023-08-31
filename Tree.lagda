% !TEX root =  main.tex
\section{Brouwer Trees: An Introduction}
\begin{code}[hide]
  open import Data.Nat
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
  module _ {ℓ} (ℂ : Set ℓ) (El : ℂ → Set ℓ) (Cℕ : ℂ) (CℕIso : Iso (El Cℕ) ℕ ) where
\end{code}

We then generalize limits to any function whose domain is the interpretation of some code.
\begin{code}
    data Tree : Set ℓ where
      OZ : Tree
      O↑ : Tree -> Tree
      OLim : ∀  (c : ℂ ) → (f : El c → Tree) → Tree
\end{code}

\begin{code}[hiding]
\end{code}


Our module is paramterized over a universe level, a type $\bC$ of \textit{codes}, and an ``elements-of'' interpretation
function $\mathit{El}$, which computes the type represented by each code.
Increasingly larger trees can be obtained by setting $\bC := \AgdaPrimitive{Set} \ \ell$ and
$\mathit{El} := \mathit{id}$ for increasing $\ell$.
However, by defining an inductive-recursive universe,
one can still capture limits over some non-countable types, since
 $\AgdaDatatype{Tree}$ is in $\AgdaPrimitive{Set}$ whenever $\bC$ is.


Brouwer trees are a the quintessential example of a higher-order inductive type.%
\footnote{Not to be confused with Higher Inductive Types (HITs) from Homotopy Type Theory~\citep{hottbook}}:
Each tree is built using smaller trees or functions producing smaller trees, which is essentially
a way of storing a possibly infinite number of smaller trees.

\subsection{Ordering Trees}

\subsection{A Join Operation}

\begin{code}

    OℕLim : (ℕ → Tree) → Tree
    OℕLim f = OLim Cℕ  (λ cn → f (Iso.fun CℕIso cn))

    -- from Kraus et al https://arxiv.org/pdf/2104.02549.pdf
    data _≤o_ : Tree → Tree → Set ℓ where
      ≤o-Z : ∀ {o} → OZ ≤o o
      ≤o-sucMono : ∀ {o1 o2} → o1 ≤o o2 → O↑ o1 ≤o O↑ o2
      ≤o-cocone : ∀  {o } {c : ℂ} (f : El c  → Tree) (k : El c) → o ≤o f k → o ≤o OLim c f
      ≤o-limiting : ∀   {o } {c : ℂ} → (f : El c → Tree) → (∀ k → f k ≤o o) → OLim c f ≤o o

    ≤o-refl : ∀ o → o ≤o o
    ≤o-refl OZ = ≤o-Z
    ≤o-refl (O↑ o) = ≤o-sucMono (≤o-refl o)
    ≤o-refl (OLim c f) = ≤o-limiting f (λ k → ≤o-cocone f k (≤o-refl (f k)))

    ≤o-reflEq : ∀ {o1 o2} → o1 ≡ o2 → o1 ≤o o2
    ≤o-reflEq refl = ≤o-refl _

    ≤o-trans : ∀ {o1 o2 o3} → o1 ≤o o2 → o2 ≤o o3 → o1 ≤o o3
    ≤o-trans ≤o-Z p23 = ≤o-Z
    ≤o-trans (≤o-sucMono p12) (≤o-sucMono p23) = ≤o-sucMono (≤o-trans p12 p23)
    ≤o-trans p12 (≤o-cocone f k p23) = ≤o-cocone f k (≤o-trans p12 p23)
    ≤o-trans (≤o-limiting f x) p23 = ≤o-limiting f (λ k → ≤o-trans (x k) p23)
    ≤o-trans (≤o-cocone f k p12) (≤o-limiting .f x) = ≤o-trans p12 (x k)

    infixr 10 _≤⨟o_

    _≤⨟o_ :  ∀ {o1 o2 o3} → o1 ≤o o2 → o2 ≤o o3 → o1 ≤o o3
    lt1 ≤⨟o lt2 = ≤o-trans lt1 lt2

    -- ≤o-℧ :  ∀  {o ℓ} {c : ℂ} {f : El c → Tree} → o ≤o f (℧Approx c) → o ≤o OLim c f
    -- ≤o-℧ {c = c} lt = ≤o-cocone _ (℧Approx c) lt

    _<o_ : Tree → Tree → Set ℓ
    o1 <o o2 = O↑ o1 ≤o o2

    ≤↑o : ∀ o → o ≤o O↑ o
    ≤↑o OZ = ≤o-Z
    ≤↑o (O↑ o) = ≤o-sucMono (≤↑o o)
    ≤↑o (OLim c f) = ≤o-limiting f λ k → ≤o-trans (≤↑o (f k)) (≤o-sucMono (≤o-cocone f k (≤o-refl (f k))))


    <-in-≤o : ∀ {x y} → x <o y → x ≤o y
    <-in-≤o pf = ≤o-trans (≤↑o _) pf


    -- https://cj-xu.github.io/agda/constructive-ordinals-in-hott/BrouwerTree.Code.Results.html#3168
    -- TODO: proper credit
    <∘≤-in-< : ∀ {x y z} → x <o y → y ≤o z → x <o z
    <∘≤-in-< x<y y≤z = ≤o-trans x<y y≤z

    -- https://cj-xu.github.io/agda/constructive-ordinals-in-hott/BrouwerTree.Code.Results.html#3168
    -- TODO: proper credit
    ≤∘<-in-< : ∀ {x y z} → x ≤o y → y <o z → x <o z
    ≤∘<-in-< {x} {y} {z} x≤y y<z = ≤o-trans (≤o-sucMono x≤y) y<z

    underLim : ∀   {c : ℂ} o →  (f : El c → Tree) → (∀ k → o ≤o f k) → o ≤o OLim c f
    underLim {c = c} o f all = ≤o-trans (≤o-cocone (λ _ → o) {!!} (≤o-refl o)) (≤o-limiting (λ _ → o) (λ k → ≤o-cocone f k (all k)))

    extLim : ∀   {c : ℂ} →  (f1 f2 : El c → Tree) → (∀ k → f1 k ≤o f2 k) → OLim c f1 ≤o OLim c f2
    extLim {c = c} f1 f2 all = ≤o-limiting f1 (λ k → ≤o-cocone f2 k (all k))


    existsLim : ∀  {c1 : ℂ} {c2 : ℂ} →  (f1 : El c1  → Tree) (f2 : El  c2  → Tree) → (∀ k1 → Σ[ k2 ∈ El  c2 ] f1 k1 ≤o f2 k2) → OLim  c1 f1 ≤o OLim  c2 f2
    existsLim {æ1} {æ2} f1 f2 allex = ≤o-limiting  f1 (λ k → ≤o-cocone f2 (proj₁ (allex k)) (proj₂ (allex k)))


    ¬Z<↑o : ∀  o → ¬ ((O↑ o) ≤o OZ)
    ¬Z<↑o o ()


    open import Induction.WellFounded
    access : ∀ {x} → Acc _<o_ x → WfRec _<o_ (Acc _<o_) x
    access (acc r) = r

    -- https://cj-xu.github.io/agda/constructive-ordinals-in-hott/BrouwerTree.Code.Results.html#3168
    -- TODO: proper credit
    smaller-accessible : (x : Tree) → Acc _<o_ x → ∀ y → y ≤o x → Acc _<o_ y
    smaller-accessible x isAcc y x<y = acc (λ y' y'<y → access isAcc y' (<∘≤-in-< y'<y x<y))

    -- https://cj-xu.github.io/agda/constructive-ordinals-in-hott/BrouwerTree.Code.Results.html#3168
    -- TODO: proper credit
    ordWF : WellFounded _<o_
    ordWF OZ = acc λ _ ()
    ordWF (O↑ x) = acc (λ { y (≤o-sucMono y≤x) → smaller-accessible x (ordWF x) y y≤x})
    ordWF (OLim c f) = acc helper
      where
        helper : (y : Tree) → (y <o OLim c f) → Acc _<o_ y
        helper y (≤o-cocone .f k y<fk) = smaller-accessible (f k) (ordWF (f k)) y (<-in-≤o y<fk)



    private
      data MaxView : Tree → Tree → Set ℓ where
        MaxZ-L : ∀ {o} → MaxView OZ o
        MaxZ-R : ∀ {o} → MaxView o OZ
        MaxLim-L : ∀ {o } {c : ℂ} {f : El c → Tree} → MaxView (OLim c f) o
        MaxLim-R : ∀ {o } {c : ℂ} {f : El c → Tree}
          → (∀   {c' : ℂ} {f' : El c' → Tree} → ¬ (o ≡ OLim  c' f'))
          → MaxView o (OLim c f)
        MaxLim-Suc : ∀  {o1 o2 } → MaxView (O↑ o1) (O↑ o2)

      maxView : ∀ o1 o2 → MaxView o1 o2
      maxView OZ o2 = MaxZ-L
      maxView (OLim c f) o2 = MaxLim-L
      maxView (O↑ o1) OZ = MaxZ-R
      maxView (O↑ o1) (OLim c f) = MaxLim-R λ ()
      maxView (O↑ o1) (O↑ o2) = MaxLim-Suc

    abstract
      omax : Tree → Tree → Tree
      omax' : ∀ {o1 o2} → MaxView o1 o2 → Tree

      omax o1 o2 = omax' (maxView o1 o2)

      omax' {.OZ} {o2} MaxZ-L = o2
      omax' {o1} {.OZ} MaxZ-R = o1
      omax' {(OLim c f)} {o2} MaxLim-L = OLim c λ x → omax (f x) o2
      omax' {o1} {(OLim c f)} (MaxLim-R _) = OLim c (λ x → omax o1 (f x))
      omax' {(O↑ o1)} {(O↑ o2)} MaxLim-Suc = O↑ (omax o1 o2)

      omax-≤L : ∀ {o1 o2} → o1 ≤o omax o1 o2
      omax-≤L {o1} {o2} with maxView o1 o2
      ... | MaxZ-L = ≤o-Z
      ... | MaxZ-R = ≤o-refl _
      ... | MaxLim-L {f = f} = extLim f (λ x → omax (f x) o2) (λ k → omax-≤L)
      ... | MaxLim-R {f = f} _ = {!!} -- underLim o1 (λ x → omax o1 (f x)) (λ k → omax-≤L)
      ... | MaxLim-Suc = ≤o-sucMono omax-≤L


      omax-≤R : ∀ {o1 o2} → o2 ≤o omax o1 o2
      omax-≤R {o1} {o2} with maxView o1 o2
      ... | MaxZ-R = ≤o-Z
      ... | MaxZ-L = ≤o-refl _
      ... | MaxLim-R {f = f} _ = extLim f (λ x → omax o1 (f x)) (λ k → omax-≤R {o1 = o1} {f k})
      ... | MaxLim-L {f = f} = underLim o2 (λ x → omax (f x) o2) (λ k → omax-≤R {o1 = f k} {o2 = o2})
      ... | MaxLim-Suc {o1} {o2} = ≤o-sucMono (omax-≤R {o1 = o1} {o2 = o2})




      omax-monoR : ∀ {o1 o2 o2'} → o2 ≤o o2' → omax o1 o2 ≤o omax o1 o2'
      omax-monoR' : ∀ {o1 o2 o2'} → o2 <o o2' → omax o1 o2 <o omax (O↑ o1) o2'

      omax-monoR {o1} {o2} {o2'} lt with maxView o1 o2 in eq1 | maxView o1 o2' in eq2
      ... | MaxZ-L  | v2  = ≤o-trans lt (≤o-reflEq (cong omax' eq2))
      ... | MaxZ-R  | v2  = ≤o-trans omax-≤L (≤o-reflEq (cong omax' eq2))
      ... | MaxLim-L {f = f1} |  MaxLim-L  = extLim _ _ λ k → omax-monoR {o1 = f1 k} lt
      omax-monoR {o1} {(OLim _ f')} {.(OLim _ f)} (≤o-cocone f k lt) | MaxLim-R neq  | MaxLim-R neq'
        = ≤o-limiting (λ x → omax o1 (f' x)) (λ y → ≤o-cocone (λ x → omax o1 (f x)) k (omax-monoR {o1 = o1} {o2 = f' y} (≤o-trans (≤o-cocone _ y (≤o-refl _)) lt)))
      omax-monoR {o1} {.(OLim _ _)} {o2'} (≤o-limiting f x₁) | MaxLim-R x  | v2  =
        ≤o-trans (≤o-limiting (λ x₂ → omax o1 (f x₂)) λ k → omax-monoR {o1 = o1} (x₁ k)) (≤o-reflEq (cong omax' eq2))
      omax-monoR {(O↑ o1)} {.(O↑ _)} {.(O↑ _)} (≤o-sucMono lt) | MaxLim-Suc  | MaxLim-Suc  = ≤o-sucMono (omax-monoR {o1 = o1} lt)
      omax-monoR {(O↑ o1)} {(O↑ o2)} {(OLim _ f)} (≤o-cocone f k lt) | MaxLim-Suc  | MaxLim-R x
        = ≤o-trans (omax-monoR' {o1 = o1} {o2 = o2} {o2' = f k} lt) (≤o-cocone (λ x₁ → omax (O↑ o1) (f x₁)) k (≤o-refl _)) --omax-monoR' {!lt!}

      omax-monoR' {o1} {o2} {o2'}  (≤o-sucMono lt) = ≤o-sucMono ( (omax-monoR {o1 = o1} lt))
      omax-monoR' {o1} {o2} {.(OLim _ f)} (≤o-cocone f k lt)
        = ≤o-cocone _ k (omax-monoR' {o1 = o1} lt)


      omax-monoL : ∀ {o1 o1' o2} → o1 ≤o o1' → omax o1 o2 ≤o omax o1' o2
      omax-monoL' : ∀ {o1 o1' o2} → o1 <o o1' → omax o1 o2 <o omax o1' (O↑ o2)
      omax-monoL {o1} {o1'} {o2} lt with maxView o1 o2 in eq1 | maxView o1' o2 in eq2
      ... | MaxZ-L | v2 = ≤o-trans (omax-≤R {o1 = o1'}) (≤o-reflEq (cong omax' eq2))
      ... | MaxZ-R | v2 = ≤o-trans lt (≤o-trans (omax-≤L {o1 = o1'}) (≤o-reflEq (cong omax' eq2)))
      omax-monoL {.(OLim _ _)} {.(OLim _ f)} {o2} (≤o-cocone f k lt) | MaxLim-L  | MaxLim-L
        = ≤o-cocone (λ x → omax (f x) o2) k (omax-monoL lt)
      omax-monoL {.(OLim _ _)} {o1'} {o2} (≤o-limiting f lt) | MaxLim-L |  v2
        = ≤o-limiting (λ x₁ → omax (f x₁) o2) λ k → ≤o-trans (omax-monoL (lt k)) (≤o-reflEq (cong omax' eq2))
      omax-monoL {.OZ} {.OZ} {.(OLim _ _)} ≤o-Z | MaxLim-R neq  | MaxZ-L  = ≤o-refl _
      omax-monoL  {.(OLim _ f)} {.OZ} {.(OLim _ _)} (≤o-limiting f x) | MaxLim-R neq | MaxZ-L
        with () ← neq refl
      omax-monoL {o1} {.(OLim _ _)} {.(OLim _ _)} (≤o-cocone _ k lt) | MaxLim-R {f = f} neq | MaxLim-L {f = f'}
        = ≤o-limiting (λ x → omax o1 (f x)) (λ y → ≤o-cocone (λ x → omax (f' x) (OLim _ _)) k
          (≤o-trans (omax-monoL lt) (omax-monoR {o1 = f' k} (≤o-cocone f y (≤o-refl _)))))
      ... | MaxLim-R neq | MaxLim-R {f = f} neq' = extLim (λ x → omax o1 (f x)) (λ x → omax o1' (f x)) (λ k → omax-monoL lt)
      omax-monoL {.(O↑ _)} {.(O↑ _)} {.(O↑ _)} (≤o-sucMono lt) | MaxLim-Suc  | MaxLim-Suc
        = ≤o-sucMono (omax-monoL lt)
      omax-monoL {.(O↑ _)} {.(OLim _ f)} {.(O↑ _)} (≤o-cocone f k lt) | MaxLim-Suc  | MaxLim-L
        = ≤o-cocone (λ x → omax (f x) (O↑ _)) k (omax-monoL' lt)

      omax-monoL' {o1} {o1'} {o2} lt with maxView o1 o2 in eq1 | maxView o1' o2 in eq2
      omax-monoL' {o1} {.(O↑ _)} {o2} (≤o-sucMono lt) | v1 | v2 = ≤o-sucMono (≤o-trans (≤o-reflEq (cong omax' (sym eq1))) (omax-monoL lt))
      omax-monoL' {o1} {.(OLim _ f)} {o2} (≤o-cocone f k lt) | v1 | v2
        = ≤o-cocone _ k (≤o-trans (≤o-sucMono (≤o-reflEq (cong omax' (sym eq1)))) (omax-monoL' lt))


      omax-mono : ∀ {o1 o2 o1' o2'} → o1 ≤o o1' → o2 ≤o o2' → omax o1 o2 ≤o omax o1' o2'
      omax-mono {o1' = o1'} lt1 lt2 = ≤o-trans (omax-monoL lt1) (omax-monoR {o1 = o1'} lt2)

      omax-strictMono : ∀ {o1 o2 o1' o2'} → o1 <o o1' → o2 <o o2' → omax o1 o2 <o omax o1' o2'
      omax-strictMono lt1 lt2 = omax-mono lt1 lt2


      omax-sucMono : ∀ {o1 o2 o1' o2'} → omax o1 o2 ≤o omax o1' o2' → omax o1 o2 <o omax (O↑ o1') (O↑ o2')
      omax-sucMono lt = ≤o-sucMono lt


      -- omax-Z : ∀ o → omax o OZ ≡ o
      -- omax-Z OZ = refl
      -- omax-Z (O↑ o) = refl
      -- omax-Z (OLim c f) = cong (OLim c) {!!} -- cong (OLim c) (funExt (λ x → omax-Z (f x)))

      omax-Z : ∀ o → omax o OZ ≤o o
      omax-Z OZ = ≤o-Z
      omax-Z (O↑ o) = ≤o-refl (omax (O↑ o) OZ)
      omax-Z (OLim c f) = extLim (λ x → omax (f x) OZ) f (λ k → omax-Z (f k))

      omax-↑ : ∀ {o1 o2} → omax (O↑ o1) (O↑ o2) ≡ O↑ (omax o1 o2)
      omax-↑ = refl

      omax-≤Z : ∀ o → omax o OZ ≤o o
      omax-≤Z OZ = ≤o-refl _
      omax-≤Z (O↑ o) = ≤o-refl _
      omax-≤Z (OLim c f) = extLim _ _ (λ k → omax-≤Z (f k))

      -- omax-oneL : ∀ {o} → omax O1 (O↑ o) ≤o O↑ o
      -- omax-oneL  = ≤o-refl _

      -- omax-oneR : ∀ {o} → omax (O↑ o) O1 ≤o O↑ o
      -- omax-oneR {OZ} = ≤o-sucMono (≤o-refl _)
      -- omax-oneR {O↑ o} = ≤o-sucMono (≤o-refl _)
      -- omax-oneR {OLim c f} = ≤o-sucMono (substPath (λ x → x ≤o OLim c f) (sym (omax-Z (OLim c f))) (≤o-refl (OLim c f))) -- rewrite ctop (omax-Z (OLim c f))= ≤o-refl _


      omax-limR : ∀   {c : ℂ} (f : El  c  → Tree) o → omax o (OLim c f) ≤o OLim c (λ k → omax o (f k))
      omax-limR f OZ = ≤o-refl _
      omax-limR f (O↑ o) = extLim _ _ λ k → ≤o-refl _
      omax-limR f (OLim c f₁) = ≤o-limiting _ λ k → ≤o-trans (omax-limR f (f₁ k)) (extLim _ _ (λ k2 → omax-monoL {o1 = f₁ k} {o1' = OLim c f₁} {o2 = f k2}  (≤o-cocone _ k (≤o-refl _))))


      omax-commut : ∀ o1 o2 → omax o1 o2 ≤o omax o2 o1
      omax-commut o1 o2 with maxView o1 o2
      ... | MaxZ-L = omax-≤L
      ... | MaxZ-R = ≤o-refl _
      ... | MaxLim-R {f = f} x = extLim _ _ (λ k → omax-commut o1 (f k))
      ... | MaxLim-Suc {o1 = o1} {o2 = o2} = ≤o-sucMono (omax-commut o1 o2)
      ... | MaxLim-L {c = c} {f = f} with maxView o2 o1
      ... | MaxZ-L = extLim _ _ λ k → omax-Z (f k)
      ... | MaxLim-R x = extLim _ _ (λ k → omax-commut (f k) o2)
      ... | MaxLim-L {c = c2} {f = f2} =
        ≤o-trans (extLim _ _ λ k → omax-limR f2 (f k))
        (≤o-trans (≤o-limiting _ (λ k → ≤o-limiting _ λ k2 → ≤o-cocone _ k2 (≤o-cocone _ k (≤o-refl _))))
        (≤o-trans (≤o-refl (OLim c2 λ k2 → OLim c λ k → omax (f k) (f2 k2)))
        (extLim _ _ (λ k2 → ≤o-limiting _ λ k1 → ≤o-trans (omax-commut (f k1) (f2 k2)) (omax-monoR {o1 = f2 k2} {o2 = f k1} {o2' = OLim c f} (≤o-cocone _ k1 (≤o-refl _)))))))


      omax-assocL : ∀ o1 o2 o3 → omax o1 (omax o2 o3) ≤o omax (omax o1 o2) o3
      omax-assocL o1 o2 o3 with maxView o2 o3 in eq23
      ... | MaxZ-L = omax-monoL {o1 = o1} {o1' = omax o1 OZ} {o2 = o3} omax-≤L
      ... | MaxZ-R = omax-≤L
      ... | m with maxView o1 o2
      ... | MaxZ-L rewrite sym eq23 = ≤o-refl _
      ... | MaxZ-R rewrite sym eq23 = ≤o-refl _
      ... | MaxLim-R {f = f} x rewrite sym eq23 = ≤o-trans (omax-limR (λ x → omax (f x) o3) o1) (extLim _ _ λ k → omax-assocL o1 (f k) o3) -- f,omax-limR f o1
      omax-assocL .(O↑ _) .(O↑ _) .OZ | MaxZ-R  | MaxLim-Suc = ≤o-refl _
      omax-assocL o1 o2 .(OLim _ _) | MaxLim-R {f = f} x   | MaxLim-Suc = extLim _ _ λ k → omax-assocL o1 o2 (f k)
      omax-assocL (O↑ o1) (O↑ o2) (O↑ o3) | MaxLim-Suc  | MaxLim-Suc = ≤o-sucMono (omax-assocL o1 o2 o3)
      ... | MaxLim-L {f = f} rewrite sym eq23 = extLim _ _ λ k → omax-assocL (f k) o2 o3



      omax-assocR : ∀ o1 o2 o3 →  omax (omax o1 o2) o3 ≤o omax o1 (omax o2 o3)
      omax-assocR o1 o2 o3 = ≤o-trans (omax-commut (omax o1 o2) o3) (≤o-trans (omax-monoR {o1 = o3} (omax-commut o1 o2))
        (≤o-trans (omax-assocL o3 o2 o1) (≤o-trans (omax-commut (omax o3 o2) o1) (omax-monoR {o1 = o1} (omax-commut o3 o2)))))


      omax-swap4 : ∀ {o1 o1' o2 o2'} → omax (omax o1 o1') (omax o2 o2') ≤o omax (omax o1 o2) (omax o1' o2')
      omax-swap4 {o1}{o1'}{o2 }{o2'} =
        omax-assocL (omax o1 o1') o2 o2'
        ≤⨟o omax-monoL {o1 = omax (omax o1 o1') o2} {o2 = o2'}
          (omax-assocR o1 o1' o2 ≤⨟o omax-monoR {o1 = o1} (omax-commut o1' o2) ≤⨟o omax-assocL o1 o2 o1')
        ≤⨟o omax-assocR (omax o1 o2) o1' o2'

      omax-swap6 : ∀ {o1 o2 o3 o1' o2' o3'} → omax (omax o1 o1') (omax (omax o2 o2') (omax o3 o3')) ≤o omax (omax o1 (omax o2 o3)) (omax o1' (omax o2' o3'))
      omax-swap6 {o1} {o2} {o3} {o1'} {o2'} {o3'} =
        omax-monoR {o1 = omax o1 o1'} (omax-swap4 {o1 = o2} {o1' = o2'} {o2 = o3} {o2' = o3'})
        ≤⨟o omax-swap4 {o1 = o1} {o1' = o1'}

      omax-lim2L :
        ∀
        {c1 : ℂ}
        (f1 : El  c1 → Tree)
        {c2 : ℂ}
        (f2 : El  c2 → Tree)
        → OLim  c1 (λ k1 → OLim  c2 (λ k2 → omax (f1 k1) (f2 k2))) ≤o omax (OLim  c1 f1) (OLim  c2 f2)
      omax-lim2L f1 f2 = ≤o-limiting  _ (λ k1 → ≤o-limiting  _ λ k2 → omax-mono (≤o-cocone  f1 k1 (≤o-refl _)) (≤o-cocone  f2 k2 (≤o-refl _)))

      omax-lim2R :
        ∀
        {c1 : ℂ}
        (f1 : El  c1 → Tree)
        {c2 : ℂ}
        (f2 : El  c2 → Tree)
        →  omax (OLim  c1 f1) (OLim  c2 f2) ≤o OLim  c1 (λ k1 → OLim  c2 (λ k2 → omax (f1 k1) (f2 k2)))
      omax-lim2R f1 f2 = extLim  _ _ (λ k1 → omax-limR  _ (f1 k1))

    --Attempt to have an idempotent version of max

      nmax : Tree → ℕ → Tree
      nmax o ℕ.zero = OZ
      nmax o (ℕ.suc n) = omax (nmax o n) o

      nmax-mono : ∀ {o1 o2 } n → o1 ≤o o2 → nmax o1 n ≤o nmax o2 n
      nmax-mono ℕ.zero lt = ≤o-Z
      nmax-mono {o1 = o1} {o2} (ℕ.suc n) lt = omax-mono {o1 = nmax o1 n} {o2 = o1} {o1' = nmax o2 n} {o2' = o2} (nmax-mono n lt) lt

    --
      omax∞ : Tree → Tree
      omax∞ o = OℕLim (λ n → nmax o n)


      omax-∞lt1 : ∀ o → omax (omax∞ o) o ≤o omax∞ o
      omax-∞lt1 o = ≤o-limiting  _ λ k → helper (Iso.fun CℕIso k)
        where
          helper : ∀ n → omax (nmax o n) o ≤o omax∞ o
          helper n = ≤o-cocone  _ (Iso.inv CℕIso (ℕ.suc n)) (subst (λ sn → nmax o (ℕ.suc n) ≤o nmax o sn) (sym (Iso.rightInv CℕIso (suc n))) (≤o-refl _))
        -- helper (ℕ.suc n) = ≤o-cocone  _ (CℕfromNat (ℕ.suc (ℕ.suc n))) (subst (λ sn → omax (omax (nmax o n) o) o ≤o nmax o sn) (sym (Cℕembed (ℕ.suc n)))
        --   {!!})
        --

      -- nmax-idem-absorb : ∀ o n → omax o o ≤o o → nmax o n ≤o o
      -- nmax-idem-absorb o ℕ.zero lt = ≤o-Z
      -- nmax-idem-absorb o (ℕ.suc n) lt = omax-monoL (nmax-idem-absorb o n lt) ≤⨟o lt
      -- omax∞-idem-absorb : ∀ {o} → omax o o ≤o o → omax∞ o ≤o o
      -- omax∞-idem-absorb lt = ≤o-limiting  (λ x → nmax _ (CℕtoNat x)) (λ k → nmax-idem-absorb _ (CℕtoNat k) lt)

      omax-∞ltn : ∀ n o → omax (omax∞ o) (nmax o n) ≤o omax∞ o
      omax-∞ltn ℕ.zero o = omax-≤Z (omax∞ o)
      omax-∞ltn (ℕ.suc n) o =
        ≤o-trans (omax-monoR {o1 = omax∞ o} (omax-commut (nmax o n) o))
        (≤o-trans (omax-assocL (omax∞ o) o (nmax o n))
        (≤o-trans (omax-monoL {o1 = omax (omax∞ o) o} {o2 = nmax o n} (omax-∞lt1 o)) (omax-∞ltn n o)))

      omax∞-idem : ∀ o → omax (omax∞ o) (omax∞ o) ≤o omax∞ o
      omax∞-idem o = ≤o-limiting  _ λ k → ≤o-trans (omax-commut (nmax o (Iso.fun CℕIso k)) (omax∞ o)) (omax-∞ltn (Iso.fun CℕIso k) o)


      omax∞-self : ∀ o → o ≤o omax∞ o
      omax∞-self o = ≤o-cocone  _ (Iso.inv CℕIso 1) (subst (λ x → o ≤o nmax o x) (sym (Iso.rightInv CℕIso 1)) (≤o-refl _))

      omax∞-idem∞ : ∀ o → omax o o ≤o omax∞ o
      omax∞-idem∞ o = ≤o-trans (omax-mono (omax∞-self o) (omax∞-self o)) (omax∞-idem o)

      omax∞-mono : ∀ {o1 o2} → o1 ≤o o2 → (omax∞ o1) ≤o (omax∞ o2)
      omax∞-mono lt = extLim  _ _ λ k → nmax-mono (Iso.fun CℕIso k) lt



      nmax-≤ : ∀ {o} n → omax o o ≤o o → nmax o n ≤o o
      nmax-≤ ℕ.zero lt = ≤o-Z
      nmax-≤ {o = o} (ℕ.suc n) lt = ≤o-trans (omax-monoL {o1 = nmax o n} {o2 = o} (nmax-≤ n lt)) lt

      omax∞-≤ : ∀ {o} → omax o o ≤o o → omax∞ o ≤o o
      omax∞-≤ lt = ≤o-limiting  _ λ k → nmax-≤ (Iso.fun CℕIso k) lt

      -- Convenient helper for turing < with omax∞ into < without
      omax<-∞ : ∀ {o1 o2 o} → omax (omax∞ (o1)) (omax∞ o2) <o o → omax o1 o2 <o o
      omax<-∞ lt = ≤∘<-in-< (omax-mono (omax∞-self _) (omax∞-self _)) lt

      omax-<Ls : ∀ {o1 o2 o1' o2'} → omax o1 o2 <o omax (O↑ (omax o1 o1')) (O↑ (omax o2 o2'))
      omax-<Ls {o1} {o2} {o1'} {o2'} = omax-sucMono {o1 = o1} {o2 = o2} {o1' = omax o1 o1'} {o2' = omax o2 o2'}
        (omax-mono {o1 = o1} {o2 = o2} (omax-≤L) (omax-≤L))

      omax∞-<Ls : ∀ {o1 o2 o1' o2'} → omax o1 o2 <o omax (O↑ (omax (omax∞ o1) o1')) (O↑ (omax (omax∞ o2) o2'))
      omax∞-<Ls {o1} {o2} {o1'} {o2'} =  <∘≤-in-< (omax-<Ls {o1} {o2} {o1'} {o2'})
        (omax-mono {o1 = O↑ (omax o1 o1')} {o2 = O↑ (omax o2 o2')}
          (≤o-sucMono (omax-monoL (omax∞-self o1)))
          (≤o-sucMono (omax-monoL (omax∞-self o2))))


      omax∞-lub : ∀ {o1 o2 o} → o1 ≤o omax∞ o → o2 ≤o omax∞  o → omax o1 o2 ≤o (omax∞ o)
      omax∞-lub {o1 = o1} {o2 = o2} lt1 lt2 = omax-mono {o1 = o1} {o2 = o2} lt1 lt2 ≤⨟o omax∞-idem _

      omax∞-absorbL : ∀ {o1 o2 o} → o2 ≤o o1 → o1 ≤o omax∞ o → omax o1 o2 ≤o omax∞ o
      omax∞-absorbL lt12 lt1 = omax∞-lub lt1 (lt12 ≤⨟o lt1)

      omax∞-distL : ∀ {o1 o2} → omax (omax∞ o1) (omax∞ o2) ≤o omax∞ (omax o1 o2)
      omax∞-distL {o1} {o2} =
        omax∞-lub {o1 = omax∞ o1} {o2 = omax∞ o2} (omax∞-mono omax-≤L) (omax∞-mono (omax-≤R {o1 = o1}))


      omax∞-distR : ∀ {o1 o2} → omax∞ (omax o1 o2) ≤o omax (omax∞ o1) (omax∞ o2)
      omax∞-distR {o1} {o2} = ≤o-limiting  _ λ k → helper {n = Iso.fun CℕIso k}
        where
        helper : ∀ {o1 o2 n} → nmax (omax o1 o2) n ≤o omax (omax∞ o1) (omax∞ o2)
        helper {o1} {o2} {ℕ.zero} = ≤o-Z
        helper {o1} {o2} {ℕ.suc n} =
          omax-monoL {o1 = nmax (omax o1 o2) n} (helper {o1 = o1} {o2} {n})
          ≤⨟o omax-swap4 {omax∞ o1} {omax∞ o2} {o1} {o2}
          ≤⨟o omax-mono {o1 = omax (omax∞ o1) o1} {o2 = omax (omax∞ o2) o2} {o1' = omax∞ o1} {o2' = omax∞ o2}
            (omax∞-lub {o1 = omax∞ o1} (≤o-refl _) (omax∞-self _))
            (omax∞-lub {o1 = omax∞ o2} (≤o-refl _) (omax∞-self _))


      omax∞-cocone : ∀  {c : ℂ} (f : El c → Tree) k →
        f k ≤o omax∞ (OLim  c f)
      omax∞-cocone f k =  omax∞-self _ ≤⨟o omax∞-mono (≤o-cocone  _ k (≤o-refl _))

      -- omax* : ∀ {n} → Vec Tree n → Tree
      -- omax* [] = OZ
      -- omax* (x ∷ os) = omax x (omax* os)

      -- omax*-≤L : ∀ {n o} {os : Vec Tree n} → o ≤o omax* (o ∷ os)
      -- omax*-≤L = omax-≤L

      -- omax*-≤R : ∀ {n o} {os : Vec Tree n} → omax* os ≤o omax* (o ∷ os)
      -- omax*-≤R {o = o} = omax-≤R {o1 = o}

      -- omax*-≤-n : ∀ {n} {os : Vec Tree n} (f : Fin n) → lookup f os ≤o omax* os
      -- omax*-≤-n {os = o ∷ os} Fin.zero = omax*-≤L {o = o} {os = os}
      -- omax*-≤-n {os = o ∷ os} (Fin.suc f) = omax*-≤-n f ≤⨟o (omax*-≤R {o = o} {os = os})

      -- omax*-swap : ∀ {n} {os1 os2 : Vec Tree n} → omax* (zipWith omax os1 os2) ≤o omax (omax* os1) (omax* os2)
      -- omax*-swap {n = ℕ.zero} {[]} {[]} = ≤o-Z
      -- omax*-swap {n = ℕ.suc n} {o1 ∷ os1} {o2 ∷ os2} = omax-monoR {o1 = omax o1 o2} (omax*-swap {n = n}) ≤⨟o omax-swap4 {o1 = o1} {o1' = o2} {o2 = omax* os1} {o2' = omax* os2}

      -- omax*-mono : ∀ {n} {os1 os2 : Vec Tree n} → foldr (λ (o1 , o2) rest → (o1 ≤o o2) × rest) Unit (zipWith _,_ os1 os2) → omax* os1 ≤o omax* os2
      -- omax*-mono {ℕ.zero} {[]} {[]} lt = ≤o-Z
      -- omax*-mono {ℕ.suc n} {o1 ∷ os1} {o2 ∷ os2} (lt , rest) = omax-mono {o1 = o1} {o1' = o2} lt (omax*-mono {os1 = os1} {os2 = os2} rest)

    -- orec : ∀  (P : Tree → Set ℓ)
    --   → ((x : Tree) → (rec : (y : Tree) → (_ : ∥ y <o x ∥₁) → P y ) → P x)
    --   → ∀ {o} → P o
    -- orec P f = induction (λ x rec → f x rec) _
    --   where open WFI (ordWFProp)


    -- oPairRec : ∀  (P : Tree → Tree → Set ℓ)
    --   → ((x1 x2 : Tree) → (rec : (y1 y2 : Tree) → (_ : (y1 , y2) <oPair (x1 , x2)) → P y1 y2 ) → P x1 x2)
    --   → ∀ {o1 o2} → P o1 o2
    -- oPairRec P f = induction (λ (x1 , x2) rec → f x1 x2 λ y1 y2 → rec (y1 , y2)) _
    --   where open WFI (oPairWF)

\end{code}
