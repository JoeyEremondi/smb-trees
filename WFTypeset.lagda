
\begin{code}[hide]
module WFTypeset where

-- open import Data.Product.Base using (Σ; _,_; proj₁)
open import Function.Base using (_on_)
open import Induction
open import Level using (Level; _⊔_)
open import Relation.Binary.Core using (Rel)
open import Relation.Binary.Definitions
  using (Symmetric; _Respectsʳ_; _Respects_)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl)
open import Relation.Unary

private
  variable
    a b ℓ ℓ₁ ℓ₂ r : Level
    A : Set a
    B : Set b

WfRec : Rel A r → ∀ {ℓ} → RecStruct A ℓ _
WfRec _<_ P x = ∀ y → y < x → P y

\end{code}

\begin{code}
data Acc {A : Set a}
     (_<_ : A → A → Set ℓ)
     (x : A)
     : Set (a ⊔ ℓ) where
  acc : (rs : ∀ y → y < x → Acc _<_ y) → Acc _<_ x

WellFounded : (A → A → Set ℓ) → Set _
WellFounded _<_ = ∀ x → Acc _<_ x
\end{code}

\begin{code}[hide]
------------------------------------------------------------------------
-- Basic properties

acc-inverse : ∀ {_<_ : Rel A ℓ} {x : A} (q : Acc _<_ x) →
              (y : A) → y < x → Acc _<_ y
acc-inverse (acc rs) y y<x = rs y y<x

Acc-resp-≈ : {_≈_ : Rel A ℓ₁} {_<_ : Rel A ℓ₂} → Symmetric _≈_ →
             _<_ Respectsʳ _≈_ → (Acc _<_) Respects _≈_
Acc-resp-≈ sym respʳ x≈y (acc rec) =
  acc (λ z z<y → rec z (respʳ (sym x≈y) z<y))

module Some {_<_ : Rel A r} {ℓ} where

  wfRecBuilder : SubsetRecursorBuilder (Acc _<_) (WfRec _<_ {ℓ = ℓ})
  wfRecBuilder P f x (acc rs) = λ y y<x →
    f y (wfRecBuilder P f y (rs y y<x))

  wfRec : SubsetRecursor (Acc _<_) (WfRec _<_)
  wfRec = subsetBuild wfRecBuilder

  unfold-wfRec : (P : Pred A ℓ) (f : WfRec _<_ P ⊆′ P) {x : A} (q : Acc _<_ x) →
                 wfRec P f x q ≡ f x (λ y y<x → wfRec P f y (acc-inverse q y y<x))
  unfold-wfRec P f (acc rs) = refl

module All {_<_ : Rel A r} (wf : WellFounded _<_) ℓ where

  wfRecBuilder : RecursorBuilder (WfRec _<_ {ℓ = ℓ})
  wfRecBuilder P f x = Some.wfRecBuilder P f x (wf x)
\end{code}


That is, an element of a type is accessible for a relation if all strictly
smaller elements of it are also accessible. A relation is well-founded
if all values are accessible with respect to that relation.
This can then be used to define induction with arbitrary recursive
calls on smaller values:

\begin{code}
  wfRec : (P : A → Set ℓ)
    → (∀ x → (∀ y → y < x → P y) → P x)
    → ∀ x → P x
\end{code}
The $\AgdaFunction{wfRec}$ function is defined using structural recursion on an argument
of type $\AgdaDatatype{Acc}$, so the type checker accepts it.
\begin{code}[hide]
  wfRec = build wfRecBuilder

module FixPoint
  {_<_ : Rel A r} (wf : WellFounded _<_)
  (P : Pred A ℓ) (f : WfRec _<_ P ⊆′ P)
  (f-ext : (x : A) {IH IH′ : WfRec _<_ P x} → (∀ {y} y<x → IH y y<x ≡ IH′ y y<x) → f x IH ≡ f x IH′)
  where

  some-wfRec-irrelevant : ∀ x → (q q′ : Acc _<_ x) → Some.wfRec P f x q ≡ Some.wfRec P f x q′
  some-wfRec-irrelevant = All.wfRec wf _
                                   (λ x → (q q′ : Acc _<_ x) → Some.wfRec P f x q ≡ Some.wfRec P f x q′)
                                   (λ { x IH (acc rs) (acc rs′) → f-ext x (λ y<x → IH _ y<x (rs _ y<x) (rs′ _ y<x)) })

  open All wf ℓ
  wfRecBuilder-wfRec : ∀ {x y} y<x → wfRecBuilder P f x y y<x ≡ wfRec P f y
  wfRecBuilder-wfRec {x} {y} y<x with wf x
  ... | acc rs = some-wfRec-irrelevant y (rs y y<x) (wf y)


\end{code}
Well-founded induction computes a fixed point of the function,
meaning that the particular proof that the strict order holds
is irrelevant:
\begin{code}
  unfold-wfRec : ∀ {x}
    → wfRec P f x ≡ f x (λ y _ → wfRec P f y)
\end{code}

\begin{code}[hide]

  unfold-wfRec {x} = f-ext x wfRecBuilder-wfRec
\end{code}
