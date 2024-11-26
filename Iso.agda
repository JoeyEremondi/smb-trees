
-- Taken from the agda-cubical library
-- https://agda.github.io/cubical/Cubical.Foundations.Isomorphism.html
module Iso where
open import Relation.Binary.PropositionalEquality as Eq hiding (refl)
open import Level

-- Section and retract
module _ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} where
  section : (f : A → B) → (g : B → A) → Set ℓ'
  section f g = ∀ b → f (g b) ≡ b

  -- NB: `g` is the retraction!
  retract : (f : A → B) → (g : B → A) → Set ℓ
  retract f g = ∀ a → g (f a) ≡ a

record Iso {ℓ ℓ'} (A : Set ℓ) (B : Set ℓ') : Set (ℓ ⊔ ℓ') where
  no-eta-equality
  constructor iso
  field
    fun : A → B
    inv : B → A
    rightInv : section fun inv
    leftInv  : retract fun inv


open import Data.Nat
open import Data.Maybe

refl : ∀ {ℓ} {A : Set ℓ} → Iso A A
refl .Iso.fun = λ x → x
refl .Iso.inv = λ x → x
refl .Iso.rightInv = λ _ → Eq.refl
refl .Iso.leftInv = λ _ → Eq.refl

maybeNatIso : ∀ {ℓ} {A : Set ℓ} → Iso A ℕ → Iso (Maybe A) ℕ
Iso.fun (maybeNatIso theIso) nothing = 0
Iso.fun (maybeNatIso theIso) (just x) = ℕ.suc ( Iso.fun theIso x )
Iso.inv (maybeNatIso theIso) ℕ.zero = nothing
Iso.inv (maybeNatIso theIso) (ℕ.suc n) = just (Iso.inv theIso n)
Iso.rightInv (maybeNatIso theIso) ℕ.zero = Eq.refl
Iso.rightInv (maybeNatIso theIso) (ℕ.suc n) = cong ℕ.suc (Iso.rightInv theIso n)
Iso.leftInv (maybeNatIso theIso) (just x) = cong just (Iso.leftInv theIso x)
Iso.leftInv (maybeNatIso theIso) nothing = Eq.refl


if0 : ∀ {ℓ} {A : Set ℓ} →  ℕ →  A → A → A
if0 zero z s = z
if0 (suc n) z s = s

