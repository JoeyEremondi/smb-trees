module SmallSMB where

open import Data.Unit
open import Data.Nat as Nat hiding (_<_ ; _≤_)
import Iso

open import SMBTree ⊤ (λ _ → ℕ) tt Iso.refl

ℕω : Set
ℕω = SMBTree



fromℕ : ℕ -> ℕω
fromℕ zero = Z
fromℕ (suc n) = ↑ (fromℕ n)

ω : ℕω
ω = Lim _ (λ n → fromℕ n)

<ω : ∀ {n} → (fromℕ n) < ω
<ω {n = n} = ≤-limUpperBound (suc n)
